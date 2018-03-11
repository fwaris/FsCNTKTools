#load "SetEnv.fsx"

open CNTK
open System
open System.Windows.Forms
open FSCNTK.Tools.Graph
open System.Collections.Generic
open FSCNTK.Tools.Graph.grph
open System.Windows.Controls
open System.Windows.Markup.Localizer

type C = CNTK.CNTKLib

let test_model = __SOURCE_DIRECTORY__ + "/test_model.bin"
//let t2 = @"D:\repodata\fscntk\m_fs_untrained.bin"
let t2 = @"D:\repodata\fscntk\PGeneratorDCGAN.bin"

let device = DeviceDescriptor.GPUDevice(0)

let model = Function.Load(test_model,device)
let model_t2 = Function.Load(t2,device)

let inline mCollect m k v = 
  let vs = match m |> Map.tryFind k with Some ls -> v::ls | None -> [v]
  Map.add k vs m

let inline mRemove m k v = 
  let vs = match m |> Map.tryFind k with Some ls -> ls |> List.filter (fun v'-> v'<>v) | None -> []
  Map.add k vs m

//determine 'signature' of a variable for matching purposes
let varSignature (v:Variable) =
  let dims = v.Shape.Dimensions |> Seq.toList
  let axes = seq { for a in v.DynamicAxes do 
                      if a.IsDynamic then yield 'd'
                      if a.IsOrdered then yield 'o'
                      if a.IsStatic then yield 't'
                      if a.IsBatchAxis() then yield 'b'
                      if a.IsSequenceAxis() then yield 's'
                  }
                  |> set
  dims,axes

//try to match a variable 
//to the closest one of the candidate variables
let matchVars protoVar cndtVars =
  if List.length cndtVars = 0 then None
  elif List.length cndtVars = 1 then Some cndtVars.Head
  else
    let srcDims,srcAxes = varSignature protoVar                                     //variable signature
    let inpSigs = cndtVars |> List.map (fun v-> varSignature v, v)                  //candidate variable signatures
    let sameDims =  inpSigs |> List.filter (fun ((dims,axs),v) -> dims = srcDims)   //candidate with same dimensions as variable
    if sameDims.Length = 1 then
      let (_,v) = sameDims.Head
      Some v                                                                       //only 1 match so that should be it
    else
      let (_,v) = inpSigs |> List.maxBy (fun ((dims,axs),v)  -> (Set.intersect srcAxes axs) |> Set.count)
      Some v                                                                       //pick the one with the closes axes signature

let remapTo 
  (phMap:IDictionary<Variable,Function>) 
  (linkMap:IDictionary<Variable,Variable>)
  (edge:Edge)
  = 
  match linkMap.TryGetValue(edge.Var) with
  | true,ph -> 
    let targetFunction = phMap.[ph]
    {edge with To=targetFunction.Uid}
  | false,_ -> edge

let remapFrom 
  (phMap:IDictionary<Variable,Function>) 
  (linkMap:IDictionary<Variable,Variable>)
  (edge:Edge)
  = 
  match linkMap.TryGetValue(edge.Var) with
  | true,ph -> 
    let srcFunction = phMap.[ph]
    {edge with From=srcFunction.Uid}
  | false,_ -> edge

let allVertices ((vx,es),subgraphs) = vx @ (List.collect (fun v -> v.Vertices) subgraphs) 
let allEdges ((vx,es),subgraphs) = es @ (List.collect (fun v -> v.Edges) subgraphs)      //all edges
let subgraphEdges = List.collect (fun sg -> sg.Edges |> List.map (fun e->sg.Container,e))
let subgraphVertices = List.collect(fun sg -> sg.Vertices |> List.map (fun v->sg.Container,v))

//placeholders for each block function
let blockPlaceHolders subgraphs =
  let vertices = subgraphs |>  subgraphVertices |> List.map snd
  let phBlockMap = 
    subgraphs
    |> subgraphEdges
    |> List.choose (fun (c,e) -> if e.Var.IsPlaceholder then Some (e.Var,c) else None)
    |> dict
  vertices 
  |> List.map (function 
    | Vf f ->
      f.Inputs 
      |> Seq.toList 
      |> List.choose (fun v -> match phBlockMap.TryGetValue v with | true,id-> Some(id,v,f) | _ -> None)
    | _ -> [])
    |> List.filter (List.isEmpty >> not)
    |> List.collect (fun x->x)

let relinkBlockInputs (((vx,es),subgraphs) as graphs) =

  let edges = allEdges graphs
  let blkPhs = blockPlaceHolders subgraphs  //block placeholders

  let blkInps =  //inputs coming into each block function, excluding parameters
    let blockIdSet = blkPhs |> List.map (fun (c,_,_)->c) |> set
    edges |> List.filter (fun e -> blockIdSet.Contains e.To && not e.Var.IsParameter )
  
  let (links,_) =                                     //placeholders matched to block inputs
    let inpMap = blkInps |> List.groupBy (fun e->e.To) |> Map.ofList
    (([],inpMap),blkPhs) 
    ||> List.fold (fun (acc,inpMap) (blockId,ph,_) ->
      inpMap 
      |> Map.tryFind blockId
      |> Option.map (List.map (fun e->e.Var))
      |> Option.bind (matchVars ph)
      |> Option.map (fun edgeVar ->   //match found!
        (edgeVar,ph)::acc,
        let es' = inpMap.[blockId] |> List.filter (fun e->e.Var<>edgeVar)  //remove matched so its not matched again
        inpMap |> Map.add blockId es')
      |> Option.defaultValue (acc,inpMap))

  //retarget block input edges to owners of placeholders
  //the 'to' end should be the function which 'owns' the placeholder
  //remove placeholders that were matched
  let linkMap = dict links 
  let phMap = blkPhs |> List.map (fun (c,v,f) -> v,f) |> dict   
  let remappedInputs = blkInps |> List.map (remapTo phMap linkMap)
  let toRemove = remappedInputs |>  List.map (fun e -> e.From,e.To) |> set
  let es = es |> List.filter (fun e->toRemove.Contains(e.From,e.To) |> not) 
  let es = es @ remappedInputs
  let subgraphs = subgraphs |> List.map (fun sg -> 
    {sg with
      Vertices = sg.Vertices |> List.filter (function Vv v->phMap.ContainsKey v |> not | _ -> true)
      Edges=sg.Edges |> List.filter (fun e->phMap.ContainsKey e.Var |> not)})
  ((vx,es),subgraphs)


let relinkBlockOutputs (((vxs,es),subgraphs) as graphs) = 
  let blkOutpts = 
    vxs 
    |> List.collect (function 
      | Vf f when f.IsBlock -> 
        let root = f.BlockRoot()
        root.Outputs 
          |> Seq.map (fun outV -> f.Uid,outV,root) 
          |> Seq.toList
      | _ -> []) 
    |> List.groupBy (fun (id,_,_) -> id)
    |> Map.ofList

  let possibleTargets = subgraphs |> List.map (fun g->g.Container) |> set//graphs |> List.map uid |> set

  let blkOutEdges = 
    es 
    |> List.filter (fun e -> possibleTargets.Contains e.To)
    |> List.choose (fun e -> blkOutpts |> Map.tryFind e.From |> Option.map (fun _->e.From,e)) 

  let uniqOutEs = //outputs may go to multiple places so pick unique ones for matching
    blkOutEdges 
    |> List.groupBy fst 
    |> List.map (fun (k,vs) -> 
      k,
      vs 
      |> List.map (fun (_,e) -> e.Var) 
      |> HashSet 
      |> Seq.toList)
    |> List.collect (fun (k,vs)->vs |> List.map (fun v -> k,v))

  let (links,_) =                                     //block outputs mapped to BlockRoot outputs
    let accMap = blkOutpts |> Map.map (fun _ xs -> xs |> List.map (fun (_,v,_) -> v))
    (([],accMap),uniqOutEs) 
    ||> List.fold (fun (acc,accMap) (blockId,edgeVar) ->
      accMap 
      |> Map.tryFind blockId
      |> Option.bind (matchVars edgeVar)
      |> Option.map (fun outVar ->        //matched input
        (edgeVar,outVar)::acc,
        (mRemove accMap blockId outVar))  //remove matched so its not matched again
      |> Option.defaultValue (acc,accMap))
   
  let blkRoots = blkOutpts |> Map.toSeq |> Seq.collect (fun (c,xs) -> xs |> List.map(fun (_,v,f) -> v,f)) |> dict
  let linkMap = dict links
  let remappedOutputs = blkOutEdges |> List.map snd |> List.map (remapFrom blkRoots linkMap)
  let toRemove = blkOutEdges |> List.map snd |> List.map (fun e->e.From,e.To) |> set
  let es = es |> List.filter (fun e->toRemove.Contains(e.From,e.To) |> not)    //block ouput edges removed
  let es = es @ remappedOutputs
  let sgVxsToRemove = blkRoots.Keys |> Seq.map(fun v->v.Uid) |> set
  let subgraphs = subgraphs |> List.map (fun sg -> 
    {sg with
      Vertices = sg.Vertices |> List.filter (uid >> sgVxsToRemove.Contains >> not) 
      Edges=sg.Edges |> List.filter (fun e->sgVxsToRemove.Contains e.To |> not)})
  ((vxs,es),subgraphs)
  
//remove parameter links to block subgraphs (outer edges)
//(keep parameter links to nodes inside the subgraphs)
let removeBlockParameterLinks (((vx,es),subgraphs) as graphs) =
  let fromSet =                                          //'from' nodes of subgraph parameter links
    subgraphs 
    |> subgraphEdges 
    |> List.filter (fun (_,e)->e.Var.IsParameter || e.Var.IsConstant) 
    |> List.map (fun (_,e) -> e.From)
    |> set
  let keepEdges = es |> List.filter (fun e -> fromSet.Contains e.From |> not)
  (vx,keepEdges),subgraphs
 

  //visualize ((vx,es),subgraphs)

let (((vx,es),subgraphs) as graphs) = 
  computationGraphs true model_t2 
  |> removeBlockParameterLinks 
  //|> relinkBlockOutputs 
  //|> relinkBlockInputs


visualize graphs

let testMuch() =
  let fld = @"D:\repodata\fscntk"
  let mdlFls = System.IO.Directory.EnumerateFiles(fld,"*.bin") |> Seq.toArray
  for f in mdlFls do
    printfn "testing %s" f
    let model = Function.Load(f,device)
    let graphs =
      computationGraphs false model 
      |> removeBlockParameterLinks 
      |> relinkBlockInputs
      |> relinkBlockOutputs 
    visualize graphs


