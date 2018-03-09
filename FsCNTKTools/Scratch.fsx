#load "SetEnv.fsx"

open CNTK
open System
open System.Windows.Forms
open FSCNTK.Tools.Graph
open System.Collections.Generic
open FSCNTK.Tools.Graph.grph
open System.Windows.Controls

type C = CNTK.CNTKLib

let test_model = __SOURCE_DIRECTORY__ + "/test_model.bin"
let t2 = @"D:\repodata\fscntk\m_fs_untrained.bin"

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

let remapEdge 
  (phMap:IDictionary<Variable,Function>) 
  (linkMap:IDictionary<Variable,Variable>)
  (edge:Edge)
  = 
  let ph = linkMap.[edge.Var]
  let targetFunction = phMap.[ph]
  {edge with To=targetFunction.Uid}

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
  ////let ((vx,es),subgraphs) = computationGraphs model
  //let vertices = allVertices graphs
  let edges = allEdges graphs
  let blkPhs = blockPlaceHolders subgraphs

  let blockInputs =  //inputs coming into each block function
    let blockIdSet = blkPhs |> List.map (fun (c,_,_)->c) |> set
    edges |> List.filter (fun e -> blockIdSet.Contains e.To && not e.Var.IsParameter )
  
  let blckInpMap = blockInputs |> List.groupBy (fun e->e.To) |> Map.ofList

  let (links,_) =                                     //placeholders matched to block inputs
    (([],blckInpMap),blkPhs) 
    ||> List.fold (fun (acc,inpMap) (blockId,ph,_) ->
      inpMap 
      |> Map.tryFind blockId
      |> Option.map (List.map (fun e->e.Var))
      |> Option.bind (matchVars ph)
      |> Option.map (fun edgeVar ->   //matched input
        (edgeVar,ph)::acc,
        let es' = inpMap.[blockId] |> List.filter (fun e->e.Var<>edgeVar) 
        inpMap |> Map.add blockId es')
      |> Option.defaultValue (acc,inpMap))

  //retarget block input edges to owners of placeholders
  //the 'to' end should be the function which 'owns' the placeholder
  //remove placeholders that were matched
  let phMap = blkPhs |> List.map (fun (c,v,f) -> v,f) |> dict
  let linkMap = dict links
  let blockInputs' = blockInputs |> List.map (remapEdge phMap linkMap)
  let toRemoveSet = blockInputs |> List.map (fun {From=vFrm;To=vTo} -> vFrm,vTo) |> set
  let es = es |> List.filter (fun {From=vFrm;To=vTo} -> toRemoveSet.Contains (vFrm,vTo) |> not)
  let es = es @ blockInputs'
  let subgraps = subgraphs |> List.map (fun sg -> {sg with Edges=sg.Edges |> List.filter (fun e->phMap.ContainsKey e.Var |> not)})
  ((vx,es),subgraphs)


let relinkBlockOutputs (((vx,es),subgraphs) as graphs) = 
  let rootOutMap = 
    vx 
    |> List.collect (function 
      | Vf f when f.IsBlock -> 
        let root = f.BlockRoot()
        root.Outputs 
          |> Seq.map (fun outV -> f.Uid,outV,root) 
          |> Seq.toList
      | _ -> []) 
    |> List.groupBy (fun (id,_,_) -> id)
    |> Map.ofList

  let blkOutEdges = es |> List.choose (function e when rootOutMap.ContainsKey e.From -> Some(e.From,e) | _ -> None)

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

  let (links,_) =                                     //block outputs mapped to root function outputs
    let accMap = rootOutMap |> Map.map (fun _ xs -> xs |> List.map (fun (_,v,_) -> v))
    (([],accMap),uniqOutEs) 
    ||> List.fold (fun (acc,accMap) (blockId,edgeVar) ->
      accMap 
      |> Map.tryFind blockId
      |> Option.bind (matchVars edgeVar)
      |> Option.map (fun outVar ->        //matched input
        (edgeVar,outVar)::acc,
        (mRemove accMap blockId outVar))  
      |> Option.defaultValue (acc,accMap))
   
  let blkRoots = rootOutMap |> Map.toSeq |> Seq.collect (fun (c,xs) -> xs |> List.map(fun (_,v,f) -> v,f)) |> dict

  let linkMap = dict links

  let blkOutEdges' = blkOutEdges |> List.map snd |> List.map (remapEdge blkRoots linkMap)
  let toRemoveSet = blkOutEdges |> List.map (fun (_,{From=vFrm;To=vTo}) -> vFrm,vTo) |> set
  let es = es |> List.filter (fun {From=vFrm;To=vTo} -> toRemoveSet.Contains (vFrm,vTo) |> not)
  let es = es @ blkOutEdges'
  let subgraps = subgraphs |> List.map (fun sg -> {sg with Edges=sg.Edges |> List.filter (fun e->blkRoots.ContainsKey e.Var |> not)})
  ((vx,es),subgraphs)
  
//remove parameter links to block subgraphs (outer edges)
//(keep parameter links to nodes inside the subgraphs)
let removeBlockParameterLinks (((vx,es),subgraphs) as graphs) =
  let fromSet =                                          //'from' nodes of subgraph parameter links
    subgraphs 
    |> subgraphEdges 
    |> List.filter (fun (_,e)->e.Var.IsParameter) 
    |> List.map (fun (_,e) -> e.From)
    |> set
  let keepEdges = es |> List.filter (fun e -> fromSet.Contains e.From |> not)
  (vx,keepEdges),subgraphs
 

  //visualize ((vx,es),subgraphs)

let (((vx,es),subgraphs) as graphs) = 
  computationGraphs true model_t2 
  |> removeBlockParameterLinks 
  //|> relinkBlockOutputs 
  |> relinkBlockInputs



visualize graphs


module grph = 
  open Microsoft.Msagl.Drawing 

  let makeGraph() =
    let g = new Microsoft.Msagl.Drawing.Graph()
    g.AddEdge("47","58") |> ignore
    g.AddEdge("70","71") |> ignore

    let sg1 = new Subgraph("sg1")
    g.RootSubgraph <- sg1
    sg1.AddNode(g.FindNode("47"))
    sg1.AddNode(g.FindNode("58"))

    let sg2 = new Subgraph("sg2")
    sg2.DiameterOfOpenCollapseButton <- 20.
    sg2.CollapseButtonColorActive <- Color.Blue
    sg2.CollapseButtonColorInactive <- Color.Red
    sg2.AddNode(g.FindNode("70"))
    sg2.AddNode(g.FindNode("71"))
    sg1.AddSubgraph(sg2)
    g.AddEdge("58",sg2.Id) |> ignore
    g.Attr.LayerDirection <- LayerDirection.LR
    g

  
open Microsoft.Msagl.WpfGraphControl
#r "PresentationCore"
#r "PresentationFramework"
#r "WindowsBase"
open System
open System.Windows
open System.Windows.Controls

let testWpf() =
  let gv = new GraphViewer()
  let window = new Window(Title = "Simple Test", Width = 800., Height = 600.)
  let d = new DockPanel()
  window.Content <- d
  gv.BindToPanel(d)
  window.Show()

  gv.Graph <- grph.makeGraph()
