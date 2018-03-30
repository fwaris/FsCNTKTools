namespace FsCNTK.Tools
open CNTK
open System
type C = CNTK.CNTKLib
open System.Collections.Generic

type Vertex = Vf of Function | Vv of Variable

type VarEdge = 
  {
    From          : string
    To            : string
    Var           : Variable
    IsRemapped    : bool
    ToPlaceholder : bool
  }
  with
  static member Default = {From="";To="";IsRemapped=false; Var=null; ToPlaceholder=false}

type SubG = 
  {
    Container : string
    BlockFn   : Function
    Vertices  : Vertex list
    Edges     : VarEdge list
  }

type Graph = 
  {
    Vertices          : Vertex list
    Edges             : VarEdge list
    Subgraphs         : SubG list
    Named             : IDictionary<Variable,string>
    RemappedOutEdges  : IDictionary<string*string,VarEdge>
  }
  with static member Default = {Vertices=[]; Edges=[]; Subgraphs=[]; Named=dict[]; RemappedOutEdges=dict[]}

type Expand = NoExpansion | AllBlocks | Blocks of string list

//module for graph construction from CNTK model
module ModelGraph =
  
  let inline mCollect m k v = 
    let vs = match m |> Map.tryFind k with Some ls -> v::ls | None -> [v]
    Map.add k vs m

  let inline mCollectH (m:#IDictionary<'k,'v list>) k v = 
    let v' =
      match m.TryGetValue(k) with
      | true,ls -> v::ls
      | false,_ -> [v]
    m.[k] <- v' 
    m

  let inline mRemove m k v = 
    let vs = match m |> Map.tryFind k with Some ls -> ls |> List.filter (fun v'-> v'<>v) | None -> []
    Map.add k vs m

  let isPlaceHolder = function Vv v when v.IsPlaceholder -> true | _ -> false
  let isBlock = function Vf v when v.IsBlock -> true | _ -> false
  let isOutput = function Vv v when v.IsOutput -> true | _ -> false
  let toSubG (blockFn:Function) g = {BlockFn=blockFn; Container=blockFn.Uid; Vertices=g.Vertices; Edges=g.Edges}
  let placeholder = function Vv v when v.IsPlaceholder -> Some v | _ -> None
  let frmTo e = e.From,e.To

  let toVertex (n:obj) = 
    match n with 
    | :? Function as f -> Vf f 
    | :? Variable as v -> Vv v 
    | _ -> failwith "unknown node"

  let uid (names:IDictionary<Variable,string>) = function 
    | Vf n -> n.Uid 
    | Vv n -> match names.TryGetValue n with true,n->n | _ -> n.Uid

  let name = function Vf n -> n.Name | Vv n->n.Name

  let isVisited id = Set.contains id

  type private TraversalState = 
    {
      Visits    : Set<string>
      Vertices  : Vertex list
      Edges     : Set<string*string>
      Named     : IDictionary<Variable,string>
    }
    with static member Default = {Visits=Set.empty; Vertices=[]; Edges=Set.empty; Named=dict[]}

  //recursively visit all nodes and 
  //collect vertices and edges - first pass
  let rec private traverse tstate (n:obj) = 
    let vrtx = toVertex n
    let vertexId = uid tstate.Named vrtx
    if isVisited vertexId tstate.Visits then
      tstate
    else
      let visits = tstate.Visits.Add vertexId
      match vrtx with
      | Vf f -> 
        let tstate = {tstate with Vertices=vrtx::tstate.Vertices; Visits = visits}
        let tstate =      (tstate,f.Arguments) ||> Seq.fold traverse 
        let tstate = (tstate,[f.RootFunction]) ||> Seq.fold traverse
        let tstate =         (tstate,f.Inputs) ||> Seq.fold traverse
        let tstate =        (tstate,f.Outputs) ||> Seq.fold traverse
        let edges =    (tstate.Edges,f.Inputs) ||> Seq.fold (fun es n -> Set.add ( n |> toVertex |> uid tstate.Named ,vertexId) es)
        let edges =          (edges,f.Outputs) ||> Seq.fold (fun es n -> Set.add (vertexId,  n |> toVertex |> uid tstate.Named) es)
        {tstate with Edges=edges}
      | Vv v -> 
        let tstate = {tstate with Vertices=vrtx::tstate.Vertices} 
        let tstate = if v.Owner <> null then traverse tstate v.Owner else tstate
        tstate

  // collapse edges that run through output variable nodes
  //remove output variable nodes from the graph
  let private collapseVarEdges tstate =
    let vertices = tstate.Vertices
    let edges = tstate.Edges
    let varMap = vertices |> List.choose (function Vv v -> Some v | _ -> None) |> List.map (fun v->v.Uid,v) |> Map.ofList
    let getVar (vfrm,vto) = match varMap |> Map.tryFind vfrm with Some v -> v | None -> match varMap |> Map.tryFind vto with Some v -> v | None -> failwith "one end should be a variable"
    let outputVarMap =vertices |> List.choose (function Vv v -> (if v.IsOutput then Some v else None) | _ -> None)  |> List.map (fun v->v.Uid,v) |> Map.ofList
    let outEges = (Map.empty,edges) ||> Seq.fold (fun m (f,t) -> 
      let v = match m |> Map.tryFind f with Some ls -> t::ls | None -> [t]
      m |> Map.add f v)
    let collapsedEdges,removeNodes = 
      (([],[]),edges) 
      ||> Seq.fold (fun (edges,rems) (vfrm,vto) -> 
          match outputVarMap |> Map.tryFind vto with 
          | Some v ->
              let toNodes = match outEges |> Map.tryFind v.Uid with Some ls -> ls | None -> []
              if List.isEmpty toNodes then
                ({VarEdge.Default with From=vfrm;To=vto;Var=v;}::edges,rems)
              else
                let newEdges = toNodes |> List.map (fun n -> {VarEdge.Default with From=vfrm;To=n;Var=v})
                (newEdges @ edges, v.Uid::rems)
          | None ->
            match outputVarMap |> Map.tryFind vfrm with
            | Some v -> 
              (edges,rems)
            | None -> {VarEdge.Default with From=vfrm;To=vto;Var=getVar(vfrm,vto)}::edges, rems)
    let removeSet = set removeNodes
    let vx' = vertices |> List.filter (uid tstate.Named >> removeSet.Contains >> not)
    let es' = collapsedEdges
    {Graph.Default with Vertices=vx'; Edges=es'; Named=tstate.Named}
    

//remove edges that have the same source and destination
//happens with Combine op, at least
  let excludeSelfLinks (graph:Graph) = {graph with Edges=graph.Edges |> List.filter (fun e -> e.From<>e.To)}
    
  let axisVector (is:Axis seq) =
      let vs = new AxisVector(Seq.length is)
      is |>  Seq.iter vs.Add
      vs

  let fixFunction (fn:Function) = 
    let nameless = 
      fn.Inputs 
      |> Seq.filter (fun v-> v.IsInput && String.IsNullOrWhiteSpace v.Name && String.IsNullOrWhiteSpace v.Uid) 
      |> Seq.toList
    fn,nameless |> List.mapi(fun i v->v,sprintf"Input%d" i)

  //create the computational graph for a single function
  let functionGraph (f:Function) = 
    let (f,ns) = fixFunction f
    let tstate = traverse {TraversalState.Default with Named=dict ns} f.RootFunction
    let es = Set.union tstate.Edges (f.Outputs |> Seq.map (fun v -> v.Owner.Uid,v.Uid) |> set)
    {tstate with Edges=es}
    |> collapseVarEdges
    |> excludeSelfLinks
  
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
    (phMap:IDictionary<Variable,Function>)   //placeholder to target function
    (linkMap:IDictionary<Variable,Variable>) 
    (edge:VarEdge)
    = 
    match linkMap.TryGetValue(edge.Var) with
    | true,ph -> 
      let targetFunction = phMap.[ph]
      {edge with To=targetFunction.Uid; IsRemapped=true; ToPlaceholder=true}
    | false,_ -> edge

  let remapFrom 
    (srcMap:IDictionary<Variable,Function>) 
    (linkMap:IDictionary<Variable,Variable>)
    (edge:VarEdge)
    = 
    match linkMap.TryGetValue(edge.Var) with
    | true,v -> 
      let srcFunction = srcMap.[v]
      {edge with From=srcFunction.Uid; IsRemapped=true; Var=v}
    | false,_ -> edge

  let allVertices (graph:Graph) = graph.Vertices @ (graph.Subgraphs |> List.collect (fun sg -> sg.Vertices)) 
  let allEdges (graph:Graph) = graph.Edges @ (List.collect (fun (sg:SubG) -> sg.Edges) graph.Subgraphs)      //all edges
  let subgraphEdges = List.collect (fun (sg:SubG) -> sg.Edges |> List.map (fun e->sg.Container,e))
  let subgraphVertices = List.collect(fun (sg:SubG) -> sg.Vertices |> List.map (fun v->sg.Container,v))

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

  let orderdPh fn = 
    let rec orderedPh  acc (fn:Function) =
      let acc = (acc,fn.Placeholders()) ||> Seq.fold (fun (vs:Set<string>,acc) ph -> if vs.Contains ph.Uid then vs,acc else (Set.add ph.Uid vs,ph::acc))
      let acc = (acc,fn.Arguments) ||> Seq.fold (fun acc arg-> if arg.Owner <> null then orderedPh acc arg.Owner else acc)
      acc
    orderedPh (Set.empty,[]) fn |> snd //|> List.rev  //seems reversing is not needed here

  let relinkBlockInputs2 (graph:Graph) =
    let vxsMap = graph.Vertices |> List.filter isBlock |> List.choose (function Vf f -> Some(f.Uid,f) | _ -> None) |> Map.ofList

    let remapped = 
      graph.Subgraphs
      |> List.map (fun g ->

        let block = vxsMap.[g.Container]
        let args = block.Arguments |> Seq.toList
        let blkRoot = block.BlockRoot()
        let phs = orderdPh blkRoot          //hopefully there is an ordering of placeholders that can be used to match arguments

        let matchedArgs =                   //placheholder argument mapping
          if args.Length = phs.Length then
            List.zip phs args |> List.filter (fun (a,b) -> varSignature a = varSignature b)
          else
            []
        
        let phArgMap = dict matchedArgs    //matched placeholder to arguments lookup table

        let phOwnerMap =                   //placeholder and owner function map
          g.Vertices 
          |> List.collect (function  | Vf f->  f.Placeholders() |> Seq.toList |> List.map (fun p->p,f)  | _  -> []) 
          |> List.filter (fun (ph,f) -> phArgMap.ContainsKey ph)
          |> dict 
        
        let addEdges,removeEdges,removeVxs = 
          (([],[],[]),matchedArgs)
          ||> List.fold (fun (addAcc,remAcc,remVxAcc) (ph,arg) ->

            let phOwnerId = phOwnerMap.[ph].Uid

            let hasE,e =  graph.RemappedOutEdges.TryGetValue ((arg.Uid, g.Container))

            let addE,remEs,remVx =
              if hasE then
                (
                  {e with To=phOwnerId; ToPlaceholder=true},            //re-link incoming edge to owner of placeholder as new edge
                  [(e.From,e.To); (ph.Uid,phOwnerId) ],                 //remove incoming edge
                  ph                                                    //remove placeholder vertex
                )
              else
                let argId = if arg.Owner <> null then arg.Owner.Uid else arg.Uid
                (
                  {VarEdge.Default with From=argId; To=phOwnerId; IsRemapped=true; ToPlaceholder=true; Var=arg},
                  [ (argId, g.Container); (ph.Uid, phOwnerId); ],
                  ph
                )

            (addE::addAcc), (remEs::remAcc), (remVx::remVxAcc)
          )

        let removedPh = HashSet removeVxs
        let removeEdges = List.collect (fun x->x) removeEdges |> set

        let g = 
          { g with 
              Vertices = g.Vertices |> List.filter (function Vv v when v.IsPlaceholder -> removedPh.Contains v |> not | _ -> true)
              Edges = g.Edges |> List.filter (frmTo>>removeEdges.Contains>>not)
          }

        addEdges, removeEdges, g
      )
       
    let addEdges,removeEdges,subgraphs = 
      (([],Set.empty,[]),remapped) 
      ||> List.fold (fun (aE,rE,gs) (e,r,g)-> aE @ e, Set.union rE r, List.append gs [g])

    let es = graph.Edges |> List.filter (frmTo>>removeEdges.Contains>>not)
    let es = es @ addEdges

    {graph with Edges=es; Subgraphs=subgraphs}

  let relinkBlockInputs (graph:Graph) =

    let edges = allEdges graph
    let blkPhs = blockPlaceHolders graph.Subgraphs  //block placeholders

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
    let toRemove = blkInps @ remappedInputs |> List.map (fun e -> e.From,e.To) |> set
    let es = graph.Edges |> List.filter (fun e->toRemove.Contains(e.From,e.To) |> not) 
    let es = es @ remappedInputs
    let subgraphs = graph.Subgraphs |> List.map (fun sg -> 
      {sg with
        Vertices = sg.Vertices |> List.filter (function Vv v->phMap.ContainsKey v |> not | _ -> true)
        Edges=sg.Edges |> List.filter (fun e->phMap.ContainsKey e.Var |> not)})
    {graph with Edges=es; Subgraphs=subgraphs}

  let relinkBlockOutputs (graph:Graph) =
    let sgIds = graph.Subgraphs |> List.map (fun g->g.Container) |> set

    let blkOutputMap = 
      graph.Vertices 
      |> List.filter (uid graph.Named >> sgIds.Contains) //only look at block functions that are expanded
      |> List.collect (function 
        | Vf f when f.IsBlock ->  //e.g. lstm
          let root = f.BlockRoot() //e.g. combine
          Seq.zip f.Outputs root.Outputs 
          |> Seq.map(fun (a,b) -> a,b,root)
          |> Seq.toList //assume block outputs correspond to block root outputs, by order
        | _ -> []) 

    let varUsedInEdges = (Dictionary<_,_>(),graph.Edges) ||> List.fold (fun acc (e:VarEdge) -> mCollectH acc e.Var e)

    let removeList,addList,replaceList = 
      (([],[],[]),blkOutputMap) 
      ||> List.fold (fun (accRemove,accAdd,accReplace) (blkOutVar,rootFnOutVar,blockRootFn) ->
        let blkOutEs = varUsedInEdges.[blkOutVar]
        let remapped = blkOutEs |> List.map (fun e -> 
          {e with From=blockRootFn.Uid; Var=rootFnOutVar; IsRemapped=true})
        blkOutEs::accRemove,
        remapped::accAdd,
        accReplace @ List.zip blkOutEs remapped)

    let toRemove = removeList |> List.collect (fun es -> es |> List.map (fun e->e.From,e.To)) |> set
    let es = graph.Edges |> List.filter (fun e -> toRemove.Contains(e.From,e.To) |> not)
    let es = es @ (addList |> List.collect (fun es->es))

    let sgVxsToRemove = blkOutputMap |> Seq.map(fun (_,v,_) ->v.Uid) |> set

    //out edges remapped - keep old around for remapping input
    let replaceMap = replaceList |> List.map (fun (oldE,newE) -> (oldE.Var.Uid,oldE.To),newE) |> dict 

    let subgraphs = graph.Subgraphs |> List.map (fun sg -> 
      {sg with
        Vertices = sg.Vertices |> List.filter (uid graph.Named >> sgVxsToRemove.Contains >> not) 
        Edges=sg.Edges |> List.filter (fun e->sgVxsToRemove.Contains e.To |> not)})
    {graph with Edges=es; Subgraphs=subgraphs; RemappedOutEdges=replaceMap}


  ///List block operations and their unique ids in the given function.
  ///Results can be used to identify which blocks to expand in the graph
  let blocks fn =
    let g = functionGraph fn 
    g.Vertices |> List.filter isBlock |> List.map (uid g.Named) 
 
  //remove parameter links to block subgraphs (outer edges)
  //(keep parameter links to nodes inside the subgraphs)
  let removeBlockParameterLinks graph =
    let fromSet =                                          //'from' nodes of subgraph parameter links
      graph.Subgraphs 
      |> subgraphEdges 
      |> List.filter (fun (_,e)->e.Var.IsParameter || e.Var.IsConstant) 
      |> List.map (fun (_,e) -> e.From)
      |> set
    let keepEdges = graph.Edges |> List.filter (fun e -> fromSet.Contains e.From |> not)
    {graph with Edges=keepEdges}

  let private chooseBlocks blocks matchList =
    let ms = matchList |> List.map (fun (s:string) ->s.ToLower())
    blocks 
    |> List.map (fun (a:string,b:string) -> b, [a.ToLower();b.ToLower()])
    |> List.choose (fun (b,ls) -> 
      let allParis = seq {for l in ls do for m in ms do yield (l,m)}
      if allParis |> Seq.exists (fun (l,m)->l.Contains m) then
        Some b
      else
        None)

  ///create root computational graph and optionally subgraphs nested one level down
  let computationGraphs expand (fn:Function) =
    let graph = functionGraph fn
    let subgraphs =
      match expand with
      | NoExpansion -> []
      | AllBlocks ->
            graph.Vertices |> List.choose (function 
            | Vf fn when fn.IsBlock -> fn.BlockRoot() |> functionGraph |> toSubG fn |> Some
            | _ -> None)
      | Blocks list ->
            let blockIds = graph.Vertices |> List.filter isBlock |> List.choose (function Vf f-> Some(f.OpName,f.Uid) | _ -> None)
            let targetBlocks = chooseBlocks blockIds list |> set
            graph.Vertices |> List.choose (function 
            | Vf fn when targetBlocks.Contains fn.Uid -> fn.BlockRoot() |> functionGraph |> toSubG fn |> Some
            | x -> None)
    if List.isEmpty subgraphs then
      graph
    else
      {graph with Subgraphs=subgraphs}
      |> removeBlockParameterLinks
      |> relinkBlockOutputs
      |> relinkBlockInputs2

  
//module for visualization of model graphs
module ModelViz = 
  open Microsoft.Msagl.Drawing 
  open ModelGraph

  let edgeLabel (e:VarEdge) = 
    let v = e.Var
    if v.IsConstant then
      ""
    else
      let toPh = if e.ToPlaceholder then " -> [??placeholder??]" else ""
      sprintf "%s %s\r\n%A" v.Uid toPh  (v.Shape.Dimensions |> Seq.toList)

  let opNameMap =
    [
      "times","@"
      "plus","+"
      "minus","-"
      "elementtimes",".*"
    ]
    |> Map.ofList

  let opName (s:string) = s.ToLower() |> Map.tryFind <| opNameMap

  let nodeLabel = function
    | Vf f -> f.OpName |> opName |> Option.defaultValue f.OpName
    | Vv v -> 
      let n = 
        if String.IsNullOrWhiteSpace(v.Name) |> not then v.Name 
        elif v.IsInput then "Input"
        elif v.IsOutput then "Output"
        elif v.IsParameter then "Parameter"
        elif v.IsPlaceholder then "Placeholder"
        elif v.IsConstant then 
          let cv = v.GetValue()
          let cv = Value.Create(v.Shape,[cv],DeviceDescriptor.CPUDevice)
          let cval = cv.GetDenseData<float32>(v).[0].[0]
          string cval
        else ""
      sprintf "%s\r\n%A" n (v.Shape.Dimensions |> Seq.toList)

  let styleNode (n:Node) =
      let v = n.UserData :?> Vertex
      n.LabelText <- nodeLabel v
      n.Attr.LabelMargin <- 5
      match v with 
      | Vv vr -> 
        if vr.IsInput then 
          n.Attr.Shape <- Shape.Ellipse
          n.Attr.FillColor <- Color.Azure
        elif vr.IsOutput then 
          n.Attr.Shape <- Shape.Ellipse
          n.Attr.FillColor <- Color.LavenderBlush
          n.Attr.LineWidth <- 2.0
        elif vr.IsConstant then 
          n.Attr.Shape <- Shape.Mdiamond
          n.Attr.FillColor <- Color.Cornsilk
      | Vf fn -> 
        n.Attr.FillColor <- Color.Bisque
        fn.OpName |> opName |> Option.iter (fun _ -> n.Attr.Shape <- Shape.Circle)
        if fn.IsBlock then n.Attr.LineWidth <- 3.0

  let styleEdge (e:Edge) =
      let tE = e.UserData :?> VarEdge
      e.LabelText <- edgeLabel tE
      if tE.IsRemapped then e.Attr.AddStyle Style.Dotted
      if tE.ToPlaceholder then e.Attr.Color <- Color.IndianRed

  //simple graph (no subgraphs)
  let makeGraph graph =
    let g = new Microsoft.Msagl.Drawing.Graph()
    let drawingNodes = graph.Vertices |> List.map (fun v -> let n = (uid graph.Named>>g.AddNode) v in n.UserData<-v; n)
    drawingNodes |> List.iter styleNode
    let drawingEdges = graph.Edges |> List.map(fun e -> let ed = g.AddEdge(e.From,e.To) in ed.UserData <- e; ed)
    drawingEdges |> List.iter styleEdge
    g

  //graph with subgraphs
  let makeGraphs graph =
    let g = new Microsoft.Msagl.Drawing.Graph()
    let root = new Subgraph("root")
    let uid = uid graph.Named
    let allVxs = allVertices graph //graph.Vertices  @ (List.collect (fun (sg:SubG) -> sg.Vertices) graph.Subgraphs)
    let sgIds = graph.Subgraphs |> List.map (fun (sg:SubG)->sg.Container) |> set
    let blockVxs = allVxs |> List.filter (uid >> sgIds.Contains)
    let baseVxs = allVxs |> List.filter (uid >> sgIds.Contains >> not)
    let subGraphs = blockVxs |> List.map (fun v -> uid v, new Subgraph("sg_" + uid v, UserData=v, LabelText=nodeLabel v))
    let sgMap = subGraphs |> Map.ofList
    let nodes = baseVxs |> List.map (fun v -> new Node(uid v, UserData=v, LabelText=nodeLabel v))
    let nodeMap = nodes |> List.map (fun n -> n.Id,n) |> Map.ofList

    let subgraphNodes =          //subgraphs own vertices plus any parameter inputs (the graph looks better)
      (Map.empty,graph.Subgraphs) 
      ||> List.fold(fun acc (sg:SubG) -> 
        (acc,sg.Vertices) 
        ||> List.fold (fun acc v-> 
          let acc = mCollect acc sg.Container (uid v)
          match v with
          | Vf f -> (acc,f.Inputs) ||> Seq.fold(fun acc i -> if i.IsParameter then mCollect acc sg.Container (uid v) else acc)
          | _ -> acc))

    let subgraphNodeIds = subgraphNodes |> Map.toSeq |> Seq.collect snd |> set

    let rootNodes = 
      graph.Vertices 
      |> List.filter (uid >> subgraphNodeIds.Contains >> not) 
      |> List.choose (uid >> nodeMap.TryFind) 

    nodes |> List.iter styleNode

    g.RootSubgraph <- root
    nodes |> List.iter g.AddNode
    subGraphs |> List.iter (snd >> root.AddSubgraph)
    rootNodes |> List.iter (root.AddNode) //this might break in future as we are mixing subgraphs and nodes

    subgraphNodes |> Map.iter (fun sgId vxIds -> 
      sgMap.TryFind(sgId) |> Option.iter(fun sgNode -> 
        vxIds |> List.iter (nodeMap.TryFind >> (Option.iter sgNode.AddNode)))) 
      
    let es = allEdges graph //graph.Edges @ (List.collect (fun (sg:SubG)->sg.Edges) subgraphs)
    let sgIdMap = sgMap |> Map.map (fun k v->v.Id) // |> Seq.append rootNodes |> List.map(fun |> Seq.map (fun (k,sg)->k,sg.Id) |> Map.ofSeq
    let drawingEdges =
      es 
      |> List.map (fun e ->
        { e with
            From = sgIdMap.TryFind e.From |> Option.defaultValue e.From
            To    = sgIdMap.TryFind e.To |> Option.defaultValue e.To
        })
      |> List.map (fun e->g.AddEdge(e.From,edgeLabel e,e.To, UserData=e))
    drawingEdges |> List.iter styleEdge
    g
  
  ///visualize a graph given vertices, edges and subgraphs
  let visualize graph =
    let gv = new Microsoft.Msagl.GraphViewerGdi.GViewer()
    let g = 
      if List.isEmpty graph.Subgraphs then
        makeGraph graph
      else
        makeGraphs graph
    g.Edges |> Seq.iter (fun e->  if e.Label<> null then e.Label.FontSize <- 8.0)
    gv.Graph <- g
    let f = new System.Windows.Forms.Form()
    f.SuspendLayout()
    gv.Dock <- System.Windows.Forms.DockStyle.Fill
    f.Controls.Add(gv)
    gv.Invalidate()
    gv.Update()
    f.ResumeLayout()
    f.Show()
  
  ///construct and show the function graph
  let showGraph expand f = ((computationGraphs expand) >> visualize) f
