namespace FSCNTK.Tools
open CNTK
open System
type C = CNTK.CNTKLib
  open System.Collections.Generic

module Graph =
  
  let inline mCollect m k v = 
    let vs = match m |> Map.tryFind k with Some ls -> v::ls | None -> [v]
    Map.add k vs m

  let inline mRemove m k v = 
    let vs = match m |> Map.tryFind k with Some ls -> ls |> List.filter (fun v'-> v'<>v) | None -> []
    Map.add k vs m

  type Vertex = Vf of Function | Vv of Variable
  type Edge = {From:string; To:string; Var:Variable}
  type SubG = {Container:string; Vertices:Vertex list; Edges:Edge list}

  let isPlaceHolder = function Vv v when v.IsPlaceholder -> true | _ -> false
  let isBlock = function Vf v when v.IsBlock -> true | _ -> false
  let isOutput = function Vv v when v.IsOutput -> true | _ -> false
  let toSubG uid (vx,es) = {Container=uid; Vertices=vx; Edges=es}

  let toVertex (n:obj) = 
    match n with 
    | :? Function as f -> Vf f 
    | :? Variable as v -> Vv v 
    | _ -> failwith "unknown node"

  let uid = function 
    | Vf n -> n.Uid 
    | Vv n -> 
      //if n.IsInput then
      //  let i = 1
      //  ()
      //if String.IsNullOrWhiteSpace n.Uid then 
      //  n.ToFunction().Uid 
      //else 
        n.Uid

  let name = function Vf n -> n.Name | Vv n->n.Name

  let isVisited id = Set.contains id

  //recursively visit all nodes and 
  //collect vertices and edges - first pass
  let rec traverse (vertices,edges,visits) (n:obj) = 
    let vrtx = toVertex n
    let vertexId = uid vrtx
    if isVisited vertexId visits then
      (vertices,edges,visits)
    else
      let visits = visits.Add vertexId
      match vrtx with
      | Vf f -> 
        let acc = (vrtx::vertices,edges,visits)
        let acc = (acc,f.Arguments) ||> Seq.fold traverse 
        let acc = (acc,[f.RootFunction]) ||> Seq.fold traverse
        let acc = (acc,f.Inputs) ||> Seq.fold traverse
        let (vertices,edges,vists) = (acc,f.Outputs) ||> Seq.fold traverse
        let edges =  (edges,f.Inputs) ||> Seq.fold (fun es n -> Set.add ( n |> toVertex |> uid ,vertexId) es)
        let edges = (edges,f.Outputs) ||> Seq.fold (fun es n -> Set.add (vertexId,  n |> toVertex |> uid) es)
        (vertices,edges,vists)
      | Vv v -> 
        let acc = (vrtx::vertices,edges,visits)
        let acc = if v.Owner <> null then traverse acc v.Owner else acc
        acc

  // collapse edges that run through output variable nodes
  //remove output variable nodes from the graph
  let collapseVarEdges (vertices,edges) =
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
                ({From=vfrm;To=vto;Var=v}::edges,rems)
              else
                let newEdges = toNodes |> List.map (fun n -> {From=vfrm;To=n;Var=v})
                (newEdges @ edges, v.Uid::rems)
          | None ->
            match outputVarMap |> Map.tryFind vfrm with
            | Some v -> 
              (edges,rems)
            | None -> {From=vfrm;To=vto;Var=getVar(vfrm,vto)}::edges, rems)
    let removeSet = set removeNodes
    let vx' = vertices |> List.filter (uid>>removeSet.Contains>>not)
    let es' = collapsedEdges 
    vx',es'

//remove edges that have the same source and destination
//happens with Combine op, at least
  let excludeSelfLinks (vxs,es) = vxs, es |> List.filter (fun e -> e.From<>e.To)
    
  let axisVector (is:Axis seq) =
      let vs = new AxisVector(Seq.length is)
      is |>  Seq.iter vs.Add
      vs

  //msagl requires names for all nodes, input nodes can be nameless so replace them if need be
  let fixFunction (fn:Function) = 
    let nameless = fn.Inputs |> Seq.filter (fun v-> v.IsInput && String.IsNullOrWhiteSpace v.Name) |> Seq.toList
    if Seq.isEmpty nameless then
      fn
    else
      let nClones = nameless |> List.mapi (fun i v-> 
              let name = sprintf "Unamed input %d" i
              CNTKLib.InputVariable(v.Shape,v.IsSparse,v.DataType,v.NeedsGradient,name,axisVector v.DynamicAxes))
      let mapping = Seq.zip nameless nClones |> dict
      fn.Clone(ParameterCloningMethod.Share,mapping)

  //create the computational graph for a single function
  let functionGraph (f:Function) = 
    let f = fixFunction f
    let (vxs,es,vs) = traverse ([],Set.empty,Set.empty) f.RootFunction
    let es = Set.union es (f.Outputs |> Seq.map (fun v -> v.Owner.Uid,v.Uid) |> set)
    (vxs,es)
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
    let toRemove = blkInps @ remappedInputs |> List.map (fun e -> e.From,e.To) |> set
    let es = es |> List.filter (fun e->toRemove.Contains(e.From,e.To) |> not) 
    let es = es @ remappedInputs
    let subgraphs = subgraphs |> List.map (fun sg -> 
      {sg with
        Vertices = sg.Vertices |> List.filter (function Vv v->phMap.ContainsKey v |> not | _ -> true)
        Edges=sg.Edges |> List.filter (fun e->phMap.ContainsKey e.Var |> not)})
    ((vx,es),subgraphs)

  let relinkBlockOutputs (((vxs,es),subgraphs) as graphs) = 
    let sgIds = subgraphs |> List.map (fun g->g.Container) |> set
    let blkOutpts = 
      vxs 
      |> List.filter (uid >> sgIds.Contains) //only look at block functions that are expanded
      |> List.collect (function 
        | Vf f when f.IsBlock -> 
          let root = f.BlockRoot()
          root.Outputs 
            |> Seq.map (fun outV -> f.Uid,outV,root) 
            |> Seq.toList
        | _ -> []) 
      |> List.groupBy (fun (id,_,_) -> id)
      |> Map.ofList

    let blkOutEdges = 
      es 
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
    let toRemove = (blkOutEdges |> List.map snd) @ remappedOutputs |> List.map (fun e->e.From,e.To) |> set
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

  //create root computational graph and optionally subgraphs nested one level down
  let computationGraphs expandBlocks (fn:Function) =
    //let fn = fixFunction fn
    let (vxs,es) = functionGraph fn
    if not expandBlocks then
      (vxs,es),[]
    else
      let subgraphs = 
        if expandBlocks then 
          vxs |> List.choose (function 
          | Vf fn when fn.IsBlock -> fn.BlockRoot() |> functionGraph |> toSubG fn.Uid |> Some
          | _ -> None)
        else []
      ((vxs,es),subgraphs) 
      |> removeBlockParameterLinks
      |> relinkBlockOutputs
      |> relinkBlockInputs
  
  //module supporting graph visualization
  module grph = 
    open Microsoft.Msagl.Drawing 
    open System.Collections.Generic
    
    let edgeLabel (v:Variable) = 
      if v.IsConstant then
        ""
      else
        sprintf "%s\r\n%A" v.Uid  (v.Shape.Dimensions |> Seq.toList)

    let nodeLabel = function
      | Vf f -> f.OpName
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

    let makeGraph (vertices,edges) =
      let g = new Microsoft.Msagl.Drawing.Graph()
      let drawingNodes = vertices |> List.map (uid>>g.AddNode) 
      drawingNodes 
      |> List.zip vertices 
      |> List.iter (fun (v,n)->
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
          if fn.IsBlock then n.Attr.LineWidth <- 3.0
      )
      let drawingEdges = edges |> Seq.map(fun e -> let ed = g.AddEdge(e.From,e.To) in ed.UserData <- e.Var; ed) |> Seq.toList
      (drawingEdges,edges) ||> List.zip |> List.iter (fun (e,ev) -> 
        //e.Label <- new Label()
        e.LabelText <- edgeLabel ev.Var
        //e.Label.FontSize <- 8.0
        //e.Label.Text <- edgeLabel ev.Var
      )
      g


    let makeGraphs ((vertices,edges),subgraphs) =
      let g = new Microsoft.Msagl.Drawing.Graph()
      let allVxs = vertices @ (List.collect (fun v -> v.Vertices) subgraphs)
      let sgIds = subgraphs |> List.map (fun sg->sg.Container) |> set
      let blockVxs = allVxs |> List.filter (uid >> sgIds.Contains)
      let baseVxs = allVxs |> List.filter (uid >> sgIds.Contains >> not)
      let root = new Subgraph("root")
      let subGraphs = blockVxs |> List.map (fun v -> uid v, new Subgraph("sg_" + uid v, UserData=v, LabelText=nodeLabel v))
      let sgMap = subGraphs |> Map.ofList
      let nodes = baseVxs |> List.map (fun v -> new Node(uid v, UserData=v, LabelText=nodeLabel v))
      let nodeMap = nodes |> List.map (fun n -> n.Id,n) |> Map.ofList

      let subgraphNodes =          //subgraphs own the their own vertices plus any parameter inputs (the graph looks better)
        (Map.empty,subgraphs) 
        ||> List.fold(fun acc sg -> 
          (acc,sg.Vertices) 
          ||> List.fold (fun acc v-> 
            let acc = mCollect acc sg.Container (uid v)
            match v with
            | Vf f -> (acc,f.Inputs) ||> Seq.fold(fun acc i -> if i.IsParameter then mCollect acc sg.Container (uid v) else acc)
            | _ -> acc))

      let subgraphNodeIds = subgraphNodes |> Map.toSeq |> Seq.collect snd |> set

      let rootNodes = 
        vertices 
        |> List.filter (uid >> subgraphNodeIds.Contains >> not) 
        |> List.choose (uid >> nodeMap.TryFind) 

      //nodes not in subgraphs are in the root subgraph
      //turn them into subgraphs and exclude then from other nodes 
      //subgraphs can only be linked to subgraphs (it seems in msagl) to this way root subgraph nodes can link to subgraph nodes
      let nodes,rootNodes =
        if List.isEmpty subGraphs then 
          nodes,rootNodes
        else
          let rootNodeSubgraphs = rootNodes |> List.map (fun n->
            let sg = new Subgraph(n.Id, UserData=n.UserData, LabelText=n.LabelText)
            sg.Attr.LabelMargin <- 20
            //let dummyNode = new Node(sg.Id + "1", LabelText="")
            //g.AddNode dummyNode
            //sg.AddNode dummyNode        
            sg :> Node)
          let nodes = let h = HashSet rootNodes in  nodes |> List.filter (h.Contains >> not)
          nodes,rootNodeSubgraphs


      g.RootSubgraph <- root
      nodes |> List.iter g.AddNode
      subGraphs |> List.iter (snd >> root.AddSubgraph)
      rootNodes |> List.iter (root.AddNode) //this might break in future as we are mixing subgraphs and nodes

      subgraphNodes |> Map.iter (fun sgId vxIds -> 
        sgMap.TryFind(sgId) |> Option.iter(fun sgNode -> 
          vxIds |> List.iter (nodeMap.TryFind >> (Option.iter sgNode.AddNode)))) 
      
      let es = edges @ (List.collect (fun sg->sg.Edges) subgraphs)
      let sgIdMap = sgMap |> Map.map (fun k v->v.Id) // |> Seq.append rootNodes |> List.map(fun |> Seq.map (fun (k,sg)->k,sg.Id) |> Map.ofSeq
      let es' =
        es 
        |> List.map (fun e ->
          { e with
              From = sgIdMap.TryFind e.From |> Option.defaultValue e.From
              To    = sgIdMap.TryFind e.To |> Option.defaultValue e.To
          })
        //|> List.map (fun e -> 
        //  match sgIdMap.TryFind e.From, sgIdMap.TryFind e.To with
        //  | Some sgFrm, Some sgTo -> 
        //    {e with 
        //      From = sgFrm   //retarget edges to subgraphs nodes 
        //      To   = sgTo
        //    }
        //  | _ -> e
        //)
        |> List.map (fun e->g.AddEdge(e.From,edgeLabel e.Var,e.To))
      g
  
  //let visualize ((nodes,edges),subgraphs) =  
  //  let gv = new GraphViewer()
  //  let window = new Window(Title = "Simple Test", Width = 800., Height = 600.)
  //  let d = new DockPanel()
  //  window.Content <- d
  //  gv.BindToPanel(d)
  //  window.Show()
  //  let g = grph.makeGraphs ((nodes,edges),subgraphs)

  //  gv.Graph <- g

  let visualize ((nodes,edges),subgraphs) =
    let gv = new Microsoft.Msagl.GraphViewerGdi.GViewer()
    let g = 
      if List.isEmpty subgraphs then
        grph.makeGraph(nodes,edges)
      else
        grph.makeGraphs ((nodes,edges),subgraphs)
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
  
  let showGraph expand f = ((computationGraphs expand) >> visualize) f
