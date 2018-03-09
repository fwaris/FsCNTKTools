namespace FSCNTK.Tools
open CNTK
open System
type C = CNTK.CNTKLib

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

  let uid = function Vf n -> n.Uid | Vv n ->n.Uid
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

  //create the computational graph for a single function
  let functionGraph (f:Function) = 
    let (vx,es,vs) = traverse ([],Set.empty,Set.empty) f.RootFunction
    let es = Set.union es (f.Outputs |> Seq.map (fun v -> v.Owner.Uid,v.Uid) |> set)
    collapseVarEdges (vx,es)

  //create root computational graph and optionally subgraphs nested one level down
  let computationGraphs expand (fn:Function) =
    let (vx,es) = functionGraph fn
    let subgraphs = 
      if expand then 
        vx |> List.choose (function 
        | Vf fn when fn.IsBlock -> fn.BlockRoot() |> functionGraph |> toSubG fn.Uid |> Some
        | _ -> None)
      else []
    (vx,es),subgraphs

  
  //module supporting graph visualization
  module grph = 
    open Microsoft.Msagl.Drawing 
    
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
      let blockVxs = allVxs |> List.filter (uid>>sgIds.Contains)
      let baseVxs = allVxs |> List.filter (uid>>sgIds.Contains>>not)
      let root = new Subgraph("root")
      let subGraphs = blockVxs |> List.map (fun v -> uid v, new Subgraph("sg_" + uid v, UserData=v, LabelText=nodeLabel v))
      let sgMap = subGraphs |>  Map.ofList
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

      let rootNodes = vertices |> List.filter (uid >> subgraphNodeIds.Contains >> not) |> List.choose (uid >> nodeMap.TryFind) //any node not in subgraph is in root subgraph

      g.RootSubgraph <- root
      nodes |> List.iter g.AddNode
      subGraphs |> List.iter (snd >> root.AddSubgraph )
      rootNodes |> List.iter root.AddNode
      subgraphNodes |> Map.iter (fun sgId vxIds -> sgMap.TryFind(sgId) |> Option.iter(fun sgNode -> vxIds |> List.iter (nodeMap.TryFind>>(Option.iter sgNode.AddNode)))) 
      
      let es = edges @ (List.collect (fun sg->sg.Edges) subgraphs)
      let allNodeMaps =[sgMap |> Map.map(fun k v->v:>Node) ;nodeMap]
      es 
      |> List.filter (fun e->(sgMap.ContainsKey e.From || sgMap.ContainsKey e.To) |> not)
      |> List.iter (fun e->g.AddEdge(e.From,edgeLabel e.Var,e.To) |> ignore)
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
    let g = grph.makeGraphs ((nodes,edges),subgraphs)
   // g.Edges |> Seq.iter (fun e->  e.Label.FontSize <- 8.0)
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
