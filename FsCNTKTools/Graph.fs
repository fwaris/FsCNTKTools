namespace FSCNTK.Tools
open CNTK
open System
open System.Windows.Forms
type C = CNTK.CNTKLib

module Graph =

  type Vertex = Vf of Function | Vv of Variable
  type Edge = {From:string; To:string; Var:Variable}

  let toVertex (n:obj) = 
    match n with 
    | :? Function as f -> Vf f 
    | :? Variable as v -> Vv v 
    | _ -> failwith "unknown node"

  let uid = function Vf n -> n.Uid | Vv n ->n.Uid
  let name = function Vf n -> n.Name | Vv n->n.Name

  let isVisited id = Set.contains id

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

  let computationalGraph (f:Function) = 
    let (vx,es,vs) = traverse ([],Set.empty,Set.empty) f.RootFunction
    let es = Set.union es (f.Outputs |> Seq.map (fun v -> v.Owner.Uid,v.Uid) |> set)
    let varMap = vx |> List.choose (function Vv v -> Some v | _ -> None) |> List.map (fun v->v.Uid,v) |> Map.ofList
    let getVar (vfrm,vto) = match varMap |> Map.tryFind vfrm with Some v -> v | None -> match varMap |> Map.tryFind vto with Some v -> v | None -> failwith "one end should be a variable"
    let outputVarMap =vx |> List.choose (function Vv v -> (if v.IsOutput then Some v else None) | _ -> None)  |> List.map (fun v->v.Uid,v) |> Map.ofList
    let outEges = (Map.empty,es) ||> Seq.fold (fun m (f,t) -> 
      let v = match m |> Map.tryFind f with Some ls -> t::ls | None -> [t]
      m |> Map.add f v)
    let collapsedEdges,removeNodes = 
      (([],[]),es) 
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
    let vx' = vx |> List.filter (uid>>removeSet.Contains>>not)
    let es' = collapsedEdges 
    vx',es'


  module grph = 
    open Microsoft.Msagl.Drawing 
    let makeGraph(vertices,edges) =
      let g = new Microsoft.Msagl.Drawing.Graph()
      let drawingNodes = vertices |> List.map (uid>>g.AddNode) 
      drawingNodes 
      |> List.zip vertices 
      |> List.iter (fun (v,n)->
        let a = new NodeAttr()
        match v with 
        | Vv vr -> 
          n.Attr.FillColor <- Color.Azure
          if vr.IsInput then n.Attr.Shape <- Shape.Ellipse
          elif vr.IsOutput then n.Attr.Shape <- Shape.Ellipse; n.Attr.LineWidth <- 2.0
          elif vr.IsConstant then n.Attr.Shape <- Shape.Mdiamond
        | Vf fn -> n.Attr.FillColor <- Color.Bisque
      )
      (drawingNodes,vertices) ||> List.zip |> List.iter (fun (n,v) -> let l = name v in if l<>"" then n.LabelText <- name v)
      let drawingEdges = edges |> Seq.map(fun e -> let ed = g.AddEdge(e.From,e.To) in ed.UserData <- e.Var; ed) |> Seq.toList
      g
  
  let visualize (nodes,edges) =
    let gv = new Microsoft.Msagl.GraphViewerGdi.GViewer()
    gv.Graph <- grph.makeGraph(nodes,edges)
    let f = new System.Windows.Forms.Form()
    f.SuspendLayout()
    gv.Dock <- DockStyle.Fill
    f.Controls.Add(gv)
    f.ResumeLayout()
    f.Show()
  
  let showGraph : Function->unit = computationalGraph >> visualize