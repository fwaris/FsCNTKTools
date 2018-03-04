#load "SetEnv.fsx"

open CNTK
open System
open System.Windows.Forms

type C = CNTK.CNTKLib

let test_model = __SOURCE_DIRECTORY__ + "/test_model.bin"

let device = DeviceDescriptor.GPUDevice(0)

let model = Function.Load(test_model,device)

type Vertex = Vf of Function | Vv of Variable

type Edge = string*string //from->to

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
  let outputs = vx |> List.choose (function Vv v -> (if v.IsOutput then Some v else None) | _ -> None) 
  let outM = outputs |> List.map (fun v->v.Uid,v) |> Map.ofList
  let outEges = (Map.empty,es) ||> Seq.fold (fun m (f,t) -> 
    let v = match m |> Map.tryFind f with Some ls -> t::ls | None -> [t]
    m |> Map.add f v)
  let collapsedEdges,removeNodes,keepNodes = 
    (([],[],[]),es) 
    ||> Seq.fold (fun (edges,rems,keeps) (vfrm,vto) -> 
        match outM |> Map.tryFind vto with 
        | Some v ->
            let toNodes = match outEges |> Map.tryFind v.Uid with Some ls -> ls | None -> []
            if List.isEmpty toNodes then
              ((vfrm,vto)::edges,rems,keeps)
            else
              let newEdges = toNodes |> List.map (fun n -> vfrm,n)
              (newEdges @ edges, v.Uid::rems,keeps)
        | None ->
          match outM |> Map.tryFind vfrm with
          | Some v -> 
            let toNodes = match outEges |> Map.tryFind v.Uid with Some ls -> ls | None -> []
            if List.isEmpty toNodes then
              (edges,rems,v.Uid::keeps)
            else
              (edges,rems,keeps)
          | None ->  [vfrm,vto] @ edges, rems, keeps)
  let removeSet = set removeNodes
  let keepSet = set keepNodes
  let removeSet = Set.difference removeSet keepSet
  let vx' = vx |> List.filter (uid>>removeSet.Contains>>not)
  let es' = collapsedEdges
  vx',es'

let (vx,es) = computationalGraph model

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
      | Vv _ -> n.Attr.FillColor <- Color.Azure
      | Vf _ -> n.Attr.FillColor <- Color.Bisque
    )
    (drawingNodes,vertices) ||> List.zip |> List.iter (fun (n,v) -> let l = name v in if l<>"" then n.LabelText <- name v)
    let drawingEdges = edges |> Seq.map(fun (vfrm,vto) -> g.AddEdge(vfrm,vto)) |> Seq.toList
    g
  
let gv = new Microsoft.Msagl.GraphViewerGdi.GViewer()
gv.Graph <- grph.makeGraph(vx,es)
let f = new System.Windows.Forms.Form()
f.SuspendLayout()
gv.Dock <- DockStyle.Fill
f.Controls.Add(gv)
f.ResumeLayout()
f.Show()
