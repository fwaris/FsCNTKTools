#load "FsCNTKTools_SetEnv.fsx"
//script to test that environment is set up correctly

open CNTK
type C = CNTK.CNTKLib

let test_model = __SOURCE_DIRECTORY__ + "/test_model.bin"

let device = DeviceDescriptor.GPUDevice(0)

let testViewer()=
  let g = new Microsoft.Msagl.GraphViewerGdi.GViewer()
  let f = new System.Windows.Forms.Form()
  f.Controls.Add(g)
  f.Show()
  // testViewer()


let testModelLoad() =
  Function.Load(test_model,device)
  // testModelLoad()

open FsCNTK.Tools

//list the blocks in the function for possible expansion
//note the uids are assigned when model is loaded
let blocks() = Function.Load(test_model,device) |> ModelGraph.blocks 

let model = Function.Load(test_model,device)
ModelGraph.blocks model

let showGraph_NoExpansion() = model |> ModelViz.showGraph NoExpansion
let showGraph_ExpandAll()   = model |> ModelViz.showGraph AllBlocks
let showGraph_ExpandSome()  = model |> ModelViz.showGraph (Blocks ["LSTM"])