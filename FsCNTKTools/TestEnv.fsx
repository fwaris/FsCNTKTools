#load "SetEnv.fsx"
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


//let testGraph() = Function.Load(test_model,device) |> FSCNTK.Tools.Graph.showGraph
let testGraph() = Function.Load(@"D:\repodata\fscntk\m_fs_untrained.bin",device) |> FSCNTK.Tools.Graph.showGraph
testGraph()