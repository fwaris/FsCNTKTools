#load "SetEnv.fsx"

open CNTK
open FsCNTK.Tools

type C = CNTK.CNTKLib

let test_model = __SOURCE_DIRECTORY__ + "/test_model.bin"
//let t2 = @"D:\repodata\fscntk\m_fs_untrained.bin"
let t2 = @"D:\repodata\fscntk\l_fs_l.bin"

let device = DeviceDescriptor.GPUDevice(0)

let model = Function.Load(test_model,device)
let model_t2 = Function.Load(t2,device)
FsCNTK.Tools.ModelViz.showGraph AllBlocks model_t2

let testMuch() =
  let fld = @"D:\repodata\fscntk"
  let mdlFls = System.IO.Directory.EnumerateFiles(fld,"*.bin") |> Seq.toArray
  for f in mdlFls do
    printfn "testing %s" f
    let model = Function.Load(f,device)
    let graphs =
      ModelGraph.computationGraphs FsCNTK.Tools.AllBlocks model 
    ModelViz.visualize graphs
