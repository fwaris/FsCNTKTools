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

let (((vx,es),subgraphs) as graphs) = computationGraphs true model_t2

visualize graphs

let testMuch() =
  let fld = @"D:\repodata\fscntk"
  let mdlFls = System.IO.Directory.EnumerateFiles(fld,"*.bin") |> Seq.toArray
  for f in mdlFls do
    printfn "testing %s" f
    let model = Function.Load(f,device)
    let graphs =
      computationGraphs true model 
    visualize graphs
