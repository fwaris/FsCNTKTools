
//TODO use Paket for reference management

open System
open System.IO

Environment.SetEnvironmentVariable("Path",
    Environment.GetEnvironmentVariable("Path") + ";" + __SOURCE_DIRECTORY__)

let pkgdir =  __SOURCE_DIRECTORY__ + @"..\..\packages"

let fullPath paths = Path.GetFullPath(Path.Combine(paths))

//change these for you installation (e.g. GPU vs CPU)
let dependencies = [
      @"CNTK.Deps.Cuda.2.4.0\support\x64\Dependency"
      @"CNTK.Deps.cuDNN.2.4.0\support\x64\Dependency"
      @"CNTK.Deps.MKL.2.4.0\support\x64\Dependency"
      @"CNTK.Deps.OpenCV.Zip.2.4.0\support\x64\Dependency"
      @"CNTK.Deps.OpenCV.Zip.2.4.0\support\x64\Dependency\Release"
      @"CNTK.GPU.2.4.0\support\x64\Release"
    ]

dependencies 
|> Seq.iter (fun dep -> 
    Environment.SetEnvironmentVariable("Path",
        fullPath [|pkgdir;dep|] + ";" + Environment.GetEnvironmentVariable("Path"))
    )    

#r @"..\packages\CNTK.GPU.2.4.0\lib\net45\x64\Cntk.Core.Managed-2.4.dll"

#r @"..\packages\Microsoft.Msagl.1.0.2\lib\net40\Microsoft.Msagl.dll"

#r @"..\packages\Microsoft.Msagl.Drawing.1.0.2\lib\net40\Microsoft.Msagl.Drawing.dll"

#r @"..\packages\Microsoft.Msagl.GraphViewerGDI.1.0.2\lib\net40\Microsoft.Msagl.GraphViewerGdi.dll"

#load "Graph.fs"