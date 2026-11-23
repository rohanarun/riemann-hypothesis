/- Stock Lake API client for one explicitly leased, dependency-ready proof batch. -/
module
import all Lake
import Lake.DSL -- Registers the same DSL builtins as stock LakeMain.
import all Lake.CLI.Main
import all Lake.Build.Run
import all Lake.Build.Index
import all Lake.Load.Workspace
open Lean Lake System

public def main (args : List String) : IO UInt32 := do
  let [request, output] := args | throw <| IO.userError "expected request and result paths"
  let .ok req := Json.parse (← IO.FS.readFile request) | throw <| IO.userError "invalid request"
  let .ok names := req.getObjValAs? (Array String) "modules" | throw <| IO.userError "missing modules"
  if names.isEmpty || names.size > 4096 then throw <| IO.userError "empty or oversized proof lease"
  initSearchPath (← findSysroot)
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := {elanInstall?, leanInstall?, lakeInstall?, rootDir := ".", updateToolchain := false}
  let cfg ← opts.mkLoadConfig.toIO fun e => IO.userError e.toString
  let some ws ← (loadWorkspace cfg).toBaseIO | throw <| IO.userError "workspace load failed"
  -- Checking the requested modules' imported artifacts under noBuild prevents
  -- a missing or stale dependency from expanding this lease into a larger build.
  let preflight : FetchM Unit := do
    for name in names do
      let some mod := ws.findModule? name.toName | error s!"unknown module {name}"
      discard <| (← mod.presetup.fetch).await
  discard <| ws.runFetchM preflight {noBuild := true, trustHash := false, verbosity := .quiet}
  let config : BuildConfig := {trustHash := false, verbosity := .quiet, outLv := .error}
  let jobs ← mkJobQueue
  let mctx ← mkMonitorContext config jobs
  let bctx ← mkBuildContext ws config jobs
  let store ← BuildStoreRef.new
  let requested ← IO.mkRef (#[] : Array OpaqueJob)
  let specs ← (parseTargetSpecs ws (names.toList.map ("+" ++ ·))).toIO fun e => IO.userError e.toString
  let build : FetchM (Job Unit) := do
    let work ← specs.mapM (·.build)
    requested.set work
    return Job.mixArray work
  let compute := Job.async build
  let job ← (compute.run none {} store bctx).run nilTrace
  let result ← monitorBuild mctx job
  let work ← requested.get
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let good := if let some j := work[i]? then
      match j.task.get with | .ok .. => true | .error .. => false
    else false
    rows := rows.push <| Json.mkObj [("module",toJson names[i]!), ("ok",toJson good),
      ("action",toJson ("stock-Lake-proof-build" : String))]
  let value := Json.mkObj [("ok",toJson result.isOk), ("modules",toJson rows),
    ("operation",toJson ("native-proof" : String)), ("dependency_preflight",toJson true)]
  IO.FS.writeFile output (value.compress ++ "\n")
  return 0
