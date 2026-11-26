import Lean
import Lake.Build.Trace

open Lean Lean.Meta

private def hasClass (entry : InstanceEntry) (classes : List String) : Bool :=
  match entry.keys[0]? with
  | some (DiscrTree.Key.const name _) => classes.contains name.toString
  | _ => false

-- The native instance extension writes these entries to the public module data.
private unsafe def hasRegistration (data : ModuleData) (classes : List String) : Bool := Id.run do
  let some (_, records) := data.entries.find? (·.1 == instanceExtension.ext.name) | return false
  let entries : Array (ScopedEnvExtension.Entry InstanceEntry) := unsafeCast records
  return entries.any fun entry =>
    let instanceData : InstanceEntry := match entry with
      | .global e | .scoped _ e => e
    classes.isEmpty || hasClass instanceData classes

private unsafe def provides (path : System.FilePath) (classes : List String) : IO Bool := do
  let (data, region) ← readModuleData path
  let found := hasRegistration data classes
  region.free
  return found

/-- Read a TSV with the original module name, public object path and expected Lake object hash.
Print one module name per line. Optional class names restrict the selection. -/
unsafe def main (args : List String) : IO Unit := do
  let manifest :: classes := args | throw <| IO.userError "expected a manifest path and optional class names"
  let input ← IO.FS.Handle.mk manifest .read
  let mut selected := #[]
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let [name, path, hash] := line.trimAsciiEnd.toString.splitOn "\t"
      | throw <| IO.userError "expected a module name, path and hash"
    let path := System.FilePath.mk path
    unless (← Lake.computeBinFileHash path).toString == hash do
      throw <| IO.userError s!"public object hash mismatch for {name}"
    if ← provides path classes then selected := selected.push name
  for name in selected do IO.println name
