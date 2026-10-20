/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import Lean

/-! Runtime coverage of the existing production read-only CFG checker. This
report is diagnostic data. It never claims an end-to-end certificate. -/
open EDSL X86 Sequential Lean

private def probeOne (directory : System.FilePath) (symbol : String) : IO Json := do
  let data ← IO.FS.readBinFile (directory / (symbol ++ ".bin"))
  let bytes := data.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let result := CFG.analyze bytes
  let (status, obligation, nodes) := match result with
    | .ok graph => ("cfg-accepted", "independent contract, loaded final-ELF binding, ABI/memory/OS obligations and kernel proof remain", graph.nodes.length)
    | .error error => ("unsupported", reprStr error, 0)
  return Json.mkObj [
    ("symbol", toJson symbol), ("bytes", toJson data.size),
    ("cfg_status", toJson status), ("first_obligation", toJson obligation),
    ("cfg_nodes", toJson nodes), ("end_to_end_certified", toJson false)]

def main (arguments : List String) : IO UInt32 := do
  let [specification, directory, output] := arguments | do
    (← IO.getStderr).putStrLn "usage: lake env lean --run corpus/Probe.lean SPECIFICATIONS.tsv EXTRACTED_DIR OUTPUT.json"
    return 2
  try
    let text ← IO.FS.readFile specification
    let mut entries := #[]
    let mut names : Array String := #[]
    for row in text.splitOn "\n" do
      if row.isEmpty || row.startsWith "#" then continue
      let fields := row.splitOn "\t"
      if fields.length != 5 then throw (IO.userError "malformed specification row")
      let number := entries.size + 1
      let id := if number < 10 then "0" ++ toString number else toString number
      if fields[0]! != id || names.contains fields[1]! then
        throw (IO.userError "unordered definition IDs or duplicate function symbol")
      for field in fields do
        if !(field.toList.any fun character => !character.isWhitespace) then
          throw (IO.userError "empty specification field")
      names := names.push fields[1]!
      entries := entries.push (← probeOne directory fields[1]!)
    if entries.size != 40 then throw (IO.userError "v1 requires 40 distinct function rows")
    let accepted := entries.filter fun entry =>
      (entry.getObjValAs? String "cfg_status").toOption == some "cfg-accepted"
    let report := Json.mkObj [
      ("schema", toJson ("edsl.compiler-corpus.cfg-probe.v1" : String)),
      ("profile", toJson ("production read-only CFG; 64 bytes / 32 static instructions" : String)),
      ("artifacts_probed", toJson entries.size),
      ("cfg_accepted", toJson accepted.size),
      ("certified_end_to_end", toJson (0 : Nat)),
      ("functions", Json.arr entries)]
    IO.FS.writeFile output (report.pretty ++ "\n")
    (← IO.getStdout).putStrLn s!"CFG-PROBED {entries.size}; CFG-ACCEPTED {accepted.size}; CERTIFIED 0"
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"CORPUS-PROBE-FAILED: {error}; no program-defect conclusion"
    return 1
