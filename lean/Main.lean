/-
  CLI wrapper for the Lean port. IDENTICAL contract to ./oracle/wrapper.c (SPEC S0):

    stdin  : arbitrary bytes
    stdout : on success, the serialization of the parsed value; no trailing newline
    exit 0 : parse succeeded
    exit 1 : parse failed

  Exit 2 (serialize failure) cannot occur here: `serialize` is a total function, so the
  oracle's "printing failed" path has no counterpart. That asymmetry is itself a result.
-/
import Cjson

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let input ← stdin.readBinToEnd
  match Cjson.parseDoc input.toList with
  | none => return 1
  | some v =>
    stdout.write (ByteArray.mk (Cjson.serialize v).toArray)
    stdout.flush
    return 0
