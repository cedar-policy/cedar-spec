import Lean.Data.HashMap
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser
import Lean.Data.Json.Basic

import Protobuf.Util
import Protobuf.ByteArray
import Protobuf.BParsec
import Protobuf.Varint
import Protobuf.Types
import Protobuf.Structures
import Protobuf.Packed
import Protobuf.HardCodeTest2
open Proto

-- #check String.Iterator
-- #check Lean.Parsec
-- #check Lean.Json

-- TODO: Zig-zag signed integers

-- TODO: Floats

-- TODO: Doubles

-- TODO: Maps


def bufsize : USize := 2000000 * 1024

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
   let fileExists ← filename.pathExists
   if not fileExists then
     let stderr ← IO.getStderr
     stderr.putStrLn s!"File not found: {filename}"
     pure none
   else
     let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
     pure (some (IO.FS.Stream.ofHandle handle))


def readFileBytes (filename: String) : IO ByteArray := do
  let stream ← fileStream filename
  match stream with
  | none =>
    let stderr ← IO.getStderr
    stderr.putStrLn s!"No bytes found"
    pure (ByteArray.mk #[])
  | some stream =>
    stream.read bufsize


def processJson (filename: String): IO Bool := do
  let result_str ← IO.FS.readFile filename
  match parse_hardcode2_json result_str with
    | .error _ => pure false
    | .ok _ => pure true

def processProto (filename: String): IO String := do
  let result_bytes ← readFileBytes filename
  match parse_hardcode2 result_bytes.iter with
    | .error e => pure e
    | .ok h => pure s!"Successfully parsed {h.a.size} elements, 0: {h.a.get! 0}, 1: {h.a.get! 1}"

structure Timed (α : Type) where
  data : α
  duration : Nat
deriving Lean.ToJson

def runAndTime (f : Unit -> α) : BaseIO (Timed α) := do
  let start ← IO.monoNanosNow
  let result := f ()
  let stop ← IO.monoNanosNow
  .ok {
    data := result,
    duration := stop - start
  }

def main (args: List String) : IO UInt32 := do
  if args.length != 2 then panic! "Usage ./Protobuf [Proto File] [JSON File]"


  let proto_sec ← runAndTime (processProto (args.get! 0))
  println! proto_sec.data
  println! proto_sec.duration


  let json_sec ←  runAndTime (processJson (args.get! 1))
  println! json_sec.data
  println! json_sec.duration

  pure 0
