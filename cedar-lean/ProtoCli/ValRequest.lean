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
import Protobuf.Message

import CedarProto.AuthorizationRequest
import CedarProto.ValidationRequest
import DiffTest

open Proto

@[inline]
def bufsize : USize := 2000000 * 1024

@[inline]
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
   let fileExists ← filename.pathExists
   if not fileExists then
     let stderr ← IO.getStderr
     stderr.putStrLn s!"File not found: {filename}"
     pure none
   else
     let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
     pure (some (IO.FS.Stream.ofHandle handle))

@[inline]
def readFileBytes (filename: String) : IO ByteArray := do
  let stream ← fileStream filename
  match stream with
  | none =>
    let stderr ← IO.getStderr
    stderr.putStrLn s!"No bytes found"
    pure (ByteArray.mk #[])
  | some stream =>
    stream.read bufsize

@[inline]
def processJson (result_str: String): IO Cedar.Validation.Proto.ValidationRequest := do
  match Lean.Json.parse result_str with
    | .error _ =>
      println! s!"Failed to parse JSON input"
      pure default
    | .ok json => do
      let schema := DiffTest.getJsonField json "schema" >>= DiffTest.jsonToSchema
      let policies := DiffTest.getJsonField json "policies" >>= DiffTest.jsonToPolicies
      match schema, policies with
        | (.ok schema), (.ok policies)  =>
          println! s!"JSON parse successful"
          pure (Cedar.Validation.Proto.ValidationRequest.mk schema policies)
        | _, _ =>
          println! "Failed to create Validation Request Message"
          pure default

@[inline]
def processProto (result_bytes: ByteArray): IO Cedar.Validation.Proto.ValidationRequest := do
  let result: Except String Cedar.Validation.Proto.ValidationRequest := Message.interpret? result_bytes
  match result with
    | .error e =>
      println! "Protobuf failed to parse {e}"
      pure default
    | .ok x =>
      println! "Protobuf parse successful"
      pure x

structure Timed (α : Type) where
  data : α
  duration : Nat
deriving Lean.ToJson

def runAndTime (f : IO α) : IO (Timed α) := do
  let start ← IO.monoNanosNow
  let result ← f
  let stop ← IO.monoNanosNow
  .ok {
    data := result,
    duration := stop - start
  }

def main (args: List String) : IO UInt32 := do
  if args.length != 2 then panic! "Usage ./Protobuf [Proto File] [JSON File]"

  let proto_bytes ← readFileBytes (args.get! 0)
  let proto_sec ← runAndTime (processProto proto_bytes)
  println! s!"ProtoTime: {proto_sec.duration}"

  let json_str ← IO.FS.readFile (args.get! 1)
  let json_sec ←  runAndTime (processJson json_str)
  println! s!"JSONTime:  {json_sec.duration}"

  -- Cedar.Spec.Policies is a list that has no guarentee on it's ordering
  -- for comparison, we need to sort first
  -- let p1 := List.canonicalize (fun p: Cedar.Spec.Policy => p.id) proto_sec.data.policies
  -- let p2 := List.canonicalize (fun p: Cedar.Spec.Policy => p.id) json_sec.data.policies

  -- let x1: Cedar.Spec.AuthorizationRequest := {proto_sec.data with
    -- policies := p1
  -- }
  -- let x2: Cedar.Spec.AuthorizationRequest := {json_sec.data with
    -- policies := p2
  -- }

  let x1 := proto_sec.data
  let x2 := json_sec.data

  println! s!"Representations equal? {decide (x1 = x2)}"

  -- println! s!"{repr x1}"
  -- println! s!"{repr x2}"

  pure 0
