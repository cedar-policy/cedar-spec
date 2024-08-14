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

import CedarProto.Request
import CedarProto.Entities
import CedarProto.LiteralPolicySet
import CedarProto.AuthorizationRequest
import DiffTest

open Proto

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


def processJson (filename: String): IO Cedar.Spec.AuthorizationRequest := do
  let result_str ← IO.FS.readFile filename

  match Lean.Json.parse result_str with
    | .error _ =>
      println! s!"Failed to parse JSON input"
      pure default
    | .ok json => do
      let request := DiffTest.getJsonField json "request" >>= DiffTest.jsonToRequest
      let entities := DiffTest.getJsonField json "entities" >>= DiffTest.jsonToEntities
      let policies := DiffTest.getJsonField json "policies" >>= DiffTest.jsonToPolicies
      match request, entities, policies with
        | (.ok request), (.ok entities), (.ok policies)  =>
          println! s!"JSON parse successful"
          pure (Cedar.Spec.AuthorizationRequest.mk request entities policies)
        | _, _, _ =>
          println! "Failed to create Authorization Request Message"
          pure default

def processProto (filename: String): IO Cedar.Spec.AuthorizationRequest := do
  let result_bytes ← readFileBytes filename
  let result: Except String Cedar.Spec.AuthorizationRequest := Message.interpret? result_bytes
  match result with
    | .error e =>
      println! "Protobuf failed to parse {e}"
      pure default
    | .ok x =>
      println! "Protobuf parse successful"
      pure (x)

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

  let proto_sec ← runAndTime (processProto (args.get! 0))
  println! s!"ProtoTime: {proto_sec.duration}"

  let json_sec ←  runAndTime (processJson (args.get! 1))
  println! s!"JSONTime:  {json_sec.duration}"

  -- Cedar.Spec.Policies is a list that has no guarentee on it's ordering
  -- for comparison, we need to sort first
  let p1 := List.canonicalize (fun p: Cedar.Spec.Policy => p.id) proto_sec.data.policies
  let p2 := List.canonicalize (fun p: Cedar.Spec.Policy => p.id) json_sec.data.policies

  let x1: Cedar.Spec.AuthorizationRequest := {proto_sec.data with
    policies := p1
  }
  let x2: Cedar.Spec.AuthorizationRequest := {json_sec.data with
    policies := p2
  }

  println! s!"Representations equal? {decide (x1 = x2)}"

  -- println! s!"{repr x}"
  -- println! s!"{repr y}"

  pure 0
