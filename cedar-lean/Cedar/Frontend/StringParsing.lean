
/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module
public import Std.Internal.Parsec.String
public import Cedar.Spec.Policy

---- String parsing and conversion utilities ---

-- Parsing hex numbers `\xHH` and unicode codepoints `\u{...}` is done with the
-- functions `Char.asHexNat` and `String.asHexNat`. We prove that the latter roundtrips
-- with `Nat.toHexString` implemented here, for natural numbers ≤ 0xFFFFFF.


/-- Parses a character into a `Nat` number, assuming the character is the hex reprsentation of
that natural number. -/
@[expose] public def Char.asHexNat (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
    else .error s!"invalid hex digit: '{c}'"

/-- Parses a string into a `Nat` number, assuming the string is the hex representation of that
    natural number. -/
@[expose] public def String.asHexNat (s : String) : Except String Nat :=
  if s.isEmpty then .error "empty hex string"
  else if s.length > 6 then .error "hex string too long"
  else s.toList.foldl (fun acc c => do
    let n ← acc
    let d ← c.asHexNat
    .ok (n * 16 + d)) (.ok 0)

/-- Simple recursive hex digit list with explicit termination. -/
@[expose] public def Nat.toHexChars (n : Nat) : List Char :=
  if n == 0 then ['0'] else go n []
where
  go : Nat → List Char → List Char
    | 0, acc => acc
    | n + 1, acc =>
      let val := n + 1
      let d := val % 16
      let r := val / 16
      go r (Nat.digitChar d :: acc)
  termination_by n => n

@[expose] public def Nat.toHexString (n : Nat) : String :=
  String.ofList (Nat.toHexChars n)


--- Subparsers: parsing patterns and escaping strings  ---
namespace Cedar.Frontend.Cst

def toPatternAux (input : List Char) : Option Spec.Pattern :=
  match input with
  | [] => some []
  | '\\' :: '*'  :: cs => do let tail ← toPatternAux cs; some (.justChar '*' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← toPatternAux cs; some (.justChar '\\' :: tail)
  | '\\' :: 'n'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\x00' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← toPatternAux cs; some (.justChar '"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← toPatternAux cs; some (.justChar '\'' :: tail)
  | '\\' :: 'u'  :: '{' :: cs =>
    let digits := cs.takeWhile (· ≠ '}')
    let afterBrace := cs.drop digits.length
    match h : afterBrace with
    | '}' :: remaining => do
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← d.asHexNat.toOption
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      let tail ← toPatternAux remaining
      some (.justChar (Char.ofNat codepoint) :: tail)
    | _ => none
  | '\\' :: _ => none
  | '*' :: cs => do let tail ← toPatternAux cs; some (.star :: tail)
  | c :: cs => do let tail ← toPatternAux cs; some (.justChar c :: tail)
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  · have h1 : digits.length ≤ cs.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    have h2 : afterBrace.length = cs.length - digits.length := by
      simp [afterBrace, List.length_drop]
    have h3 : remaining.length + 1 = afterBrace.length := by
      simp [h]
    omega

/--
  `toPattern?` parse a string representing a Cedar pattern.
-/
public def toPattern? (s : String) : Option Spec.Pattern :=
  toPatternAux s.toList

def unescapeAux (input : List Char) : Option (List Char) :=
  match input with
  | [] => some []
  | '\\' :: 'n'  :: cs => do let tail ← unescapeAux cs; some ('\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← unescapeAux cs; some ('\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← unescapeAux cs; some ('\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← unescapeAux cs; some ('\x00' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← unescapeAux cs; some ('\\' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← unescapeAux cs; some ('"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← unescapeAux cs; some ('\'' :: tail)
  | '\\' :: 'u'  :: '{' :: cs =>
    let digits := cs.takeWhile (· ≠ '}')
    let afterBrace := cs.drop digits.length
    match h : afterBrace with
    | '}' :: remaining => do
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← d.asHexNat.toOption
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      let tail ← unescapeAux remaining
      some (Char.ofNat codepoint :: tail)
    | _ => none
  | '\\' :: _ => none
  | c :: cs => do
    let tail ← unescapeAux cs
    some (c :: tail)
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  · have h1 : digits.length ≤ cs.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    have h2 : afterBrace.length = cs.length - digits.length := by
      simp [afterBrace, List.length_drop]
    have h3 : remaining.length + 1 = afterBrace.length := by
      simp [h]
    omega

/-- `unescape?` un-escapces a string S.
-/
public def unescape? (s : String) : Option String := do
  let chars ← unescapeAux s.toList
  some (String.ofList chars)

end Cedar.Frontend.Cst
