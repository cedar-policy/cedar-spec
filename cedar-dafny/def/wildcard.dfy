/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

include "std.dfy"
include "core.dfy"


// Defines the wildcard matching functions in a separate module because they
// don't depend on the Evaluator state, and we want to reuse them to reason
// about other components of Cedar (e.g., policy analysis).
module def.wildcard {

  import opened core
  import opened std

  import opened lib = core

  export
    provides lib, wildcardMatch

  predicate charMatch(textChar: char, patternChar: PatElem)
    requires patternChar.JustChar?
  {
    match patternChar {
      case JustChar(c) => textChar == c
    }
  }

  predicate wildcard(patternChar: PatElem) {
    patternChar.Star?
  }

  predicate wildcardMatch(text: string, pattern: Pattern) {
    if pattern == [] && text == [] then
      true
    else if pattern == [] then
      false
    else if text == [] then
      wildcard(pattern[0]) && wildcardMatch(text, pattern[1..])
    else if wildcard(pattern[0]) then
      wildcardMatch(text, pattern[1..]) ||
      wildcardMatch(text[1..], pattern)
    else
      charMatch(textChar := text[0], patternChar := pattern[0]) &&
      wildcardMatch(text[1..], pattern[1..])
  } by method {
    wildcardMatchEq(text, pattern);
    return wildcardMatchIdx(text, pattern, 0, 0);
  }

  predicate wildcardMatchIdx(text: string, pattern: Pattern, i: nat, j: nat)
    requires i <= |text| && j <= |pattern|
    decreases |text| - i
    decreases |pattern| - j
  {
    if j == |pattern| && i == |text| then
      true
    else if j == |pattern| then
      false
    else if i == |text| then
      wildcard(pattern[j]) && wildcardMatchIdx(text, pattern, i, j + 1)
    else if wildcard(pattern[j]) then
      wildcardMatchIdx(text, pattern, i, j + 1) ||
      wildcardMatchIdx(text, pattern, i + 1, j)
    else
      charMatch(textChar := text[i], patternChar := pattern[j]) &&
      wildcardMatchIdx(text, pattern, i + 1, j + 1)
  } by method {
    var cache: array2<std.Option<bool>>;
    cache := new std.Option<bool>[|text|+1, |pattern|+1]((_,_) => None);
    var r := wildcardMatchIdxMem(text, pattern, i, j, cache);
    return r;
  }

  lemma wildcardMatchEqIdx(text: string, pattern: Pattern, i: nat, j: nat)
    requires i <= |text| && j <= |pattern|
    ensures wildcardMatch(text[i..], pattern[j..]) == wildcardMatchIdx(text, pattern, i, j)
    decreases |text| - i
    decreases |pattern| - j
  {
  }

  lemma wildcardMatchEq(text: string, pattern: Pattern)
    ensures wildcardMatch(text, pattern) == wildcardMatchIdx(text, pattern, 0, 0) {
    wildcardMatchEqIdx(text, pattern, 0, 0);
  }

  method wildcardMatchIdxMem(text: string, pattern: Pattern, i: nat, j: nat, cache: array2<std.Option<bool>>) returns(r: bool)
    requires i <= |text| && j <= |pattern|;
    requires cache.Length0 == |text| + 1 && cache.Length1 == |pattern| + 1;
    requires forall p: nat, q: nat ::  p < cache.Length0 &&  q < cache.Length1 && cache[p, q].Some? ==> cache[p, q].value == wildcardMatchIdx(text, pattern, p, q);
    modifies cache;
    decreases |text| - i;
    decreases |pattern| - j;
    ensures r == wildcardMatchIdx(text, pattern, i, j);
    ensures cache[i, j] == Some(wildcardMatchIdx(text, pattern, i, j));
    ensures forall p: nat, q: nat ::  p < cache.Length0 &&  q < cache.Length1 && cache[p, q].Some? ==> cache[p, q].value == wildcardMatchIdx(text, pattern, p, q);
  {
    if cache[i, j].Some? {
      r := cache[i, j].value;
      return;
    }
    if j == |pattern| && i == |text| {
      r := true;
    }
    else if j == |pattern| {
      r := false;
    }
    else if i == |text| {
      if wildcard(pattern[j]) {
        r := wildcardMatchIdxMem(text, pattern, i, j + 1, cache);
      } else {
        r := false;
      }
    }
    else if wildcard(pattern[j]) {
      r := wildcardMatchIdxMem(text, pattern, i, j + 1, cache);
      if !r {
        r := wildcardMatchIdxMem(text, pattern, i + 1, j, cache);
      }
    }
    else {
      if charMatch(textChar := text[i], patternChar := pattern[j]) {
        r := wildcardMatchIdxMem(text, pattern, i + 1, j + 1, cache);
      } else {
        r := false;
      }
    }
    cache[i, j] := Some(r);
    return;
  }
}
