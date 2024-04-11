/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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


/-!
This file contains `simp` lemmas for proofs about code that uses the `do`
notation together with `Except` and `Option`.
-/


-- The `Except.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Except.bind_ok_T (a : α) (f : α → ExceptT ε Id β) :
  (bind (Except.ok a) f : ExceptT ε Id β) = f a
:= by rfl

@[simp] theorem Except.bind_ok (a : α) (f : α → Except ε β) :
  (bind (Except.ok a) f : Except ε β) = f a
:= by rfl

@[simp] theorem Except.bind_err (e : ε) (f : α → Except ε β) :
  (bind (Except.error e) f : Except ε β) = (Except.error e)
:= by rfl

-- The `Option.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Option.bind_some_T (a : α) (f : α → OptionT Id β) :
  (bind (Option.some a) f : OptionT Id β) = f a
:= by rfl

@[simp] theorem Option.bind_some_fun (a : α) (f : α → Option β) :
  (bind (Option.some a) f : Option β) = f a
:= by rfl

@[simp] theorem Option.bind_none_fun (f : α → Option β) :
  (bind Option.none f : Option β) = Option.none
:= by rfl
