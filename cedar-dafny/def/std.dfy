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

// ----------------- std.dfy ----------------- //
// The "std" module holds generic code that we're adopting from the Dafny
// standard library.

module def.std {

  datatype Option<+T> = Some(value: T) | None {
    predicate IsFailure() {
      None?
    }

    function PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    function Extract(): T
      requires Some? {
      value
    }

    function UnwrapOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }
  }

  datatype Result<+T, +E> = Ok(value: T) | Err(error: E) {
    predicate IsFailure() {
      Err?
    }

    function PropagateFailure<U>(): Result<U, E>
      requires Err?
    {
      Err(error)
    }

    function Extract(): T
      requires Ok?
    {
      value
    }

    function Map<U>(f: T -> U): Result<U, E>
    {
      if Ok? then Ok(f(value)) else PropagateFailure()
    }

    function MapErr<F>(f: E -> F): Result<T, F>
    {
      if Ok? then Ok(value) else Err(f(error))
    }
  }

  datatype Either<+L, +R> = Left(left: L) | Right(right: R)
}
