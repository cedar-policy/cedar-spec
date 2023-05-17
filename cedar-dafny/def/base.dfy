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

module def.base {
  import opened std

  // ----- Identifiers and names ----- //

  // Identifier for use in record fields, etc.
  datatype Id = Id(id: string)

  // Name, which is an identifier along with optional namespaces.
  // Valid names include `foo` (which has no namespace), `foo::bar`,
  // `foo::bar::baz`, etc.
  datatype Name = Name(id: Id, path: seq<Id>) {
    static function fromId(id: Id): Name {
      Name(id, [])
    }

    static function fromStr(str: string): Name {
      Name.fromId(Id(str))
    }
  }

  // ----- Errors and Cedar-specific result type ----- //

  // There are four kinds of error values related to extension types:
  // CallStyleError, ArityMismatchError, NoSuchFunctionError, and
  // ExtensionError.  The first three can be detected statically, through
  // validation. The fourth is the abstract, catch-all error that represents all
  // runtime errors thrown by extension functions, which cannot be prevented
  // statically (e.g., string input parsing errors).
  //
  // ArithmeticOverflowError is never raised by the main engine but may be
  // raised by engine_with_overflow. We generally avoid modifying code used by
  // the main engine for the sake of the engine_with_overflow, but adding
  // ArithmeticOverflowError here will save us the trouble of managing two
  // different Error types (and Result, etc.) and didn't break any existing code
  // in Matt's test.
  datatype Error =
    EntityDoesNotExist |
    AttrDoesNotExist |
    TypeError |
    ArithmeticOverflowError |
    ArityMismatchError |
    NoSuchFunctionError |
    ExtensionError

  // Customization of the standard Result type for concrete evaluation: the
  // error type is fixed to Error in Result<T>, and the value type is fixed to the
  // unit type in UnitResult. We also introduce convenience functions Ok and Err
  // that let us construct Result<T> values without having to qualify the names.
  type Result<T> = std.Result<T, Error>
  type UnitResult = Result<()>

  function Ok<T>(v: T): Result<T> {
    Result.Ok(v)
  }

  function Err<T>(v: Error): Result<T> {
    Result.Err(v)
  }

  // ----- Generic type coercions ----- //

  // A generic way to coerce a base type to a wrapper type and back.
  datatype Coerce<!Base(!new,==), !Wrapper(!new,==)> =
    Coerce(
      wrap: Base -> Wrapper,
      unwrap: Wrapper -> Result<Base>)
  {
    ghost predicate wellFormed() {
      (forall b: Base ::
         unwrap(wrap(b)) == Ok(b)) &&
      (forall w: Wrapper | unwrap(w).Ok? ::
         wrap(unwrap(w).Extract()) == w) &&
      (forall w: Wrapper | unwrap(w).Err? ::
         forall b: Base :: wrap(b) != w)
    }

    static function compose<T(!new,==)>(c: Coerce<T, Base>, c': Coerce<Base, Wrapper>): (res: Coerce<T, Wrapper>)
      ensures (c.wellFormed() && c'.wellFormed()) ==> res.wellFormed()
    {
      var wrap := (t: T) => c'.wrap(c.wrap(t));
      var unwrap :=
        (w: Wrapper) =>
          var b :- c'.unwrap(w);
          c.unwrap(b);

      Coerce(wrap, unwrap)
    }
  }
}
