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

include "../../def/all.dfy"
include "../types.dfy"

module validation.ext.decimal {
  import opened def.std
  import opened def.base
  import opened def.core
  import opened def.ext.decimal.parseDecimal
  import opened types

  // Returns the map from Decimal extension function names to their types.
  function register(): map<Name, ExtFunType>
  {
    var D := Type.Extension(Name.fromStr("decimal"));
    map[
      Name.fromStr("decimal")             := ExtFunType([Type.String],D,Some(checkDecimalArgs)),
      Name.fromStr("lessThan")            := ExtFunType([D,D],Type.Bool(AnyBool),None),
      Name.fromStr("lessThanOrEqual")     := ExtFunType([D,D],Type.Bool(AnyBool),None),
      Name.fromStr("greaterThan")         := ExtFunType([D,D],Type.Bool(AnyBool),None),
      Name.fromStr("greaterThanOrEqual")  := ExtFunType([D,D],Type.Bool(AnyBool),None)
    ]
  }

  function checkDecimalArgs(args: seq<Expr>): types.Result<()>
  {
    if |args| != 1 then Ok(())
    else match args[0] {
           case PrimitiveLit(String(s)) =>
             match Parse(s) {
               case None => Err(ExtensionErr(Call(Name.fromStr("decimal"),args)))
               case Some(_) => Ok(())
             }
           case _ => Ok(())
         }
  }
}
