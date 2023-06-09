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

include "base.dfy"
include "ext/fun.dfy"
include "ext/decimal.dfy"
include "ext/ipaddr.dfy"

module def.ext {
  import opened base
  import opened fun
  import dec = decimal
  import ip = ipaddr

  datatype Value =
    Decimal(d: dec.Decimal) |
    IPAddr(ip: ip.IPAddr)
  {
    static function asDecimal(v: Value): Result<dec.Decimal> {
      if v.Decimal? then Ok(v.d) else Err(TypeError)
    }

    static function asIPAddr(v: Value): Result<ip.IPAddr> {
      if v.IPAddr? then Ok(v.ip) else Err(TypeError)
    }

  }

  // Returns the map from extension function names to their implementations.
  // Note that we're currently assuming that function names are unique.
  // This might have to be revisited in the future if we allow different
  // extension types to contain functions with the same name.  In that case,
  // we'll want to specify dispatching mechanisms for function and method-style
  // invocations.
  function register<T(!new,==)>(coerce: Coercions<Value, T>): map<Name, ExtFun<T>>
  {
    var dec2val := Coerce((d: dec.Decimal) => Value.Decimal(d), Value.asDecimal);
    var ip2val  := Coerce((ip: ip.IPAddr) => Value.IPAddr(ip), Value.asIPAddr);

    dec.DecimalFunctions.register(Coercions.compose(dec2val, coerce)) +
    ip.IPAddrFunctions.register(Coercions.compose(ip2val, coerce))
  }

}
