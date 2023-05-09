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

include "../def/ext/decimal.dfy"

module test.decimal {
  import opened def.ext.decimal.parseDecimal
  method ParseValidStr() {
    var validStr := ["-12.34", "1.2345"];
    var i := |validStr| - 1;
    while 0 <= i
    {
      expect Parse(validStr[i]).Some?;
      i := i - 1;
    }
  }

  method ParseInvalidStr() {
    var invalidStr :=
      [
        "-12", // no decimal point
        "1.23456", // too many fractional digits
        "922337203685477.5808", // overflow
        "-922337203685477.5809" // underflow
      ];
    var i := |invalidStr| - 1;
    while 0 <= i {
      expect Parse(invalidStr[i]).None?;
      i := i - 1;
    }
  }

  method {:test} Test() {
    ParseValidStr();
    ParseInvalidStr();
  }
}
