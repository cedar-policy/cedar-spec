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
