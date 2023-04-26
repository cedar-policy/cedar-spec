include "../def/ext/ipaddr.dfy"

module test.ipaddr {
  import opened def.ext.ipaddr.parseIPAddr

  method parseValidStr() {
    var validStr :=
      [
        "127.0.0.1",
        "::",
        "::/5",
        "F:AE::F:5:F:F:0" // :: represents just one group of zeros
      ];
    var i := |validStr| - 1;
    while 0 <= i
    {
      expect parse(validStr[i]).Some?;
      i := i - 1;
    }
  }

  method parseInvalidStr() {
    var invalidStr :=
      [
        "127.0.0.1.", // one more dot
        "::::", // too many double colons
        "F:AE::F:5:F:F:0:0", // too many groups
        "F:A:F:5:F:F:0:0:1", // too many groups
        "F:A" // too few groups
      ];
    var i := |invalidStr| - 1;
    while 0 <= i {
      expect parse(invalidStr[i]).None?;
      i := i - 1;
    }
  }

  method loopback() {
    var ipv4 := parse("127.0.0.1");
    expect ipv4.Some?;
    expect ipv4.value.isLoopback();
    var ipv6 := parse("::B");
    expect ipv6.Some?;
    expect !ipv6.value.isLoopback();

    var ipv6_loopback := parse("::1");
    expect ipv6_loopback.Some?;
    expect ipv6_loopback.value.isLoopback();

    //Currently don't support parsing IPv4 embedded in IPv6
    var ipv4_embeded_in_ipv6 := parse("::ffff:127.0.0.1");
    expect ipv4_embeded_in_ipv6.None?;

    //As in Rust, IPv4 embedded in IPv6 only uses IPv6 loopback
    var hex_ipv4_embeded_in_ipv6 := parse("::ffff:ff00:0001");
    expect hex_ipv4_embeded_in_ipv6.Some?;
    expect !hex_ipv4_embeded_in_ipv6.value.isLoopback();
  }

  method getAddrValue() {
    var ipv4 := parse("192.0.2.235");
    expect ipv4.Some?;
    expect ipv4.value.getAddrValue() == 3221226219;
    var ipv6 := parse("::1:2");
    expect ipv6.Some?;
    expect ipv6.value.getAddrValue() == 0x1_0000 + 0x2;
  }

  method normalization() {
    var ipv4 := parse("127.0.0.1/16");
    expect ipv4.Some?;
    var ipv4' := parse("127.0.255.255/16");
    expect ipv4'.Some?;
    expect ipv4.value.normalize() == ipv4'.value.normalize();
    var ipv4'' := parse("255.255.255.255/0");
    expect ipv4''.Some?;
    expect ipv4''.value.normalize().getAddrValue() == 0;

    var ipv6 := parse("::1/112");
    expect ipv6.Some?;
    var ipv6' := parse("::2/112");
    expect ipv6'.Some?;
    expect ipv6.value.normalize() == ipv6'.value.normalize();
    var ipv6'' := parse("::1:2/0");
    expect ipv6''.Some?;
    expect ipv6''.value.normalize().getAddrValue() == 0;
  }

  method testInRange() {
    var ip1 := parse("238.238.238.238");
    expect ip1.Some?;
    var ip2 := parse("238.238.238.41/12");
    expect ip2.Some?;
    print ip1.value, "\n";
    print ip1.value.normalize();
    expect ip1.value.normalize().inRange(ip2.value.normalize());
  }

  method {:test} test() {
    parseValidStr();
    parseInvalidStr();
    loopback();
    getAddrValue();
    normalization();
    testInRange();
  }
}
