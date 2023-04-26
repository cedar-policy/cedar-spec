include "../../def/all.dfy"
include "../types.dfy"

module validation.ext.ipaddr {
  import opened def.std
  import opened def.base
  import opened def.core
  import opened types

  // Returns the map from IPAddr extension function names to their types.
  function register(): map<Name, ExtFunType>
  {
    var I := Type.Extension(Name.fromStr("ipaddr"));
    map[
      Name.fromStr("ip")          := ExtFunType([Type.String],I,Some(checkIpArgs)),
      Name.fromStr("isIpv4")      := ExtFunType([I],Type.Bool(AnyBool),None),
      Name.fromStr("isIpv6")      := ExtFunType([I],Type.Bool(AnyBool),None),
      Name.fromStr("isLoopback")  := ExtFunType([I],Type.Bool(AnyBool),None),
      Name.fromStr("isMulticast") := ExtFunType([I],Type.Bool(AnyBool),None),
      Name.fromStr("isInRange")   := ExtFunType([I,I],Type.Bool(AnyBool),None)
    ]
  }

  function checkIpArgs(args: seq<Expr>): types.Result<()>
  {
    if |args| != 1 then Ok(())
    else match args[0] {
           case PrimitiveLit(String(s)) =>
             match ext.ipaddr.parseIPAddr.parse(s) {
               case None => Err(ExtensionErr(Call(Name.fromStr("ip"),args)))
               case Some(_) => Ok(())
             }
           case _ => Ok(())
         }
  }
}
