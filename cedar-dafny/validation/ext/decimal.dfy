include "../../def/all.dfy"
include "../types.dfy"

module validation.ext.decimal {
  import opened def.std
  import opened def.base
  import opened def.core
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
             match ext.decimal.parseDecimal.Parse(s) {
               case None => Err(ExtensionErr(Call(Name.fromStr("decimal"),args)))
               case Some(_) => Ok(())
             }
           case _ => Ok(())
         }
  }
}
