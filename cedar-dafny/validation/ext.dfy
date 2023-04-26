include "../def/all.dfy"
include "ext/decimal.dfy"
include "ext/ipaddr.dfy"

module validation.ext {
  import opened def.base
  import opened types

  // Returns the map from extension function names to their types.
  function register(): map<Name, ExtFunType>
  {
    decimal.register() + ipaddr.register()
  }
}
