include "../def/all.dfy"

module basic {
  import opened def.base
  import opened def.core
  import opened def.engine

  lemma DefaultDeny(query: Query, store: Store)
    requires // If the policy set is empty, then
      |store.policies.policies| == 0
    ensures // every request is denied.
      Authorizer(query, store).isAuthorized().decision == Deny
  { }

  lemma ImplicitDeny(query: Query, store: Store)
    requires // If no permit policy is in force, then
      forall p |
        p in store.policies.policies.Keys &&
        store.policies.policies[p].effect == Permit ::
        !Authorizer(query, store).isInForce(p)
    ensures // the request is denied.
      Authorizer(query, store).isAuthorized().decision == Deny
  { }

  lemma ForbidTrumpsPermit(query: Query, store: Store)
    requires // If some forbid policy is in force, then
      exists f ::
        f in store.policies.policies.Keys &&
        store.policies.policies[f].effect == Forbid &&
        Authorizer(query, store).isInForce(f)
    ensures // the request is denied.
      Authorizer(query, store).isAuthorized().decision == Deny
  {
    var f :| f in Authorizer(query, store).forbids();
  }

  // A request is explicitly permitted when there is at least one permit policy
  // that is in force and no forbid policies are in force.
  ghost predicate IsExplicitlyPermitted(query: Query, store: Store) {
    (exists p ::
       p in store.policies.policies.Keys &&
       store.policies.policies[p].effect == Permit &&
       Authorizer(query, store).isInForce(p)) &&
    (forall f |
       (f in store.policies.policies.Keys &&
        store.policies.policies[f].effect == Forbid) ::
       !Authorizer(query, store).isInForce(f))
  }

  lemma AllowedIffExplicitlyPermitted(query: Query, store: Store)
    ensures // A request is allowed if and only if it is explictly permitted.
      Authorizer(query, store).isAuthorized().decision == Allow <==>
      IsExplicitlyPermitted(query, store)
  {
    var authz := Authorizer(query, store);
    if IsExplicitlyPermitted(query, store) {
      var p :| p in Authorizer(query, store).permits();
    } else {
      if Authorizer(query, store).permits() != {} {
        var f :| f in Authorizer(query, store).forbids();
      }
    }
  }

}
