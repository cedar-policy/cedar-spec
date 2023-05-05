include "../def/all.dfy"

module basic {
  import opened def.base
  import opened def.core
  import opened def.engine

  lemma ForbidTrumpsPermit(request: Request, store: Store)
    requires // If some forbid policy is satisfied, then
      exists f ::
        f in store.policies.policies.Keys &&
        store.policies.policies[f].effect == Forbid &&
        Authorizer(request, store).satisfied(f)
    ensures // the request is denied.
      Authorizer(request, store).isAuthorized().decision == Deny
  {
    var f :| f in Authorizer(request, store).forbids();
  }

  // A request is explicitly permitted when there is at least one permit policy
  // that is satisfied.
  predicate IsExplicitlyPermitted(request: Request, store: Store) {
    exists p ::
      p in store.policies.policies.Keys &&
      store.policies.policies[p].effect == Permit &&
      Authorizer(request, store).satisfied(p)
  }

  lemma AllowedIfExplicitlyPermitted(request: Request, store: Store)
    ensures // A request is allowed only if it is explictly permitted.
      Authorizer(request, store).isAuthorized().decision == Allow ==>
        IsExplicitlyPermitted(request, store)
  { }

  // DefaultDeny is the contrapositive of AllowedIfExplicitlyPermitted
  lemma DefaultDeny(request: Request, store: Store)
    ensures // If not explicitly permitted, a request is denied
      !IsExplicitlyPermitted(request,store) ==>
        Authorizer(request, store).isAuthorized().decision == Deny
  { }

}
