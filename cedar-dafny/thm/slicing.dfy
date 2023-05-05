include "../def/all.dfy"

module slicing {
  import opened def.base
  import opened def.core
  import opened def.engine


  ghost predicate isSliceOfPolicyStore(slice: PolicyStore, store: PolicyStore) {
    slice.policies.Keys <= store.policies.Keys &&
    (forall pid ::
       pid in slice.policies.Keys ==>
         slice.policies[pid] == store.policies[pid])
  }

  ghost predicate isSoundSliceForRequest(request: Request, slice: Store, store: Store) {
    isSliceOfPolicyStore(slice.policies, store.policies) &&
    (forall pid ::
       (pid in store.policies.policies.Keys && pid !in slice.policies.policies.Keys) ==>
         !Authorizer(request, store).satisfied(pid)) &&
    (forall pid ::
       pid in slice.policies.policies.Keys ==>
         Authorizer(request, slice).satisfied(pid) == Authorizer(request, store).satisfied(pid))
  }

  lemma AuthorizationIsCorrectForSoundSlicing(request: Request, slice: Store, store: Store)
    requires isSoundSliceForRequest(request, slice, store)
    ensures Authorizer(request, slice).isAuthorized() == Authorizer(request, store).isAuthorized()
  {
    ForbidsEqv(request, slice, store);
    PermitsEqv(request, slice, store);
  }

  lemma ForbidsEqv(request: Request, slice: Store, store: Store)
    requires isSoundSliceForRequest(request, slice, store)
    ensures Authorizer(request, slice).forbids() == Authorizer(request, store).forbids()
  { }

  lemma PermitsEqv(request: Request, slice: Store, store: Store)
    requires isSoundSliceForRequest(request, slice, store)
    ensures Authorizer(request, slice).permits() == Authorizer(request, store).permits()
  { }

}
