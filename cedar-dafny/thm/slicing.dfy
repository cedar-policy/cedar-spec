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

  ghost predicate isSoundSliceForQuery(query: Query, slice: Store, store: Store) {
    isSliceOfPolicyStore(slice.policies, store.policies) &&
    (forall pid ::
       (pid in store.policies.policies.Keys && pid !in slice.policies.policies.Keys) ==>
         !Authorizer(query, store).isInForce(pid)) &&
    (forall pid ::
       pid in slice.policies.policies.Keys ==>
         Authorizer(query, slice).isInForce(pid) == Authorizer(query, store).isInForce(pid))
  }

  lemma AuthorizationIsCorrectForSoundSlicing(query: Query, slice: Store, store: Store)
    requires isSoundSliceForQuery(query, slice, store)
    ensures Authorizer(query, slice).isAuthorized() == Authorizer(query, store).isAuthorized()
  {
    ForbidsEqv(query, slice, store);
    PermitsEqv(query, slice, store);
  }

  lemma ForbidsEqv(query: Query, slice: Store, store: Store)
    requires isSoundSliceForQuery(query, slice, store)
    ensures Authorizer(query, slice).forbids() == Authorizer(query, store).forbids()
  { }

  lemma PermitsEqv(query: Query, slice: Store, store: Store)
    requires isSoundSliceForQuery(query, slice, store)
    ensures Authorizer(query, slice).permits() == Authorizer(query, store).permits()
  { }

}
