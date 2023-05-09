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
    ensures // A request is allowed only if it is explicitly permitted.
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
