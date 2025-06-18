// policy0
// this policy AllowsAll for multiple signatures
permit(principal, action == Action::"comment", resource is D);

// policy1
// here's another policy which AllowsAll for a subset of the same
// signatures, and also is redundant with policy0 for that signature
permit(principal is C, action == Action::"comment", resource is D);

// policy2
// this policy DeniesAll for multiple signatures
forbid(principal is A, action == Action::"create", resource);

// policy3
// this policy AllowsNone, because the `when` condition is impossible:
// no entity type can be `in` something of type `A` according to this
// schema
permit(principal, action, resource in Group::"1") when {
    resource in A::"a"
};

// policy4
// this policy DeniesNone, because the `when` condition is impossible
forbid(principal, action == Action::"comment", resource) when {
    resource.val > principal.val &&
    principal.val > resource.val
};

// policy5
// this policy is redundant with policy1, because the `when` condition
// is always true. (as a result it's also redundant with policy0, and
// AllowsAll, for the signature (C, comment, D).)
permit(principal is C, action == Action::"comment", resource is D) when {
    principal in Group::"1" ||
    resource in Group::"1" ||
    !(principal in Group::"1")
};

// policy6
// this policy is redundant with policy2, but only for one signature.
// (also DeniesAll for that signature)
forbid(principal is A, action == Action::"create", resource is D);

// policy7
// this policy is shadowed by policy2 for two signatures, and policy6 for one signature
forbid(principal == A::"a", action == Action::"create", resource);

// policy8
// this policy overrides policy1 (and thus policy5 and policy0) for
// the signature (C, comment, D).
// It also DeniesAll for two signatures.
forbid(principal is C, action in [Action::"comment", Action::"delete"], resource is D);

// policy9
// this policy doesn't have any findings itself, but combined with policy10,
// it results in AllowsAll for the signature (B, edit, E)
permit(principal is B, action == Action::"edit", resource is E) when {
    principal.val > 0
};

// policy10
// this policy doesn't have any findings itself, but combined with policy9,
// it results in AllowsAll for the signature (B, edit, E)
permit(principal is B, action == Action::"edit", resource is E) when {
    principal.val <= 0
};

// policy11
// this policy doesn't have any findings itself, but combined with policy0,
// results in the entire policyset not allowing-all for the signature (A, comment, D)
forbid(principal == A::"a", action == Action::"comment", resource in Group::"1");

// policy12
// this policy is shadowed by policy0 for the signatures (*, comment, D);
// shadowed by policy1 and policy5 for the signature (C, comment, D);
// and is overridden by policy8 for the signature (C, comment, D)
permit(principal, action in [Action::"view", Action::"comment"], resource in Group::"PublicAssets") when {
    principal.val > 3
};

// policy13
// this policy doesn't have any findings itself, other than that for the signature
// (C, delete, D), it is overridden by policy8
permit(principal in Group::"admin", action in [Action::"edit", Action::"delete"], resource);

// policy14
// this policy doesn't have any findings itself, other than that for the signature
// (A, create, E), it is overridden by policy2
permit(principal, action in [Action::"create", Action::"share"], resource is E) when {
    principal.val <= 3
};

// as a result of all of these policies, we also have two signatures that are AllowsAll
// for the entire policyset:
// - (B, comment, D) # because of policy0 alone
// - (B, edit, E) # because of policy9 + policy10 together
// note that we _do not_ have AllowsAll for (C, comment, D), even though policy0 allows
// all requests in this sig, because policy8 overrides that.
// and note that we _do not_ have AllowsAll for (A, comment, D), even though policy0 allows
// all requests in this sig, because policy11 partially overrides that.

// as a result of all of these policies, we also have nine signatures that are DeniesAll
// for the entire policyset:
// - (A, create, D) # because of policy2 alone (and policy6 alone)
// - (A, create, E) # because of policy2 alone
// - (C, comment, D) # because of policy8 alone, despite policies 1 and 5
// - (C, delete, D) # because of policy8 alone
// - (B, create, D) # because no policy mentions this sig
// - (C, create, D) # because no policy mentions this sig
// - (A, share, D) # because no policy mentions this sig
// - (B, share, D) # because no policy mentions this sig
// - (C, share, D) # because no policy mentions this sig