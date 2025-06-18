permit(principal, action, resource) when {
    (principal.n - context.n) + (resource.n - context.n) > (-context.n)
};