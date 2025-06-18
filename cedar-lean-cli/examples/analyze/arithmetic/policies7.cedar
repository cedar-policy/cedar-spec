permit(principal, action, resource) when {
    principal.n + resource.n > context.n
};
// bound the ranges of the variables involved such that no overflow will happen
forbid(principal, action, resource) when {
    principal.n < -10000 ||
    resource.n < -10000 ||
    context.n < -10000 ||
    principal.n > 10000 ||
    resource.n > 10000 ||
    context.n > 10000
};