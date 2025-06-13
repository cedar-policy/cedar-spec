permit(principal, action, resource) when {
    context.n1 == 10 && context.n2 == 20 &&
    context.ns == [context.n1, context.n2, 20, 10, context.n2, 10, context.n2]
};