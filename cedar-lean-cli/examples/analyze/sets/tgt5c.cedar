permit(principal, action, resource) when {
    context.thing1 in context.thing2 &&
    context.things.contains(context.thing2)
};