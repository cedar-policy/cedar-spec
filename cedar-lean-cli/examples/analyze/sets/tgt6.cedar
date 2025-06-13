permit(principal, action, resource) when {
    context.things1.containsAll(context.things2) &&
    context.thing1 in context.things2
};