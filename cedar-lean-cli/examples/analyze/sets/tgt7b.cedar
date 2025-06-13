permit(principal, action, resource) when {
    context.things1.contains(resource) &&
    resource in context.things2
};