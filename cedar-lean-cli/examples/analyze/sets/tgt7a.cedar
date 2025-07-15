permit(principal, action, resource) when {
    context.things1.contains(resource) &&
    context.things2.contains(resource)
};