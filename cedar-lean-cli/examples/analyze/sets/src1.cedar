permit(principal, action, resource) when {
    context.user1 in [principal, context.user1, context.user2]
};