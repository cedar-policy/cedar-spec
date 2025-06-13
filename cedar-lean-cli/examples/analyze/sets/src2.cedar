permit(principal, action, resource) when {
    [context.user1, context.user2, User::"amelia"].contains(principal)
    || context.users.contains(principal)
};