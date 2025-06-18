permit(principal, action, resource) when {
    [context.user1, User::"amelia", context.user2, context.user1, User::"amelia", User::"amelia"].contains(principal)
    || context.users.contains(principal)
};