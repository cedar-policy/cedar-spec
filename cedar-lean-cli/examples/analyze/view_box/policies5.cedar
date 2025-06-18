// policy0
permit(principal == User::"amelia", action, resource);

// policy1
permit(principal is User, action, resource);

// policy2
// matches nothing because `resource` cannot be both `Thing` and `Box`
forbid(principal, action, resource is Thing) when {
    resource is Box
};

// policy3
permit(principal, action, resource) when {
    resource.owner == principal
};

// policy4
forbid(principal, action == Action::"view", resource is Box);