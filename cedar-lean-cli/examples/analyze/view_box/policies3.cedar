// policy0
permit(principal, action, resource is Box);

// policy1
forbid(principal, action, resource in Box::"widgets");