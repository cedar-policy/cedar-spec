// policy0
permit(principal, action, resource == Box::"widgets");

// policy1
permit(principal == User::"amelia", action == Action::"view", resource == Thing::"widget");

// policy2
permit(principal == User::"brittany", action == Action::"view", resource == Box::"brit's box");

// policy3
forbid(principal is User, action == Action::"view", resource in Box::"widgets");