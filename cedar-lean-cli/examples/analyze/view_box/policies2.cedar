// policy0
permit(principal == User::"amelia", action, resource in Box::"widgets");

// policy1
permit(principal == User::"amelia", action, resource in Box::"widgets") when {
    !resource.private
};