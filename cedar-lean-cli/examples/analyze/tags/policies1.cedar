permit(principal, action, resource) when {
    resource.hasTag("public") && resource.getTag("public") &&
    resource.hasTag("internal") && !resource.getTag("internal")
};
