permit(principal, action, resource) when {
    context.str1 like "a*" && context.str1 != "a"
};