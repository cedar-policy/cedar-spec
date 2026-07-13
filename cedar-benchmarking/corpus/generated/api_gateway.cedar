// Allow premium tier clients
permit (
    principal,
    action == Action::"invoke",
    resource
)
when { principal.tier == "premium" };

// Allow free tier to public endpoints
permit (
    principal,
    action == Action::"invoke",
    resource
)
when { principal.tier == "free" && !resource.auth_required };

// Block requests from blacklisted ranges
forbid (
    principal,
    action == Action::"invoke",
    resource
)
when { context.source_ip.isInRange(ip("192.168.100.0/24")) };

// Block oversized requests
forbid (
    principal,
    action == Action::"invoke",
    resource
)
when { context.request.content_length > 10485760 };

// Allow internal services
permit (
    principal,
    action == Action::"invoke",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block empty user agents
forbid (
    principal,
    action == Action::"invoke",
    resource
)
when { context.request.user_agent == "" };

// Allow standard tier with auth
permit (
    principal,
    action == Action::"invoke",
    resource
)
when { principal.tier == "standard" && context.request.headers.authorization != "" };
