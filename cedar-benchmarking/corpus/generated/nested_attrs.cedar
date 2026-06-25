// Allow deploy from internal network
permit (
    principal,
    action == Action::"deploy",
    resource
)
when { context.request.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block deploy to projects without public access from external
forbid (
    principal,
    action == Action::"deploy",
    resource
)
when {
    !resource.config.settings.network.allow_public &&
    !context.request.source_ip.isInRange(ip("10.0.0.0/8"))
};

// Allow deploy if instance count within limits
permit (
    principal,
    action == Action::"deploy",
    resource
)
when { context.request.params.instance_count <= resource.config.settings.max_instances };

// Block deploy exceeding instance limit
forbid (
    principal,
    action == Action::"deploy",
    resource
)
when { context.request.params.instance_count > resource.config.settings.max_instances };

// Allow configuration by department owner
permit (
    principal,
    action == Action::"configure",
    resource
)
when { resource.config.environment == "development" };

// Block configuration of production without VPN
forbid (
    principal,
    action == Action::"configure",
    resource
)
when { resource.config.environment == "production" };
