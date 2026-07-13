// Allow scaling from internal network
permit (
    principal,
    action == Action::"scale",
    resource
)
when { context.request.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block scaling beyond resource limits
forbid (
    principal,
    action == Action::"scale",
    resource
)
when { resource.config.deployment.resources.limits.cpu.lessThan(decimal("0.5")) };

// Allow reconfiguration by high-clearance operators
permit (
    principal,
    action == Action::"reconfigure",
    resource
)
when { principal.clearance >= 4 };

// Block reconfiguration of TLS-enabled services by low clearance
forbid (
    principal,
    action == Action::"reconfigure",
    resource
)
when { resource.config.deployment.network.ingress.tls && principal.clearance < 3 };

// Allow scaling services with monitoring enabled
permit (
    principal,
    action == Action::"scale",
    resource
)
when { resource.config.monitoring.enabled };

// Block scaling from external
forbid (
    principal,
    action == Action::"scale",
    resource
)
when {
    !context.request.source_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.request.source_ip.isInRange(ip("172.16.0.0/12"))
};

// Allow reconfiguration from management subnet
permit (
    principal,
    action == Action::"reconfigure",
    resource
)
when { context.change.source_ip.isInRange(ip("10.0.1.0/24")) };

// Block reconfiguration of services allowing internet egress
forbid (
    principal,
    action == Action::"reconfigure",
    resource
)
when { resource.config.deployment.network.egress.allow_internet && principal.clearance < 5 };
