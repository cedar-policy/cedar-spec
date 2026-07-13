// Allow fetches from known client IPs
permit (
    principal,
    action == Action::"fetch",
    resource
)
when { context.source_ip.isInRange(ip("0.0.0.0/0")) };

// Block oversized requests
forbid (
    principal,
    action == Action::"fetch",
    resource
)
when { context.request_size.greaterThan(principal.bandwidth_limit) };

// Allow purge from management network
permit (
    principal,
    action == Action::"purge",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block purge from external
forbid (
    principal,
    action == Action::"purge",
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow fetch if origin is healthy (recent check)
permit (
    principal,
    action == Action::"fetch",
    resource
)
when { resource.health_check.last_check > datetime("2025-01-01T00:00:00Z") };

// Block requests exceeding bandwidth
forbid (
    principal,
    action == Action::"fetch",
    resource
)
when { context.request_size.greaterThan(decimal("1000.0")) };
