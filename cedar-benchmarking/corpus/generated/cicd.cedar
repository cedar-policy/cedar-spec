// Allow triggers from developer's allowed network
permit (
    principal,
    action == Action::"trigger",
    resource
)
when { context.source_ip.isInRange(principal.ip_allowlist) };

// Block triggers from external
forbid (
    principal,
    action == Action::"trigger",
    resource
)
when {
    !context.source_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.source_ip.isInRange(ip("172.16.0.0/12"))
};

// Allow log viewing from internal
permit (
    principal,
    action == Action::"view_logs",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow artifact downloads within size limit
permit (
    principal,
    action == Action::"download_artifact",
    resource
)
when { context.artifact_size_mb.lessThanOrEqual(resource.config.artifacts.max_size_mb) };

// Block oversized artifact downloads
forbid (
    principal,
    action == Action::"download_artifact",
    resource
)
when { context.artifact_size_mb.greaterThan(decimal("500.0")) };

// Allow maintainers to trigger any pipeline
permit (
    principal,
    action == Action::"trigger",
    resource
)
when { principal.role == "maintainer" };

// Block triggers by new developers (joined recently)
forbid (
    principal,
    action == Action::"trigger",
    resource
)
when { principal.joined > datetime("2025-06-01T00:00:00Z") };

// Allow viewing logs for developers
permit (
    principal,
    action == Action::"view_logs",
    resource
)
when { principal.role == "maintainer" || principal.role == "developer" };
