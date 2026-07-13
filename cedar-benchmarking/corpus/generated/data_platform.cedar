// Allow queries from internal network
permit (
    principal,
    action == Action::"query",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block queries on classified data by junior engineers
forbid (
    principal,
    action == Action::"query",
    resource
)
when { resource.classification == "restricted" && principal.level < 3 };

// Allow pipeline runs from CI/CD subnet
permit (
    principal,
    action == Action::"run_pipeline",
    resource
)
when { context.source_ip.isInRange(ip("10.1.0.0/16")) };

// Block pipeline runs with schedule override by non-seniors
forbid (
    principal,
    action == Action::"run_pipeline",
    resource
)
when { context.override_schedule && principal.level < 4 };

// Allow encrypted exports
permit (
    principal,
    action == Action::"export",
    resource
)
when { context.encrypted };

// Block unencrypted exports of classified data
forbid (
    principal,
    action == Action::"export",
    resource
)
when { !context.encrypted && resource.classification != "public" };

// Block exports to external IPs
forbid (
    principal,
    action == Action::"export",
    resource
)
when {
    !context.destination_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.destination_ip.isInRange(ip("172.16.0.0/12"))
};

// Allow queries with row limits
permit (
    principal,
    action == Action::"query",
    resource
)
when { context.row_limit <= 10000 };

// Block pipeline runs on pipelines with unencrypted source
forbid (
    principal,
    action == Action::"run_pipeline",
    resource
)
when { !resource.config.source.connection.encrypted };

// Allow senior engineers full access
permit (
    principal,
    action,
    resource
)
when { principal.level >= 5 };
