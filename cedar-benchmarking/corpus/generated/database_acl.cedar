// Allow selects from allowed source
permit (
    principal,
    action == Action::"select",
    resource
)
when { context.source_ip.isInRange(principal.source_ip) };

// Block long-running queries
forbid (
    principal,
    action == Action::"select",
    resource
)
when { context.estimated_duration > principal.max_query_duration };

// Allow inserts for writers
permit (
    principal,
    action == Action::"insert",
    resource
)
when { principal.role == "writer" || principal.role == "admin" };

// Block bulk inserts by non-admins
forbid (
    principal,
    action == Action::"insert",
    resource
)
when { context.row_count > 10000 && principal.role != "admin" };

// Block deletes without WHERE clause
forbid (
    principal,
    action == Action::"delete",
    resource
)
when { !context.where_clause };

// Only admins can alter tables
permit (
    principal,
    action == Action::"alter",
    resource
)
when { principal.role == "admin" };

// Block access to PII tables by non-admins
forbid (
    principal,
    action,
    resource
)
when { resource.pii && principal.role != "admin" };

// Allow reads on small tables without restriction
permit (
    principal,
    action == Action::"select",
    resource
)
when { resource.size_gb.lessThan(decimal("1.0")) };

// Block external access
forbid (
    principal,
    action,
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow admins full access from internal
permit (
    principal,
    action,
    resource
)
when { principal.role == "admin" && context.source_ip.isInRange(ip("10.0.0.0/8")) };
