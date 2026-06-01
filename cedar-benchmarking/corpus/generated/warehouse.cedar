// Allow picking during shift
permit (
    principal,
    action == Action::"pick",
    resource
)
when {
    context.timestamp >= principal.shift_start &&
    context.timestamp < principal.shift_end
};

// Block picking items exceeding weight limit
forbid (
    principal,
    action == Action::"pick",
    resource
)
when { resource.weight_kg.greaterThan(principal.max_weight_kg) };

// Block picking expired items
forbid (
    principal,
    action == Action::"pick",
    resource
)
when { resource.expiry < datetime("2025-01-01T00:00:00Z") };

// Allow storing by certified workers
permit (
    principal,
    action == Action::"store",
    resource
)
when { principal.role == "stocker" || principal.role == "lead" };

// Block storing hazmat without certification
forbid (
    principal,
    action == Action::"store",
    resource
)
when { context.hazmat && principal.role != "lead" };

// Block storing heavy items exceeding worker limit
forbid (
    principal,
    action == Action::"store",
    resource
)
when { context.item_weight_kg.greaterThan(principal.max_weight_kg) };

// Allow inspection from warehouse network
permit (
    principal,
    action == Action::"inspect",
    resource
)
when { context.source_ip.isInRange(ip("192.168.0.0/16")) };

// Block picking hazmat items by non-certified workers
forbid (
    principal,
    action == Action::"pick",
    resource
)
when { resource.hazmat && principal.role != "lead" };

// Allow leads full access during shift
permit (
    principal,
    action,
    resource
)
when {
    principal.role == "lead" &&
    context.timestamp >= principal.shift_start
};

// Block high-value item picks without lead role
forbid (
    principal,
    action == Action::"pick",
    resource
)
when { resource.value.greaterThan(decimal("5000.00")) && principal.role != "lead" };
