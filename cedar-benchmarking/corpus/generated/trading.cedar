// Allow orders from registered network
permit (
    principal,
    action == Action::"place_order",
    resource
)
when { context.source_ip.isInRange(principal.network) };

// Block orders on halted instruments
forbid (
    principal,
    action == Action::"place_order",
    resource
)
when { resource.halted };

// Block orders exceeding max position
forbid (
    principal,
    action == Action::"place_order",
    resource
)
when { context.order.quantity.greaterThan(principal.max_position) };

// Allow cancellations from same network
permit (
    principal,
    action == Action::"cancel_order",
    resource
)
when { context.source_ip.isInRange(principal.network) };

// Block orders below minimum
forbid (
    principal,
    action == Action::"place_order",
    resource
)
when { context.order.quantity.lessThan(decimal("1.0")) };

// Allow senior traders higher limits
permit (
    principal,
    action == Action::"place_order",
    resource
)
when { principal.level >= 4 && context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block orders from external networks
forbid (
    principal,
    action == Action::"place_order",
    resource
)
when {
    !context.source_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.source_ip.isInRange(ip("172.16.0.0/12"))
};

// Block cancellations from external
forbid (
    principal,
    action == Action::"cancel_order",
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };
