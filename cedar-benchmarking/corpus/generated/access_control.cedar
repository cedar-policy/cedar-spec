// Allow entry (badge not expired)
permit (
    principal,
    action == Action::"enter",
    resource
)
when { context.timestamp < principal.expires };

// Block expired badges
forbid (
    principal,
    action,
    resource
)
when { principal.expires < datetime("2025-01-01T00:00:00Z") };

// Allow high-level badges everywhere
permit (
    principal,
    action == Action::"enter",
    resource
)
when { principal.access_level >= 5 };

// Block entry to restricted floors without level 3+
forbid (
    principal,
    action == Action::"enter",
    resource
)
when { resource.floor >= 10 && principal.access_level < 3 };

// Allow short unlocks
permit (
    principal,
    action == Action::"unlock",
    resource
)
when { context.duration <= duration("1h") };

// Block long unlocks
forbid (
    principal,
    action == Action::"unlock",
    resource
)
when { context.duration > duration("8h") };

// Allow entry from building network readers
permit (
    principal,
    action == Action::"enter",
    resource
)
when { context.reader_ip.isInRange(resource.network) };
