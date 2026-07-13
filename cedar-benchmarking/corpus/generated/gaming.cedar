// Allow entry if player meets level requirement
permit (
    principal,
    action == Action::"enter_zone",
    resource
)
when { principal.level >= resource.level_requirement };

// Block entry for low-reputation players in PVP zones
forbid (
    principal,
    action == Action::"enter_zone",
    resource
)
when { resource.pvp_enabled && principal.stats.reputation.lessThan(decimal("0.5")) };

// Allow trading for premium players
permit (
    principal,
    action == Action::"trade",
    resource
)
when { principal.premium };

// Block high-value trades for new players
forbid (
    principal,
    action == Action::"trade",
    resource
)
when { context.amount.greaterThan(decimal("1000.0")) && principal.stats.play_time < duration("24h") };

// Allow chat for all players
permit (
    principal,
    action == Action::"chat",
    resource
)
when { principal.level >= 1 };

// Block chat for very low reputation
forbid (
    principal,
    action == Action::"chat",
    resource
)
when { principal.stats.reputation.lessThan(decimal("0.1")) };

// Allow entry for premium players regardless of level
permit (
    principal,
    action == Action::"enter_zone",
    resource
)
when { principal.premium && principal.level >= 5 };

// Block sessions exceeding 12 hours
forbid (
    principal,
    action == Action::"enter_zone",
    resource
)
when { context.session_duration > duration("12h") };
