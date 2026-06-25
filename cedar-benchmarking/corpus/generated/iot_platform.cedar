// Allow telemetry reads from same network
permit (
    principal,
    action == Action::"read_telemetry",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow commands from high-level controllers
permit (
    principal,
    action == Action::"send_command",
    resource
)
when { principal.level >= 3 };

// Block commands with excessive timeout
forbid (
    principal,
    action == Action::"send_command",
    resource
)
when { context.timeout > duration("5m") };

// Allow firmware updates from management subnet
permit (
    principal,
    action == Action::"update_firmware",
    resource
)
when { context.source_ip.isInRange(ip("10.0.100.0/24")) };

// Block firmware updates to devices with low battery
forbid (
    principal,
    action == Action::"update_firmware",
    resource
)
when { resource.telemetry.battery.lessThan(decimal("20.0")) };

// Block commands from external network
forbid (
    principal,
    action == Action::"send_command",
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow reads for all controllers
permit (
    principal,
    action == Action::"read_telemetry",
    resource
)
when { principal.level >= 1 };

// Block commands to devices not recently seen
forbid (
    principal,
    action == Action::"send_command",
    resource
)
when { resource.last_seen < datetime("2024-01-01T00:00:00Z") };
