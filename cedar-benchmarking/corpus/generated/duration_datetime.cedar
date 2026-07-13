// Allow execution if within timeout
permit (
    principal,
    action == Action::"execute",
    resource
)
when { context.elapsed < resource.timeout };

// Block if task exceeds max duration
forbid (
    principal,
    action == Action::"execute",
    resource
)
when { context.elapsed >= resource.max_duration };

// Allow scheduling short tasks
permit (
    principal,
    action == Action::"schedule",
    resource
)
when { context.requested_duration <= duration("1h") };

// Block scheduling tasks longer than 24h
forbid (
    principal,
    action == Action::"schedule",
    resource
)
when { context.requested_duration > duration("24h") };

// Allow execution during worker shift
permit (
    principal,
    action == Action::"execute",
    resource
)
when {
    context.current_time >= principal.shift_start &&
    context.current_time < principal.shift_end
};

// Block scheduling in the past
forbid (
    principal,
    action == Action::"schedule",
    resource
)
when { context.start_time < datetime("2024-01-01T00:00:00Z") };
