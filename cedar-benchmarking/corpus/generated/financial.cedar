// Allow transfers within approval limit
permit (
    principal,
    action == Action::"transfer",
    resource
)
when { context.amount.lessThanOrEqual(principal.approval_limit) };

// Block transfers exceeding daily limit
forbid (
    principal,
    action == Action::"transfer",
    resource
)
when { context.amount.greaterThan(resource.daily_limit) };

// Block transfers from outside branch network
forbid (
    principal,
    action == Action::"transfer",
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow account closure by senior staff
permit (
    principal,
    action == Action::"close_account",
    resource
)
when { principal.level >= 3 };

// Block closure of accounts with positive balance
forbid (
    principal,
    action == Action::"close_account",
    resource
)
when { resource.balance.greaterThan(decimal("0.00")) };

// Allow audit from internal network
permit (
    principal,
    action == Action::"audit",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block audit periods longer than 1 year
forbid (
    principal,
    action == Action::"audit",
    resource
)
when { context.period > duration("365d") };

// Allow small transfers without restriction
permit (
    principal,
    action == Action::"transfer",
    resource
)
when { context.amount.lessThan(decimal("100.00")) };

// Block transfers to same account
forbid (
    principal,
    action == Action::"transfer",
    resource
)
when { context.destination == resource.owner };
