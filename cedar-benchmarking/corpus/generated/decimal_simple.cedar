// Auto-approve small transactions
permit (
    principal,
    action == Action::"approve",
    resource
)
when { resource.amount.lessThan(decimal("100.00")) };

// Require review for large transactions
forbid (
    principal,
    action == Action::"approve",
    resource
)
when { resource.amount.greaterThanOrEqual(decimal("10000.00")) };

// Block if daily total exceeds limit
forbid (
    principal,
    action == Action::"approve",
    resource
)
when { context.daily_total.greaterThan(context.user_limit) };

// Allow submissions under threshold
permit (
    principal,
    action == Action::"submit",
    resource
)
when { context.amount.lessThanOrEqual(decimal("5000.00")) };

// Block negative amounts
forbid (
    principal,
    action == Action::"submit",
    resource
)
when { context.amount.lessThan(decimal("0.00")) };
