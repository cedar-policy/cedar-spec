// Allow launch in public subnets from internal
permit (
    principal,
    action == Action::"launch",
    resource
)
when { resource.public && context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block expensive launches
forbid (
    principal,
    action == Action::"launch",
    resource
)
when { context.cost.greaterThan(decimal("50.00")) };

// Allow termination from VPN
permit (
    principal,
    action == Action::"terminate",
    resource
)
when { context.source_ip.isInRange(ip("172.16.0.0/12")) };

// Block termination from external
forbid (
    principal,
    action == Action::"terminate",
    resource
)
when {
    !context.source_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.source_ip.isInRange(ip("172.16.0.0/12"))
};

// Allow SG modification from bastion subnet
permit (
    principal,
    action == Action::"modify_sg",
    resource
)
when { context.source_ip.isInRange(ip("10.0.1.0/24")) };

// Block opening SG to 0.0.0.0/0
forbid (
    principal,
    action == Action::"modify_sg",
    resource
)
when { context.new_cidr == ip("0.0.0.0/0") };

// Allow cheap launches without restriction
permit (
    principal,
    action == Action::"launch",
    resource
)
when { context.cost.lessThan(decimal("1.00")) };
