// Allow connections from trusted zones
permit (
    principal,
    action == Action::"connect",
    resource
)
when { principal.ip.isInRange(ip("10.0.0.0/8")) && context.dest_ip.isInRange(ip("10.0.0.0/8")) };

// Block connections from external to internal high-trust zones
forbid (
    principal,
    action == Action::"connect",
    resource
)
when {
    !principal.ip.isInRange(ip("10.0.0.0/8")) &&
    !principal.ip.isInRange(ip("172.16.0.0/12"))
};

// Allow multicast
permit (
    principal,
    action == Action::"connect",
    resource
)
when { context.dest_ip.isMulticast() };

// Allow loopback for local services
permit (
    principal,
    action == Action::"connect",
    resource
)
when { context.source_ip.isLoopback() && context.dest_ip.isLoopback() };

// Block scanning from outside
forbid (
    principal,
    action == Action::"scan",
    resource
)
when { !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow scanning from security team subnet
permit (
    principal,
    action == Action::"scan",
    resource
)
when { context.source_ip.isInRange(ip("10.255.0.0/16")) };

// IPv6 internal access
permit (
    principal,
    action == Action::"connect",
    resource
)
when { context.source_ip.isInRange(ip("fd00::/8")) };

// Block link-local as source for external services
forbid (
    principal,
    action == Action::"connect",
    resource
)
when { context.source_ip.isInRange(ip("169.254.0.0/16")) };
