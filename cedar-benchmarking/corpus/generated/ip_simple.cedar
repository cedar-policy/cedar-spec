// Allow access from internal network
permit (
    principal,
    action == Action::"access",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow access from VPN subnet
permit (
    principal,
    action == Action::"access",
    resource
)
when { context.source_ip.isInRange(ip("172.16.0.0/12")) };

// Block access from known bad range
forbid (
    principal,
    action == Action::"access",
    resource
)
when { context.source_ip.isInRange(ip("192.168.100.0/24")) };

// Allow localhost
permit (
    principal,
    action == Action::"access",
    resource
)
when { context.source_ip.isLoopback() };

// Allow access to hosts in the same subnet
permit (
    principal,
    action == Action::"access",
    resource
)
when { context.source_ip.isInRange(ip("10.1.0.0/16")) && resource.address.isInRange(ip("10.1.0.0/16")) };
