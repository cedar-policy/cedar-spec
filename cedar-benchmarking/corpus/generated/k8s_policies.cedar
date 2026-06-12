// Allow pod creation within quota
permit (
    principal,
    action == Action::"create_pod",
    resource
)
when { context.pod_spec.cpu.lessThanOrEqual(resource.quota.max_cpu) };

// Block oversized memory requests
forbid (
    principal,
    action == Action::"create_pod",
    resource
)
when { context.pod_spec.memory_gb.greaterThan(resource.quota.max_memory_gb) };

// Allow delete from cluster network
permit (
    principal,
    action == Action::"delete_pod",
    resource
)
when { context.source_ip.isInRange(ip("10.244.0.0/16")) };

// Block force delete from outside
forbid (
    principal,
    action == Action::"delete_pod",
    resource
)
when { context.force && !context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Allow exec from bastion
permit (
    principal,
    action == Action::"exec",
    resource
)
when { context.source_ip.isInRange(ip("10.0.1.0/24")) };

// Block exec on high-priority pods
forbid (
    principal,
    action == Action::"exec",
    resource
)
when { resource.scheduling.priority >= 100 };

// Allow pod creation from internal only
permit (
    principal,
    action == Action::"create_pod",
    resource
)
when { context.source_ip.isInRange(ip("10.0.0.0/8")) };

// Block pod creation with no image specified
forbid (
    principal,
    action == Action::"create_pod",
    resource
)
when { context.pod_spec.image == "" };

// Allow delete of expired pods
permit (
    principal,
    action == Action::"delete_pod",
    resource
)
when { context.source_ip.isInRange(ip("10.244.0.0/16")) };

// Block exec from external networks
forbid (
    principal,
    action == Action::"exec",
    resource
)
when {
    !context.source_ip.isInRange(ip("10.0.0.0/8")) &&
    !context.source_ip.isInRange(ip("172.16.0.0/12"))
};
