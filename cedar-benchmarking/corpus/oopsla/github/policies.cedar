// Users can perform an action if they have been granted the necessary permission.
permit (
    principal,
    action == Action::"read",
    resource
)
when { principal in resource.readers };

permit (
    principal,
    action in Action::"triage",
    resource
)
when { principal in resource.triagers };

permit (
    principal,
    action in Action::"write",
    resource
)
when { principal in resource.writers };

permit (
    principal,
    action in Action::"maintain",
    resource
)
when { principal in resource.maintainers };

permit (
    principal,
    action in Action::"admin",
    resource
)
when { principal in resource.admins };

// Users also inherit permissions from the owner of a repository.
permit (
    principal,
    action == Action::"read",
    resource
)
when { principal in resource.owner.readers };

permit (
    principal,
    action in Action::"write",
    resource
)
when { principal in resource.owner.writers };

permit (
    principal,
    action in Action::"admin",
    resource
)
when { principal in resource.owner.admins };