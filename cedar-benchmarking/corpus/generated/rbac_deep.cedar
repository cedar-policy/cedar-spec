// Users can read documents at or below their clearance
permit (
    principal,
    action == Action::"read",
    resource
)
when { principal.clearance >= resource.classification };

// Users can write documents they own
permit (
    principal,
    action == Action::"write",
    resource
)
when { resource.owner == principal };

// Only high-clearance users can delete
permit (
    principal,
    action == Action::"delete",
    resource
)
when { principal.clearance >= 5 && resource.owner == principal };

// Block inactive users from all actions
forbid (
    principal,
    action,
    resource
)
when { !principal.active };

// Allow sharing within same department
permit (
    principal,
    action == Action::"share",
    resource
)
when { resource.owner == principal };

// Block sharing classified documents
forbid (
    principal,
    action == Action::"share",
    resource
)
when { resource.classification >= 4 };

// Team leads can read all team documents
permit (
    principal,
    action == Action::"read",
    resource
)
when { principal.clearance >= 3 };

// Block write to documents above clearance
forbid (
    principal,
    action == Action::"write",
    resource
)
when { principal.clearance < resource.classification };
