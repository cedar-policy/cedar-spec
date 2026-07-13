// Doctors can view any patient record
permit (
    principal,
    action == Action::"view_record",
    resource
)
when { principal.role == "doctor" };

// Nurses can view patients in their department
permit (
    principal,
    action == Action::"view_record",
    resource
)
when { principal.role == "nurse" };

// Only doctors can modify records
permit (
    principal,
    action == Action::"modify_record",
    resource
)
when { principal.role == "doctor" };

// Only doctors can prescribe
permit (
    principal,
    action == Action::"prescribe",
    resource
)
when { principal.role == "doctor" };

// Block access from outside hospital network
forbid (
    principal,
    action,
    resource
)
when { context has source_ip && !context.source_ip.isInRange(ip("192.168.1.0/24")) };

// Block high dosage prescriptions
forbid (
    principal,
    action == Action::"prescribe",
    resource
)
when { context.dosage.greaterThan(decimal("500.00")) };

// Block access with expired license
forbid (
    principal,
    action,
    resource
)
when { principal.license_expiry < datetime("2025-01-01T00:00:00Z") };

// Allow emergency access to critical patients
permit (
    principal,
    action == Action::"view_record",
    resource
)
when { resource.diagnosis.severity >= 8 };

// Block modification of high-severity cases by non-specialists
forbid (
    principal,
    action == Action::"modify_record",
    resource
)
when { resource.diagnosis.severity >= 9 && principal.role != "doctor" };
