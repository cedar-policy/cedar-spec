// ===== Basic policy structure =====
// policy0: minimal permit
permit (principal, action, resource);

// policy1: minimal forbid
forbid (principal, action, resource);

// policy2: when clause
permit (principal, action, resource)
when { true };

// policy3: unless clause
forbid (principal, action, resource)
unless { false };

// policy4: when + unless
permit (principal, action, resource)
when { true }
unless { false };

// policy5: multiple when clauses
permit (principal, action, resource)
when { true }
when { true };

// ===== Annotations =====
// policy6: single annotation with value
@id("policy6")
permit (principal, action, resource);

// policy7: annotation without value
@shadow_mode
forbid (principal, action, resource);

// policy8: multiple annotations
@id("policy8")
@advice("Allow admins full access")
permit (principal, action, resource);

// ===== Variable definitions / scope constraints =====
// policy9: principal ==
permit (
    principal == User::"alice",
    action,
    resource
);

// policy10: principal in
permit (
    principal in Group::"admins",
    action,
    resource
);

// policy11: principal is
permit (
    principal is User,
    action,
    resource
);

// policy12: principal is ... in
permit (
    principal is User in Group::"admins",
    action,
    resource
);

// policy13: action ==
permit (
    principal,
    action == Action::"read",
    resource
);

// policy14: action in single entity
permit (
    principal,
    action in Action::"readOnly",
    resource
);

// policy15: action in list
permit (
    principal,
    action in [Action::"read", Action::"write", Action::"delete"],
    resource
);

// policy16: resource ==
permit (
    principal,
    action,
    resource == File::"report.pdf"
);

// policy17: resource in
permit (
    principal,
    action,
    resource in Folder::"documents"
);

// policy18: resource is
permit (
    principal,
    action,
    resource is Photo
);

// policy19: resource is ... in
permit (
    principal,
    action,
    resource is Photo in Album::"vacation"
);

// policy20: all scopes constrained
forbid (
    principal == User::"mallory",
    action == Action::"admin",
    resource in Folder::"secrets"
);

// policy21: template slot ?principal
permit (
    principal == ?principal,
    action,
    resource
);

// policy22: template slot ?resource
permit (
    principal,
    action,
    resource in ?resource
);

// policy23: principal is with slot
permit (
    principal is User in ?principal,
    action,
    resource
);

// ===== Arithmetic operators =====
// policy24: addition
permit (principal, action, resource)
when { context.x + 1 == 10 };

// policy25: subtraction
permit (principal, action, resource)
when { context.x - 5 == 0 };

// policy26: multiplication
permit (principal, action, resource)
when { context.x * 2 == 20 };

// policy27: combined arithmetic with precedence
permit (principal, action, resource)
when { context.x + context.y * 2 - 1 == 10 };

// policy28: parenthesized arithmetic
permit (principal, action, resource)
when { (context.x + 1) * 2 == 10 };

// policy29: negative literal
permit (principal, action, resource)
when { context.x == -3 };

// policy30: negation of expression
permit (principal, action, resource)
when { -(context.x) + 10 > 0 };

// ===== Comparison operators =====
// policy31: less than
permit (principal, action, resource)
when { context.level < 10 };

// policy32: less than or equal
permit (principal, action, resource)
when { context.level <= 10 };

// policy33: greater than
permit (principal, action, resource)
when { context.level > 0 };

// policy34: greater than or equal
permit (principal, action, resource)
when { context.level >= 1 };

// policy35: not equal
permit (principal, action, resource)
when { context.status != "blocked" };

// policy36: equality
permit (principal, action, resource)
when { context.role == "admin" };

// ===== Boolean operators =====
// policy37: or
permit (principal, action, resource)
when { context.isAdmin || context.isModerator };

// policy38: and
permit (principal, action, resource)
when { context.isActive && context.isVerified };

// policy39: not
permit (principal, action, resource)
when { !context.isBlocked };

// policy40: combined boolean
permit (principal, action, resource)
when { (context.isAdmin || context.isModerator) && !context.isSuspended };

// policy41: chained or
permit (principal, action, resource)
when { context.role == "admin" || context.role == "editor" || context.role == "viewer" };

// ===== Relation operators =====
// policy42: in (membership)
permit (principal, action, resource)
when { principal in Group::"editors" };

// policy43: in with set expression
permit (principal, action, resource)
when { principal in [Group::"a", Group::"b"] };

// policy44: in with context set
permit (principal, action, resource)
when { principal in context.groups };

// policy45: has (attribute presence) with ident
permit (principal, action, resource)
when { resource has owner };

// policy46: has with string literal
permit (principal, action, resource)
when { resource has "owner info" };

// policy47: like (pattern matching)
permit (principal, action, resource)
when { resource.filename like "*.txt" };

// policy48: like with escaped star
permit (principal, action, resource)
when { resource.name like "file\*.log" };

// policy49: is (type test)
permit (principal, action, resource)
when { resource is Document };

// policy50: is ... in (type test with membership)
permit (principal, action, resource)
when { resource is Document in Folder::"shared" };

// policy51: hasTag
permit (principal, action, resource)
when { resource.hasTag("env") };

// policy52: getTag
permit (principal, action, resource)
when { resource.getTag("env") == "prod" };

// ===== If-then-else =====
// policy53: simple if-then-else
permit (principal, action, resource)
when { if context.isAdmin then true else context.level > 5 };

// policy54: nested if-then-else
permit (principal, action, resource)
when
{
    if
        context.role == "admin"
    then
        true
    else
        if context.role == "editor" then context.level >= 3 else false
};

// ===== Member access =====
// policy55: field access
permit (principal, action, resource)
when { resource.owner == principal };

// policy56: chained field access
permit (principal, action, resource)
when { context.request.headers.contentType == "json" };

// policy57: index access with string
permit (principal, action, resource)
when { resource.tags["environment"] == "production" };

// policy58: method call - contains
permit (principal, action, resource)
when { resource.readers.contains(principal) };

// policy59: method call - containsAll
permit (principal, action, resource)
when { resource.tags.containsAll(["public", "approved"]) };

// policy60: method call - containsAny
permit (principal, action, resource)
when { context.roles.containsAny(["admin", "reviewer"]) };

// policy61: method call - isEmpty
permit (principal, action, resource)
when { !resource.blocked.isEmpty() };

// ===== Extension functions (constructor style) =====
// policy62: ip address
permit (principal, action, resource)
when { ip("192.168.0.1").isInRange(ip("192.168.0.0/24")) };

// policy63: ip methods
permit (principal, action, resource)
when
{ context.sourceIp.isIpv4() && !context.sourceIp.isLoopback() && !context.sourceIp.isMulticast() };

// policy64: decimal
permit (principal, action, resource)
when { decimal("1.23").lessThan(decimal("4.56")) };

// policy65: decimal comparison methods
permit (principal, action, resource)
when
{
    context.score.greaterThanOrEqual(decimal("3.5")) &&
    context.score.lessThanOrEqual(decimal("10.0"))
};

// policy66: datetime
permit (principal, action, resource)
when { datetime("2024-10-15T11:35:00Z") < context.expiry };

// policy67: datetime methods
permit (principal, action, resource)
when
{
    context.timestamp.toDate() == datetime("2024-10-15") &&
    context.timestamp.toTime().toHours() >= 9
};

// policy68: duration
permit (principal, action, resource)
when { duration("2h30m") > context.elapsed };

// policy69: duration methods
permit (principal, action, resource)
when { context.timeout.toMilliseconds() < 5000 && context.retention.toDays() >= 30 };

// policy70: datetime offset and durationSince
permit (principal, action, resource)
when
{
    context.now.durationSince(context.lastLogin).toHours() < 24 &&
    context.now.offset(duration("-1h")) < context.deadline
};

// ===== Primary expressions =====
// policy71: set literal
permit (principal, action, resource)
when { [1, 2, 3, 4, 5].contains(context.level) };

// policy72: empty set
permit (principal, action, resource)
when { [].containsAll(context.emptyList) };

// policy73: record literal with string keys
permit (principal, action, resource)
when { { "key": "value", "count": 42 } == context.metadata };

// policy74: record literal with ident keys
permit (principal, action, resource)
when { { key: "value", count: 42 } == context.metadata };

// policy75: empty record
permit (principal, action, resource)
when { {} == context.emptyRecord };

// policy76: namespaced entity reference
permit (principal, action, resource)
when { principal in App::Organization::Group::"engineering" };

// ===== Negation =====
// policy77: double negation
permit (principal, action, resource)
when { !!context.flag };

// policy78: negation of parenthesized
forbid (principal, action, resource)
when { !(principal in Group::"family") };

// ===== Complex combinations =====
// policy79: multiple conditions with complex expressions
forbid (principal, action, resource)
when { resource has sensitivityLevel }
when { resource.sensitivityLevel >= 3 }
unless { principal in Group::"clearance_level_3" };

// policy80: deeply nested expression
permit (principal, action, resource)
when
{
    (principal is Employee in Department::"engineering") &&
    resource is Repository &&
    (resource has isPublic && resource.isPublic || principal in resource.collaborators)
};

// policy81: arithmetic in comparisons with boolean logic
forbid (principal, action, resource)
when
{
    context.requestCount + 1 > context.rateLimit * 2 &&
    context.timestamp - context.lastReset >= 3600
};

// policy82: mixed member access patterns
permit (principal, action, resource)
when
{
    resource.metadata["owner"] == principal &&
    resource.tags.contains("active") &&
    resource.permissions.containsAll(["read"])
};

// policy83: has with && guard pattern
permit (principal, action, resource)
when { principal has manager && principal.manager == User::"kirk" };

// policy84: has with || guard pattern
permit (principal, action, resource)
when { !(principal has age) || principal.age >= 21 };

// policy85: in with reflexivity
permit (principal, action, resource)
when { resource in resource };

// policy86: complex scope with conditions
@id("admin-override")
@advice("Allows admin override for sensitive resources")
permit (
    principal is Admin in Group::"superadmins",
    action in [Action::"read", Action::"write", Action::"delete"],
    resource is Document in Folder::"classified"
)
when { context.mfaAuthenticated }
when { context.sourceIp.isInRange(ip("10.0.0.0/8")) }
unless { resource has locked && resource.locked };

// ===== Edge cases =====
// policy87: deeply nested parentheses
permit (principal, action, resource)
when { ((((context.x)))) == 1 };

// policy88: long chain of &&
permit (principal, action, resource)
when { context.a && context.b && context.c && context.d && context.e };

// policy89: long chain of ||
permit (principal, action, resource)
when { context.a || context.b || context.c || context.d || context.e };

// policy90: entity with empty string eid
permit (principal, action, resource)
when { principal == User::"" };

// policy91: string with unicode escape
permit (principal, action, resource)
when { context.name == "\u{1F600}" };

// policy92: string with hex escape
permit (principal, action, resource)
when { context.val == "\x41\x42\x43" };

// policy93: multiple extension function calls
permit (principal, action, resource)
when
{
    ip(context.srcIp).isInRange(ip("10.0.0.0/8")) ||
    ip(context.srcIp).isInRange(ip("172.16.0.0/12")) ||
    ip(context.srcIp).isInRange(ip("192.168.0.0/16"))
};

// policy94: comparison chaining (single relop per relation in grammar)
permit (principal, action, resource)
when { context.x >= 0 && context.x <= 100 };

// policy95: set containment patterns
permit (principal, action, resource)
when
{
    [Action::"read", Action::"list"].contains(action) &&
    resource.tags.containsAny(context.allowedTags)
};

// policy96: record in condition
permit (principal, action, resource)
when { context.device == { os: "macOS", version: "14" } };

// policy97: deeply qualified entity type in is
permit (principal, action, resource)
when { principal is ExampleCo::IAM::User };

// policy98: whitespace variations (compact)
permit (principal, action, resource)
when { true };

// policy99: if-then-else as subexpression
permit (principal, action, resource)
when
{
    (if resource has owner then resource.owner == principal else false) ||
    principal in Group::"admins"
};
