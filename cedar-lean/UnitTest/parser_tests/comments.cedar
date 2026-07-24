// Comment at very start of file
permit(principal, action, resource);

permit(principal, action, resource); // comment after semicolon

permit(// comment inside scope
principal, action, resource);

permit(principal,// after comma
action, resource);

permit(principal, action, resource)
// comment between scope and condition
when { true };

permit(principal, action, resource) when {
// comment inside condition body
true };

permit(principal, action, resource) when { true }
// comment between conditions
unless { false };

// comment before annotation
@id("test1")
permit(principal, action, resource);

@id("test2") // comment after annotation
permit(principal, action, resource);

permit(principal, action, resource) when {
    context.x == 1 // comment after expression
    && context.y == 2
};

permit(principal, action, resource) when {
    context.x == 1 &&
    // comment between operands
    context.y == 2
};

permit(principal == User::"alice", // comment after entity ref
action, resource);

permit(principal, action, resource) when {
    [
        1, // comment in list
        2,
        3
    ].contains(context.x)
};

permit(principal, action, resource) when {
    {
        key: 1, // comment in record
        other: 2
    } == context.x
};

// Multiple consecutive comment lines
// describing this policy
// in detail
permit(principal, action, resource);

permit(principal, action, resource) when {
    if // comment after if
    true
    then // comment after then
    1
    else // comment after else
    2 == context.x
};

permit(principal, action, resource) when {
    resource.tags.contains(// comment inside method args
    "active")
};

permit(principal, action, resource) when {
    principal in [
        Group::"a", // first group
        Group::"b"  // second group
    ]
};

// comment with special chars: @#$%^&*(){}[]
permit(principal, action, resource);

// comment with // nested slashes // inside
permit(principal, action, resource);

permit(principal, action, resource) when { true }; // last policy comment
// trailing comment at end of file
