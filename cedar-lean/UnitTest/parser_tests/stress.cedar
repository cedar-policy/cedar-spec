// Stress tests for large policies and expressions
// 1: Long chain of && (20 operands)
permit (principal, action, resource)
when
{
    context.a1 &&
    context.a2 &&
    context.a3 &&
    context.a4 &&
    context.a5 &&
    context.a6 &&
    context.a7 &&
    context.a8 &&
    context.a9 &&
    context.a10 &&
    context.a11 &&
    context.a12 &&
    context.a13 &&
    context.a14 &&
    context.a15 &&
    context.a16 &&
    context.a17 &&
    context.a18 &&
    context.a19 &&
    context.a20
};

// 2: Long chain of || (20 operands)
permit (principal, action, resource)
when
{
    context.a1 ||
    context.a2 ||
    context.a3 ||
    context.a4 ||
    context.a5 ||
    context.a6 ||
    context.a7 ||
    context.a8 ||
    context.a9 ||
    context.a10 ||
    context.a11 ||
    context.a12 ||
    context.a13 ||
    context.a14 ||
    context.a15 ||
    context.a16 ||
    context.a17 ||
    context.a18 ||
    context.a19 ||
    context.a20
};

// 3: Long addition chain (20 operands)
permit (principal, action, resource)
when
{
    context.a1 +
    context.a2 +
    context.a3 +
    context.a4 +
    context.a5 +
    context.a6 +
    context.a7 +
    context.a8 +
    context.a9 +
    context.a10 +
    context.a11 +
    context.a12 +
    context.a13 +
    context.a14 +
    context.a15 +
    context.a16 +
    context.a17 +
    context.a18 +
    context.a19 +
    context.a20 > 0
};

// 4: Long multiplication chain (20 operands)
permit (principal, action, resource)
when
{
    context.a1 *
    context.a2 *
    context.a3 *
    context.a4 *
    context.a5 *
    context.a6 *
    context.a7 *
    context.a8 *
    context.a9 *
    context.a10 *
    context.a11 *
    context.a12 *
    context.a13 *
    context.a14 *
    context.a15 *
    context.a16 *
    context.a17 *
    context.a18 *
    context.a19 *
    context.a20 > 0
};

// 5: Large set literal (30 elements)
permit (principal, action, resource)
when
{
    [1,
     2,
     3,
     4,
     5,
     6,
     7,
     8,
     9,
     10,
     11,
     12,
     13,
     14,
     15,
     16,
     17,
     18,
     19,
     20,
     21,
     22,
     23,
     24,
     25,
     26,
     27,
     28,
     29,
     30].contains
        (
            context.x
        )
};

// 6: Large record literal (20 fields)
permit (principal, action, resource)
when
{
    {
        field1: { subfield1: "hello", subfield2: { subsubfield1: decimal("10.000") } },
        field2: 2,
        field3: 3,
        field4: 4,
        field5: 5,
        field6: 6,
        field7: 7,
        field8: 8,
        field9: 9,
        field10: 10,
        field11: 11,
        field12: 12,
        field13: 13,
        field14: 14,
        field15: 15,
        field16: 16,
        field17: 17,
        field18: 18,
        field19: 19,
        field20: 20
    } == context.bigRecord
};

// 7: Deep member access chain (20 levels)
permit (principal, action, resource)
when { context.a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t == "deep" };

// 8: Many method calls chained via &&
permit (principal, action, resource)
when
{
    resource.tags.contains("a") &&
    resource.tags.contains("b") &&
    resource.tags.contains("c") &&
    resource.tags.contains("d") &&
    resource.tags.contains("e") &&
    resource.tags.contains("f") &&
    resource.tags.contains("g") &&
    resource.tags.contains("h") &&
    resource.tags.contains("i") &&
    resource.tags.contains("j")
};

// 9: Deeply nested parentheses (20 levels)
permit (principal, action, resource)
when { ((((((((((((((((((((context.x)))))))))))))))))))) == 1 };

// 10: Deeply nested if-then-else (10 levels)
permit (principal, action, resource)
when
{
    if
        context.a1
    then
        if
            context.a2
        then
            if
                context.a3
            then
                if
                    context.a4
                then
                    if
                        context.a5
                    then
                        if
                            context.a6
                        then
                            if
                                context.a7
                            then
                                if
                                    context.a8
                                then
                                    if context.a9 then context.a10 else false
                                else
                                    false
                            else
                                false
                        else
                            false
                    else
                        false
                else
                    false
            else
                false
        else
            false
    else
        false
};

// 11: Action in large list (20 actions)
permit (
    principal,
    action in
        [Action::"a1",
         Action::"a2",
         Action::"a3",
         Action::"a4",
         Action::"a5",
         Action::"a6",
         Action::"a7",
         Action::"a8",
         Action::"a9",
         Action::"a10",
         Action::"a11",
         Action::"a12",
         Action::"a13",
         Action::"a14",
         Action::"a15",
         Action::"a16",
         Action::"a17",
         Action::"a18",
         Action::"a19",
         Action::"a20"],
    resource
);

// 12: Many when/unless conditions (10 conditions)
permit (principal, action, resource)
when { context.c1 }
when { context.c2 }
when { context.c3 }
when { context.c4 }
when { context.c5 }
unless { context.c6 }
unless { context.c7 }
when { context.c8 }
when { context.c9 }
when { context.c10 };

// 13: Large containsAll argument (20 elements)
permit (principal, action, resource)
when
{
    resource.tags
        .containsAll
        (
            ["tag1",
             "tag2",
             "tag3",
             "tag4",
             "tag5",
             "tag6",
             "tag7",
             "tag8",
             "tag9",
             "tag10",
             "tag11",
             "tag12",
             "tag13",
             "tag14",
             "tag15",
             "tag16",
             "tag17",
             "tag18",
             "tag19",
             "tag20"]
        )
};

// 14: Many annotations (10)
@a1("v1")
@a2("v2")
@a3("v3")
@a4("v4")
@a5("v5")
@a6("v6")
@a7("v7")
@a8("v8")
@a9("v9")
@a10("v10")
permit (principal, action, resource);

// 15: Complex expression combining many operators
permit (principal, action, resource)
when
{
    (context.x + context.y * 2 - 1 > 0) &&
    (context.a || context.b || context.c) &&
    !(context.blocked) &&
    resource has owner &&
    resource.owner == principal &&
    resource.tags.contains("active") &&
    resource.tags.containsAll(["public", "approved"]) &&
    principal in Group::"editors" &&
    resource is Document in Folder::"shared" &&
    (if context.isAdmin then true else context.level >= 5)
};

// 16: Deeply qualified entity types (5 levels of namespace)
permit (principal, action, resource)
when
{ principal is Com::Example::Corp::IAM::User && resource is Com::Example::Corp::Storage::Document };

// 17: Many index accesses
permit (principal, action, resource)
when
{
    context.data["key1"] == "v1" &&
    context.data["key2"] == "v2" &&
    context.data["key3"] == "v3" &&
    context.data["key4"] == "v4" &&
    context.data["key5"] == "v5" &&
    context.data["key6"] == "v6" &&
    context.data["key7"] == "v7" &&
    context.data["key8"] == "v8" &&
    context.data["key9"] == "v9" &&
    context.data["key10"] == "v10"
};

// 18: Nested record literals
permit (principal, action, resource)
when { { outer: { middle: { inner: { deep: "value" } } } } == context.nested };

// 19: Set of sets (nested sets)
permit (principal, action, resource)
when { [[1, 2], [3, 4], [5, 6]].contains([1, 2]) };

// 20: Mixed arithmetic and comparison in complex boolean
permit (principal, action, resource)
when
{
    (context.x + 1 >= 0 && context.x - 1 <= 100) ||
    (context.y * 2 > 10 && context.y + context.z < 50) ||
    (context.a + context.b + context.c + context.d == 0)
};
