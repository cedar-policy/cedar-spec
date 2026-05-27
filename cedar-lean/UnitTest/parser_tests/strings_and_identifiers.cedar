// String literals with various escape sequences

// Basic escapes
permit(principal, action, resource) when { context.x == "hello\nworld" };
permit(principal, action, resource) when { context.x == "tab\there" };
permit(principal, action, resource) when { context.x == "quote\"inside" };
permit(principal, action, resource) when { context.x == "back\\slash" };
permit(principal, action, resource) when { context.x == "null\0char" };
permit(principal, action, resource) when { context.x == "single\'quote" };

// Hex escapes
permit(principal, action, resource) when { context.x == "\x41\x42\x43" };
permit(principal, action, resource) when { context.x == "\x00" };
permit(principal, action, resource) when { context.x == "\x7f" };
permit(principal, action, resource) when { context.x == "\x61\x62\x63" };

// Unicode escapes
permit(principal, action, resource) when { context.x == "\u{0}" };
permit(principal, action, resource) when { context.x == "\u{41}" };
permit(principal, action, resource) when { context.x == "\u{1F600}" };
permit(principal, action, resource) when { context.x == "\u{10FFFF}" };
permit(principal, action, resource) when { context.x == "\u{61}" };
permit(principal, action, resource) when { context.x == "\u{1f4a9}" };

// Empty string
permit(principal, action, resource) when { context.x == "" };

// String with only whitespace
permit(principal, action, resource) when { context.x == "   " };

// String with mixed escapes
permit(principal, action, resource) when { context.x == "line1\nline2\ttab\x41\u{1F600}" };

// Long string
permit(principal, action, resource) when { context.x == "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789" };

// String with special characters (not needing escape)
permit(principal, action, resource) when { context.x == "!@#$%^&*()_+-=[]{}|;':,./<>?" };

// String used as record key
permit(principal, action, resource) when { context.rec["key with spaces"] == "value" };

// String in like pattern
permit(principal, action, resource) when { context.x like "hello*world" };
permit(principal, action, resource) when { context.x like "*" };
permit(principal, action, resource) when { context.x like "no wildcards here" };
permit(principal, action, resource) when { context.x like "\*literal star\*" };
permit(principal, action, resource) when { context.x like "path/to/\*/file" };

// Entity UIDs with various string contents
permit(principal == User::"", action, resource);
permit(principal == User::"alice", action, resource);
permit(principal == User::"alice bob", action, resource);
permit(principal == User::"alice\"bob", action, resource);
permit(principal == User::"alice\\bob", action, resource);
permit(principal == User::"\u{1F600}", action, resource);
permit(principal == User::"\x41\x42", action, resource);
permit(principal == User::"path/to/resource", action, resource);
permit(principal == User::"user@example.com", action, resource);
permit(principal == User::"123-456-789", action, resource);

// Namespaced entity UIDs
permit(principal == App::User::"alice", action, resource);
permit(principal == Com::Example::App::User::"alice", action, resource);
permit(principal == A::B::C::D::E::"deep", action, resource);

// Identifiers as field names
permit(principal, action, resource) when { resource.owner == principal };
permit(principal, action, resource) when { resource.camelCase == "x" };
permit(principal, action, resource) when { resource.snake_case == "x" };
permit(principal, action, resource) when { resource.MixedCase == "x" };
permit(principal, action, resource) when { resource._leading_underscore == "x" };
permit(principal, action, resource) when { resource.x123 == "x" };
permit(principal, action, resource) when { resource.a == "x" };
permit(principal, action, resource) when { resource.ALLCAPS == "x" };

// Identifiers as entity type names
permit(principal is User, action, resource);
permit(principal is CamelCaseType, action, resource);
permit(principal is Snake_Case_Type, action, resource);
permit(principal is A, action, resource);
permit(principal is ALLCAPS, action, resource);
permit(principal is Type123, action, resource);
permit(principal is _LeadingUnderscore, action, resource);

// Namespaced type names in is
permit(principal, action, resource) when { resource is App::Document };
permit(principal, action, resource) when { resource is Com::Example::Resource };

// has with string literal (for non-identifier attribute names)
permit(principal, action, resource) when { context has "spaces in name" };
permit(principal, action, resource) when { context has "123startsWithNum" };
permit(principal, action, resource) when { context has "" };
permit(principal, action, resource) when { context has "special!@#" };

// Record literal with string keys containing special chars
permit(principal, action, resource) when { {"key with spaces": 1, "123num": 2} == context.x };
