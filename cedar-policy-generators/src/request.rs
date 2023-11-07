use crate::collections::HashMap;
use crate::hierarchy::Hierarchy;
use arbitrary::Unstructured;
use cedar_policy_core::ast::{self, EntityUID, RestrictedExpr};
use cedar_policy_core::extensions::Extensions;
use smol_str::SmolStr;

/// Data structure representing an authorization request
#[derive(Debug, Clone)]
pub struct Request {
    /// Principal
    pub principal: EntityUID,
    /// Action
    pub action: EntityUID,
    /// Resource
    pub resource: EntityUID,
    /// Context
    pub context: HashMap<SmolStr, RestrictedExpr>,
}

impl Request {
    /// Generate an arbitrary Request, based on the given `Hierarchy` (but no
    /// schema)
    pub fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        context: HashMap<SmolStr, RestrictedExpr>,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        Ok(Self {
            principal: hierarchy.arbitrary_uid(u)?,
            action: hierarchy.arbitrary_uid(u)?,
            resource: hierarchy.arbitrary_uid(u)?,
            context,
        })
    }
}

impl From<Request> for ast::Request {
    fn from(req: Request) -> ast::Request {
        ast::Request::new(
            req.principal,
            req.action,
            req.resource,
            ast::Context::from_pairs(req.context)
                .expect("can't have duplicate keys because `req.context` was already a HashMap"),
            None::<&ast::RequestSchemaAllPass>,
            Extensions::none(),
        )
        .expect("we aren't doing request validation here, so new() can't fail")
    }
}

impl std::fmt::Display for Request {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(principal : {}, action: {}, resource: {})",
            self.principal, self.action, self.resource
        )?;
        if !self.context.is_empty() {
            writeln!(f, "\nWith context: {{")?;
            for (attr, val) in self.context.iter() {
                writeln!(f, "{attr} : {val},")?;
            }
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}
