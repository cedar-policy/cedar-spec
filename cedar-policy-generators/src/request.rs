use crate::collections::HashMap;
use crate::err::Error;
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
    pub context: ast::Context,
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
            context: ast::Context::from_pairs(context, Extensions::all_available())
                .map_err(Error::ContextError)?,
        })
    }
}

impl From<Request> for ast::Request {
    fn from(req: Request) -> ast::Request {
        ast::Request::new(
            (req.principal, None),
            (req.action, None),
            (req.resource, None),
            req.context,
            None::<&ast::RequestSchemaAllPass>,
            Extensions::all_available(),
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
        let mut context = self.context.iter().unwrap().peekable();
        if context.peek().is_some() {
            writeln!(f, "\nWith context: {{")?;
            for (attr, val) in context {
                writeln!(f, "{attr} : {val},")?;
            }
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}
