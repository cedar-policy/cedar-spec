use cedar_policy_core::ast::Expr;
use cedar_policy_core::est;
use serde::Serialize;
use serde::Serializer;

pub fn expr_to_est<S: Serializer>(e: &Expr, s: S) -> Result<S::Ok, S::Error> {
    let est: est::Expr = e.clone().into();
    est.serialize(s)
}
