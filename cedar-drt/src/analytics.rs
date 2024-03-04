use std::collections::HashSet;
use std::sync::Arc;
use std::{collections::HashMap, sync::mpsc};

use cedar_policy_core::ast::Expr;
use cedar_policy_core::ast::Policy;
use rayon::prelude::*;

pub enum AnalyticOutput {
    NumericDistribution(HashMap<usize, usize>),
    BucketDistributiuon {
        dist: HashMap<String, usize>,
        universe: HashSet<String>,
    },
}

trait StatefulAnalytic {
    fn process(self, p: &Policy) -> Self;
    fn get_state(self) -> AnalyticOutput;
}

#[derive(Debug, Clone)]
struct NumericAnalytic<F> {
    f: F,
    dist: HashMap<usize, usize>,
}

impl<F> NumericAnalytic<F> {
    pub fn new(f: F) -> Self {
        Self {
            f,
            dist: HashMap::default(),
        }
    }
}

impl<F> StatefulAnalytic for NumericAnalytic<F>
where
    F: Fn(&Policy) -> usize,
{
    fn process(self, p: &Policy) -> Self {
        todo!()
    }

    fn get_state(self) -> AnalyticOutput {
        AnalyticOutput::NumericDistribution(self.dist)
    }
}
