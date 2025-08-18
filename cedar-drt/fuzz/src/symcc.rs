/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use cedar_policy_symcc::{
    err::SolverError,
    solver::{Decision, Solver, WriterSolver},
};

/// An implementation of [`Solver`] that stores the SMTLib text in a buffer
/// and allows the use of the solver to take the contents of the buffer
#[derive(Debug)]
pub struct BuffSolver(WriterSolver<tokio::io::BufWriter<Vec<u8>>>);

impl BuffSolver {
    /// Create a [`BuffSolver`]
    pub fn new() -> Self {
        Self(WriterSolver::<tokio::io::BufWriter<Vec<u8>>> {
            w: tokio::io::BufWriter::new(Vec::new()),
        })
    }

    /// Obtain the contents of the buffer
    pub fn contents(&mut self) -> String {
        let buffer = self.0.w.get_mut();
        // PANIC SAFETY: contents written into the buffer should always be utf8-encoded strings
        #[allow(clippy::expect_used)]
        let ret = String::from_utf8(buffer.clone())
            .expect("Unexpected error converting Vec<u8> to String");
        buffer.clear();
        ret
    }
}

impl Solver for BuffSolver {
    fn smtlib_input(&mut self) -> &mut (dyn tokio::io::AsyncWrite + Unpin + Send) {
        self.0.smtlib_input()
    }

    async fn check_sat(&mut self) -> std::result::Result<Decision, SolverError> {
        self.0.check_sat().await
    }

    async fn get_model(&mut self) -> std::result::Result<Option<String>, SolverError> {
        self.0.get_model().await
    }
}

#[cfg(test)]
mod buff_solver_tests {
    use cedar_policy_symcc::{solver::Solver, SmtLibScript};

    #[tokio::test]
    async fn test_buff_solver() {
        let mut solver = super::BuffSolver::new();
        solver.smtlib_input().assert("false").await.unwrap();
        let decision = solver.check_sat().await.unwrap();
        assert_eq!(decision, super::Decision::Unknown);
        let model = solver.get_model().await.unwrap();
        assert!(model.is_none());
        let contents = solver.contents();
        assert_eq!(contents, "(assert false)\n(check-sat)\n(get-model)\n");
    }
}
