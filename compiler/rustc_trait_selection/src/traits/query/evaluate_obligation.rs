use crate::infer::canonical::OriginalQueryValues;
use crate::infer::InferCtxt;
use crate::traits::{
    EvaluationResult, OverflowError, PredicateObligation,
};

pub trait InferCtxtExt<'tcx> {
    fn predicate_may_hold(&self, obligation: &PredicateObligation<'tcx>) -> Result<bool, OverflowError>;

    fn predicate_must_hold_considering_regions(
        &self,
        obligation: &PredicateObligation<'tcx>,
    ) -> Result<bool, OverflowError>;

    fn predicate_must_hold_modulo_regions(&self, obligation: &PredicateObligation<'tcx>) -> Result<bool, OverflowError>;

    fn evaluate_obligation(
        &self,
        obligation: &PredicateObligation<'tcx>,
    ) -> Result<EvaluationResult, OverflowError>;
}

impl<'cx, 'tcx> InferCtxtExt<'tcx> for InferCtxt<'cx, 'tcx> {
    /// Evaluates whether the predicate can be satisfied (by any means)
    /// in the given `ParamEnv`.
    fn predicate_may_hold(&self, obligation: &PredicateObligation<'tcx>) -> Result<bool, OverflowError> {
        Ok(self.evaluate_obligation(obligation)?.may_apply())
    }

    /// Evaluates whether the predicate can be satisfied in the given
    /// `ParamEnv`, and returns `false` if not certain. However, this is
    /// not entirely accurate if inference variables are involved.
    ///
    /// This version may conservatively fail when outlives obligations
    /// are required.
    fn predicate_must_hold_considering_regions(
        &self,
        obligation: &PredicateObligation<'tcx>,
    ) -> Result<bool, OverflowError> {
        Ok(self.evaluate_obligation(obligation)?.must_apply_considering_regions())
    }

    /// Evaluates whether the predicate can be satisfied in the given
    /// `ParamEnv`, and returns `false` if not certain. However, this is
    /// not entirely accurate if inference variables are involved.
    ///
    /// This version ignores all outlives constraints.
    fn predicate_must_hold_modulo_regions(&self, obligation: &PredicateObligation<'tcx>) -> Result<bool, OverflowError> {
        Ok(self.evaluate_obligation(obligation)?.must_apply_modulo_regions())
    }

    /// Evaluate a given predicate, capturing overflow and propagating it back.
    fn evaluate_obligation(
        &self,
        obligation: &PredicateObligation<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        let mut _orig_values = OriginalQueryValues::default();
        let c_pred = self
            .canonicalize_query(obligation.param_env.and(obligation.predicate), &mut _orig_values);
        // Run canonical query. If overflow occurs, rerun from scratch but this time
        // in standard trait query mode so that overflow is handled appropriately
        // within `SelectionContext`.
        self.tcx.evaluate_obligation(c_pred)
    }
}
