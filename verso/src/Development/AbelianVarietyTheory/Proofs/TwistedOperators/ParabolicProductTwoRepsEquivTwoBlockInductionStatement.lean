import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FParabolicProductTwoRepsEquivTwoBlockInduction.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.parabolicProductTwoReps_equiv_two_block_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) := by
  first | exact @GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | exact GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | (intros; apply GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd <;> assumption)
