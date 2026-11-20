import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTameIwahoriEigenvectorJacquetQuotientNeZero.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
