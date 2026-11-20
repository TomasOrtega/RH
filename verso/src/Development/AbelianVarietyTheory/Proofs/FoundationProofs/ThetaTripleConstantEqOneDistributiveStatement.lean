import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaTripleConstantEqOneDistributive.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_one_distributive : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  first | exact @GlobalTheory.DistTriple.const_eq_one | exact GlobalTheory.DistTriple.const_eq_one | (intros; apply GlobalTheory.DistTriple.const_eq_one <;> assumption)
