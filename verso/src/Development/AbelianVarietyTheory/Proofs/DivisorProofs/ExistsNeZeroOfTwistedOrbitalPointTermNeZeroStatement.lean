import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNeZeroOfTwistedOrbitalPointTermNeZero.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | exact GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | (intros; apply GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero <;> assumption)
