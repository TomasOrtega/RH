import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetPlaneReduction
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitNormGramDetPlaneReduction.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.unitNorm_gramDet_plane_reduction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  first | exact @GlobalTheory.PlaneNormReduce.reduce | exact GlobalTheory.PlaneNormReduce.reduce | (intros; apply GlobalTheory.PlaneNormReduce.reduce <;> assumption)
