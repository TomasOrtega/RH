import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyThetaAfterExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaFinite.exists_finite_hasTheta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianVarietyThetaAfterExtension.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.abelian_variety_theta_after_extension : ∀ (K : Type) [Field K] (P : PPAS (Sp K)), ∃ (F : Type) (_ : Field F) (_ : Algebra K F), FiniteDimensional K F ∧ ∃ (Q : PPAS (Sp F)) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (Spec.map (CommRingCat.ofHom (algebraMap K F))) ψ ∧ Q.HasTheta := by
  first | exact @GlobalTheory.ThetaFinite.exists_finite_hasTheta | exact GlobalTheory.ThetaFinite.exists_finite_hasTheta | (intros; apply GlobalTheory.ThetaFinite.exists_finite_hasTheta <;> assumption)
