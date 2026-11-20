import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMumfordTensorDataFactorInclusionProjectionProps.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r), IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧ ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  first | exact @GlobalTheory.Mum.tens_inc_pr_facts | exact GlobalTheory.Mum.tens_inc_pr_facts | (intros; apply GlobalTheory.Mum.tens_inc_pr_facts <;> assumption)
