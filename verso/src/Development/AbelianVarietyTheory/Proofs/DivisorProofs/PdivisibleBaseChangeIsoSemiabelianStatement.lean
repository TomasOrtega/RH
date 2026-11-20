import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPdivisibleBaseChangeIsoSemiabelian.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.pdivisible_base_change_iso_semiabelian : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), s.IsIncl t φ κ → IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → ∀ w : 𝒜 ⟶ 𝒜.dual, IsWeilHom t t P w → ∃ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w := by
  first | exact @GlobalTheory.WeilIntegral.exists_baseChangeMap_eq_weilProj | exact GlobalTheory.WeilIntegral.exists_baseChangeMap_eq_weilProj | (intros; apply GlobalTheory.WeilIntegral.exists_baseChangeMap_eq_weilProj <;> assumption)
