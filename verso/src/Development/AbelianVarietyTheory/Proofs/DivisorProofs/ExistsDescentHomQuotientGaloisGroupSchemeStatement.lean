import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HomDescent.exists_desc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDescentHomQuotientGaloisGroupScheme.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  first | exact @GlobalTheory.HomDescent.exists_desc | exact GlobalTheory.HomDescent.exists_desc | (intros; apply GlobalTheory.HomDescent.exists_desc; all_goals assumption)
