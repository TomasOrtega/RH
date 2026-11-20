import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTriv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BirigidHom.exists_hom_of_triv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHomOfTriv.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  first | exact @GlobalTheory.BirigidHom.exists_hom_of_triv | exact GlobalTheory.BirigidHom.exists_hom_of_triv | (intros; apply GlobalTheory.BirigidHom.exists_hom_of_triv <;> assumption)
