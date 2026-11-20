import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmTensorRetractOfCmDatumRankOne.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.cmTensor_retract_of_cmDatum_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  first | exact @GlobalTheory.CM.isTen_retract_of_rank_one | exact GlobalTheory.CM.isTen_retract_of_rank_one | (intros; apply GlobalTheory.CM.isTen_retract_of_rank_one <;> assumption)
