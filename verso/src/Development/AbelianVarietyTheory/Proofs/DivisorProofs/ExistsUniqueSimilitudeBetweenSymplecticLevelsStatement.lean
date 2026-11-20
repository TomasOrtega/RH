import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTSympCover.sympCond_fibre_existsUnique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniqueSimilitudeBetweenSymplecticLevels.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.existsUnique_similitude_between_symplecticLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  first | exact @GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | exact GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | (intros; apply GlobalTheory.HTSympCover.sympCond_fibre_existsUnique <;> assumption)
