import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SecGlue.combIn_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAffineCombinationInChartUnique.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  first | exact @GlobalTheory.SecGlue.combIn_unique | exact GlobalTheory.SecGlue.combIn_unique | (intros; apply GlobalTheory.SecGlue.combIn_unique <;> assumption)
