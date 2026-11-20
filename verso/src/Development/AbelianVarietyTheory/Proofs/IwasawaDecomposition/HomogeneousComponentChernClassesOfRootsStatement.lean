import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomogeneousComponentChernClassesOfRoots
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GrassComp.homogeneousComponent_chernRoots` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHomogeneousComponentChernClassesOfRoots.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.homogeneousComponent_chernClassesOfRoots : ∀ {ι : Type} (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), homogeneousComponent d (chernRoots m Q) = chernRoots m (weightedHomogeneousComponent Prod.snd d Q) := by
  first | exact @GlobalTheory.GrassComp.homogeneousComponent_chernRoots | exact GlobalTheory.GrassComp.homogeneousComponent_chernRoots | (intros; apply GlobalTheory.GrassComp.homogeneousComponent_chernRoots <;> assumption)
