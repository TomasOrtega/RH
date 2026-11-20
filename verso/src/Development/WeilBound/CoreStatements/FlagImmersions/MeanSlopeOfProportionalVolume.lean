import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Introduce `II Ψ _ _ N T C rd Lval hP hV hT u g hu B hB hB0 hbad`. Establish `hfd : 0 < flagDeg u` using `(GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hu.2.1`. Take `⟨c0⟩` from `T.neC`. Establish `hv : 0 < T.vol c0` using `hP.1 c0`. Establish `hvc : ∀ c, T.vol c = T.vol c0` using `fun c => hV c c0`.

Establish `hcard : (0:ℝ) < Fintype.card T.Comp` using `by exact_mod_cast Fintype.card_pos`. Establish `hvolT : T.volT = Fintype.card T.Comp * T.vol c0`. Rewrite using `[RootTower.volT, Finset.sum_congr rfl fun c _ => hvc c]`. Simplify using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hD : (0:ℝ) < (dimFl Ψ N : ℝ) + 1` using `by positivity`.

Establish `key : (∑ c, T.slope II B c u) / Fintype.card T.Comp = T.PB II B u / (((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u))`. Establish `hs : ∀ c, T.slope II B c u = T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c0 * flagDeg u))`. Introduce `c`. Rewrite using `[RootTower.slope, hvc c]`. Rewrite using `[Finset.sum_congr rfl fun c _ => hs c, ← Finset.sum_div, RootTower.PB, RootTower.PPt, hvolT, div_div]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u)`. Rewrite using `[hvolT]`. Conclude with `mul_pos hD (mul_pos (mul_pos hcard hv) hfd)`.

Rewrite using `[key, le_div_iff₀ hpos]`. Establish `h` using `hT u g hu B hB hB0 hbad`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mean_slope_of_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  intro II Ψ _ _ N T C rd Lval hP hV hT u g hu B hB hB0 hbad
  have hfd : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hu.2.1
  obtain ⟨c0⟩ := T.neC
  have hv : 0 < T.vol c0 := hP.1 c0
  have hvc : ∀ c, T.vol c = T.vol c0 := fun c => hV c c0
  have hcard : (0:ℝ) < Fintype.card T.Comp := by exact_mod_cast Fintype.card_pos
  have hvolT : T.volT = Fintype.card T.Comp * T.vol c0 := by
    rw [RootTower.volT, Finset.sum_congr rfl fun c _ => hvc c]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : (0:ℝ) < (dimFl Ψ N : ℝ) + 1 := by positivity
  have key : (∑ c, T.slope II B c u) / Fintype.card T.Comp
      = T.PB II B u / (((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u)) := by
    have hs : ∀ c, T.slope II B c u
        = T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c0 * flagDeg u)) := by
      intro c
      rw [RootTower.slope, hvc c]
    rw [Finset.sum_congr rfl fun c _ => hs c, ← Finset.sum_div, RootTower.PB, RootTower.PPt, hvolT,
      div_div]
    congr 1
    ring
  have hpos : 0 < ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) := by
    rw [hvolT]
    exact mul_pos hD (mul_pos (mul_pos hcard hv) hfd)
  rw [key, le_div_iff₀ hpos]
  have h := hT u g hu B hB hB0 hbad
  linarith

end RootFieldNumerics
