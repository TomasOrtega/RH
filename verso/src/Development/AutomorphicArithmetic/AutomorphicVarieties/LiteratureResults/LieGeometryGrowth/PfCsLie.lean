import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
open UpperTheory.V.Lit.Geo GlobalTheory.CuspRep Filter Topology

/- English proof (translation)
Introduce `E _ _ _ a φ X ⟨R, hR⟩`. Take `⟨c, c0, -, ccont, cder, -⟩` from `UpperTheory.V.Lit.Bor.oneParam E a X`. Take `⟨h1, -, h3, -⟩` from `qhtFacts E a`. Take `⟨B, hB⟩` from `h3 _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image ccont.inv)`. Use `⟨B * R, fun g hg => ?_⟩` and prove the remaining obligations.

Establish `hd` using `GlobalTheory.CuspRep.hasDerivAt_curve φ g c X c0 cder`. Establish `hz : (fun t : ℝ => φ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ)` using `by filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht`. Use `hR _ (not_le.1 fun hle => ?_)` and prove the remaining obligations. Establish `h` using `hB (g * infGL E a (c t)) _ ⟨t, ht, rfl⟩`. Simplify using `only [Pi.inv_apply, mul_inv_cancel_right] at h`.

Establish `hp` using `h1 (g * infGL E a (c t))`. Establish `hg1` using `h1 g`. Establish `hB0 : 0 ≤ B`. Assume the negation of the conclusion as `hn`. Use polynomial arithmetic with `[not_le.1 hn]`.

Conclude with `absurd (h.trans (mul_le_mul_of_nonneg_left hle hB0)) (not_le.2 hg)`. Conclude with `hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.csLie :
    UpperTheory.V.Lit.Geo.Pf.CsLie := by
  intro E _ _ _ a φ X ⟨R, hR⟩
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  obtain ⟨h1, -, h3, -⟩ := qhtFacts E a
  obtain ⟨B, hB⟩ := h3 _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image ccont.inv)
  refine ⟨B * R, fun g hg => ?_⟩
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve φ g c X c0 cder
  have hz : (fun t : ℝ => φ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine hR _ (not_le.1 fun hle => ?_)
    have h := hB (g * infGL E a (c t)) _ ⟨t, ht, rfl⟩
    simp only [Pi.inv_apply, mul_inv_cancel_right] at h
    have hp := h1 (g * infGL E a (c t))
    have hg1 := h1 g
    have hB0 : 0 ≤ B := by
      by_contra hn
      nlinarith [not_le.1 hn]
    exact absurd (h.trans (mul_le_mul_of_nonneg_left hle hB0)) (not_le.2 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)
