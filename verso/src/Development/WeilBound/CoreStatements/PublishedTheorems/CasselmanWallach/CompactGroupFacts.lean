import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS Filter Topology Set

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `ψ ψ' d hmax hψ hd`. Assume the negation of the conclusion as `hneg`. Establish `hdpos : 0 < d` using `lt_of_not_ge hneg`. Establish `h0 : ψ' 0 = 0` using `hmax.hasDerivAt_eq_zero (hψ 0)`. Establish `hslope` using `hd.tendsto_slope_zero_right`.

Establish `e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0` using `nhdsWithin_le_nhds hmax`. Establish `e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0)` using `hslope (lt_mem_nhds hdpos)`. Take `⟨u, hu, hsub⟩` from `mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)`. Establish `hu0 : (0 : ℝ) < u` using `hu`. Establish `hb : u / 2 ∈ Set.Ioo (0 : ℝ) u` using `⟨by linarith, by linarith⟩`.

Take `⟨c, hc, hcslope⟩` from `exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0) (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)`. Establish `hcu : c ∈ Set.Ioo (0 : ℝ) u` using `⟨hc.1, hc.2.trans (by linarith)⟩`. Take `⟨-, hc'⟩` from `hsub hcu`. Take `⟨hbmax, -⟩` from `hsub hb`. Simplify using `only [zero_add, h0, sub_zero, smul_eq_mul] at hc'`.

Establish `hψc : 0 < ψ' c` using `(pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)`. Rewrite `hψc` using `[hcslope, sub_zero]`. Establish `hdiff : 0 < ψ (u / 2) - ψ 0`. Use `mul_pos hψc (half_pos hu0)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ (half_pos hu0).ne']`. Then use the resulting hypothesis.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem second_derivative_holds : B3 := by
  intro ψ ψ' d hmax hψ hd
  by_contra hneg
  have hdpos : 0 < d := lt_of_not_ge hneg
  have h0 : ψ' 0 = 0 := hmax.hasDerivAt_eq_zero (hψ 0)
  have hslope := hd.tendsto_slope_zero_right
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0 := nhdsWithin_le_nhds hmax
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0) := hslope (lt_mem_nhds hdpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hb : u / 2 ∈ Set.Ioo (0 : ℝ) u := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0)
    (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)
  have hcu : c ∈ Set.Ioo (0 : ℝ) u := ⟨hc.1, hc.2.trans (by linarith)⟩
  obtain ⟨-, hc'⟩ := hsub hcu
  obtain ⟨hbmax, -⟩ := hsub hb
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hc'
  have hψc : 0 < ψ' c := (pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)
  rw [hcslope, sub_zero] at hψc
  have hdiff : 0 < ψ (u / 2) - ψ 0 := by
    have := mul_pos hψc (half_pos hu0)
    rwa [div_mul_cancel₀ _ (half_pos hu0).ne'] at this
  linarith

end PositivityTheory.CW

end
