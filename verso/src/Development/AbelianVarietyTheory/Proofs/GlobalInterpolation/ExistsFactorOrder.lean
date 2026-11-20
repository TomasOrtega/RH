import Mathlib

namespace GlobalTheory.FactorOrderExistence

open Filter Topology

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exists_factor_order {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ}
    (hw : w ∈ U) (hord : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
      (∀ z : ℂ, g z = (z - w) ^ analyticOrderNatAt g w * h z) ∧ h w ≠ (0 : ℂ) := by
  classical
  obtain ⟨h0, h0a, h0ne, hev⟩ := ((hg w hw).analyticOrderAt_ne_top).1 hord
  set n := analyticOrderNatAt g w with hn
  refine ⟨fun z => if z = w then h0 w else g z / (z - w) ^ n, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzw : z = w
    · subst hzw
      refine h0a.congr ?_
      filter_upwards [hev] with y hy
      by_cases hyz : y = z
      · simp [hyz]
      · have hne : (y - z) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hyz)
        simp only [hyz, if_false]
        rw [hy, smul_eq_mul, mul_div_cancel_left₀ _ hne]
    · have ha : AnalyticAt ℂ (fun y => g y / (y - w) ^ n) z :=
        (hg z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
          (pow_ne_zero _ (sub_ne_zero.2 hzw))
      refine ha.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hzw] with y hy
      simp [hy]
  · intro z
    by_cases hzw : z = w
    · subst hzw
      have := hev.self_of_nhds
      simpa using this
    · have hne : (z - w) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzw)
      simp only [hzw, if_false]
      field_simp
  · simpa using h0ne

end GlobalTheory.FactorOrderExistence
