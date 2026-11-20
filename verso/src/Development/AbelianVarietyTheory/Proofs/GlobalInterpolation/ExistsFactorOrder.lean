import Mathlib

namespace GlobalTheory.FactorOrderExistence

open Filter Topology

/- English proof (translation)
Take `⟨h0, h0a, h0ne, hev⟩` from `((hg w hw).analyticOrderAt_ne_top).1 hord`. Use `set n := analyticOrderNatAt g w with hn`. Use `⟨fun z => if z = w then h0 w else g z / (z - w) ^ n, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Distinguish the cases in `hzw : z = w`.

Substitute `hzw` using the available equality. Use `h0a.congr ?_` and prove the remaining obligations. Use `filter_upwards [hev] with y hy`. Distinguish the cases in `hyz : y = z`. Simplify using `[hyz]`.

Establish `hne : (y - z) ^ n ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 hyz)`. Simplify using `only [hyz, if_false]`. Rewrite using `[hy, smul_eq_mul, mul_div_cancel_left₀ _ hne]`. Establish `ha : AnalyticAt ℂ (fun y => g y / (y - w) ^ n) z` using `(hg z hz).div ((analyticAt_id.sub analyticAt_const).pow n) (pow_ne_zero _ (sub_ne_zero.2 hzw))`. Use `ha.congr ?_` and prove the remaining obligations.

Use `filter_upwards [isOpen_ne.mem_nhds hzw] with y hy`. Simplify using `[hy]`. Introduce `z`. Distinguish the cases in `hzw : z = w`. Substitute `hzw` using the available equality.

Use `hev.self_of_nhds` as an intermediate fact. Simplify using `using this`. Establish `hne : (z - w) ^ n ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 hzw)`. Simplify using `only [hzw, if_false]`. Clear the denominators using the available nonvanishing facts.

Simplify using `using h0ne`.
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
