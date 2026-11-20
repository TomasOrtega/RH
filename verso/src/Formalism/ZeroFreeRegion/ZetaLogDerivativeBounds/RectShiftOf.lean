import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Establish `h` using `riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))`. Rewrite `h` using `[eventually_nhdsWithin_iff]`. Use `filter_upwards [h] with w hw hw1 hz`. Conclude with `hw hw1 (by rw [hz, mul_zero])`.
-/
lemma rso_zeta_ne_near_one : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  have h := riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw hw1 hz
  exact hw hw1 (by rw [hz, mul_zero])

/- English proof (translation)
Establish `hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1}` using `fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt`. Conclude with `hd.deriv isOpen_ne`.
-/
lemma rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.deriv isOpen_ne

/- English proof (translation)
Establish `hd1 : DifferentiableAt ℂ (deriv riemannZeta) w` using `rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)`. Establish `hd2 : DifferentiableAt ℂ riemannZeta w` using `differentiableAt_riemannZeta h1`. Establish `hy0 : (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Establish `hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w` using `(differentiableAt_id).const_cpow (Or.inl hy0)`. Establish `hden : w * (w - 1) ≠ 0` using `mul_ne_zero h0 (sub_ne_zero.2 h1)`.

Unfold `Fy`. Conclude with `(((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden`.
-/
lemma rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) w :=
    rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)
  have hd2 : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta h1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w :=
    (differentiableAt_id).const_cpow (Or.inl hy0)
  have hden : w * (w - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  unfold Fy
  exact (((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden

/- English proof (translation)
Introduce `hRDP hLA y hy σ₁ σ₀ T h1 h2 h3 hT hz`. Take `⟨A, hA1, hAev⟩` from `hLA y hy`. Use `set a : ℂ := (y : ℂ) with ha`. Use `set b : ℂ := (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y with hb`. Set `H : ℂ → ℂ` to `fun w => Fy y w - a / (w - 1) ^ 2 - b / (w - 1)`.

Set `G : ℂ → ℂ` to `fun w => if w = 1 then A 1 else H w`. Establish `hH : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ H z`. Introduce `z hz0 hz1 hzz`. Establish `hzm : z - 1 ≠ 0` using `sub_ne_zero.2 hz1`. Conclude with `((rso_Fy_diff y hy hz0 hz1 hzz).sub ((differentiableAt_const a).div ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 hzm))).sub ((differentiableAt_const b).div (differentiableAt_id.sub_const 1) hzm)`.

Establish `hG : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ G z`. Introduce `z hz0 hz1 hzz`. Use `(hH z hz0 hz1 hzz).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [isOpen_ne.mem_nhds hz1] with w hw`. Simplify using `[G, hw]`.

Establish `hev` using `hAev`. Rewrite `hev` using `[eventually_nhdsWithin_iff]`. Establish `hG1 : DifferentiableAt ℂ G 1`. Use `hA1.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with w hw`.

Distinguish the cases in `hw1 : w = 1`. Substitute `hw1` using the available equality. Simplify using `[G]`. Establish `hw'` using `hw hw1`. Simplify using `only [G, H, if_neg hw1]`.

Rewrite using `[hw']`. Expand and normalize the polynomial expressions, which then agree. Use `set U : Set ℂ := {w | ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z} with hU`. Establish `hUo : IsOpen U` using `isOpen_setOf_eventually_nhds`. Establish `hUd : DifferentiableOn ℂ G U` using `fun w hw => (hw.self_of_nhds).differentiableWithinAt`.

Establish `h01 : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0` using `eventually_ne_nhds one_ne_zero`. Establish `hsub : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U`. Introduce `w hw`. Rewrite `hw` using `[Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]`. Take `⟨⟨hr1, hr2⟩, hi1, hi2⟩` from `hw`.

Establish `hw0 : w ≠ 0`. Introduce `h`. Rewrite `hr1` using `[h]`. Simplify using `at hr1`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hw1 : w = 1`. Substitute `hw1 show ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ G z filter_upwards [rso_zeta_ne_near_one, h01] with z hz1 hz0` using the available equality. Distinguish the cases in `hz1' : z = 1`. Substitute `hz1'` using the available equality. Conclude with `hG1`.

Conclude with `hG z hz0 hz1' (hz1 hz1')`. Establish `hzw : riemannZeta w ≠ 0` using `hz w hr1 hr2 (abs_le.2 ⟨hi1, hi2⟩) hw1`. Establish `hc : ContinuousAt riemannZeta w` using `(differentiableAt_riemannZeta hw1).continuousAt`. Use `show ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z`. Use `filter_upwards [hc.eventually_ne hzw, isOpen_ne.mem_nhds hw1, isOpen_ne.mem_nhds hw0] with z hzz hz1 hz0`.

Conclude with `hG z hz0 hz1 hzz`. Use `hRDP (Fy y) G a b 1 σ₁ σ₀ (-T) T (by simpa using h2) (by simpa using h3) (by simp; linarith) (by simpa using hT) ⟨U, hUo, hsub, hUd⟩ ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [G, H, if_neg hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rectangleShiftOfResidue : RectShiftOf := by
  intro hRDP hLA y hy σ₁ σ₀ T h1 h2 h3 hT hz
  obtain ⟨A, hA1, hAev⟩ := hLA y hy
  set a : ℂ := (y : ℂ) with ha
  set b : ℂ := (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y with hb
  let H : ℂ → ℂ := fun w => Fy y w - a / (w - 1) ^ 2 - b / (w - 1)
  let G : ℂ → ℂ := fun w => if w = 1 then A 1 else H w
  have hH : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ H z := by
    intro z hz0 hz1 hzz
    have hzm : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    exact ((rso_Fy_diff y hy hz0 hz1 hzz).sub
      ((differentiableAt_const a).div ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 hzm))).sub
      ((differentiableAt_const b).div (differentiableAt_id.sub_const 1) hzm)
  have hG : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ G z := by
    intro z hz0 hz1 hzz
    refine (hH z hz0 hz1 hzz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    simp [G, hw]
  have hev := hAev
  rw [eventually_nhdsWithin_iff] at hev
  have hG1 : DifferentiableAt ℂ G 1 := by
    refine hA1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [G]
    · have hw' := hw hw1
      simp only [G, H, if_neg hw1]
      rw [hw']
      ring
  set U : Set ℂ := {w | ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z} with hU
  have hUo : IsOpen U := isOpen_setOf_eventually_nhds
  have hUd : DifferentiableOn ℂ G U := fun w hw => (hw.self_of_nhds).differentiableWithinAt
  have h01 : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 := eventually_ne_nhds one_ne_zero
  have hsub : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hr1; simp at hr1; linarith
    by_cases hw1 : w = 1
    · subst hw1
      show ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ G z
      filter_upwards [rso_zeta_ne_near_one, h01] with z hz1 hz0
      by_cases hz1' : z = 1
      · subst hz1'; exact hG1
      · exact hG z hz0 hz1' (hz1 hz1')
    · have hzw : riemannZeta w ≠ 0 := hz w hr1 hr2 (abs_le.2 ⟨hi1, hi2⟩) hw1
      have hc : ContinuousAt riemannZeta w := (differentiableAt_riemannZeta hw1).continuousAt
      show ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z
      filter_upwards [hc.eventually_ne hzw, isOpen_ne.mem_nhds hw1, isOpen_ne.mem_nhds hw0]
        with z hzz hz1 hz0
      exact hG z hz0 hz1 hzz
  refine hRDP (Fy y) G a b 1 σ₁ σ₀ (-T) T (by simpa using h2) (by simpa using h3)
    (by simp; linarith) (by simpa using hT) ⟨U, hUo, hsub, hUd⟩ ?_
  intro w hw
  simp only [G, H, if_neg hw]
  ring

end Formalism.ZF
