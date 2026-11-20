import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperHalfPlane

/- English proof (translation)
Introduce `hF hB hW L _ G hG s hs v v'`. Take `⟨hGc, C0, hC0⟩` from `hG`. Establish `hs' : s ∈ Icc (1 : ℝ) 2` using `⟨hs.1.le, hs.2⟩`. Take `⟨h1, h2, -, -, -, h6⟩` from `hB s hs'`. Establish `hW2 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s))` using `hW.1 (2 * s) (by linarith [hs.1])`.

Use `set W := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s)) with hWdef`. Use `set g : (Fin 2 → ℤ) → ℍ → ℝ := fun x z => if UpperTheory.V.Af.Rs.cls L x = v' then UpperTheory.V.Af.Rs.ker s x z else 0 with hg`. Establish `hg0 : ∀ x z, 0 ≤ g x z` using `fun x z => by`. Simplify using `only [hg]`. Use `split_ifs`.

Use `exacts [h2 x z, le_rfl]`. Establish `hgle : ∀ x z, g x z ≤ UpperTheory.V.Af.Rs.ker s x z` using `fun x z => by`. Simplify using `only [hg]`. Use `split_ifs`. Use `exacts [le_rfl, h2 x z]`.

Establish `hgm : ∀ x, Measurable (g x)`. Introduce `x`. Distinguish the cases in `h : UpperTheory.V.Af.Rs.cls L x = v'`. Establish `e : g x = UpperTheory.V.Af.Rs.ker s x`. Use function extensionality and compare the values at `z`.

Simplify using `[hg, h]`. Rewrite using `[e]`. Conclude with `(h1 x).measurable`. Establish `e : g x = fun _ => 0`. Use function extensionality and compare the values at `z`.

Simplify using `[hg, h]`. Rewrite using `[e]`. Conclude with `measurable_const`. Establish `hgs : ∀ z ∈ ModularGroup.fd, Summable fun x => g x z` using `fun z hz => Summable.of_nonneg_of_le (fun x => hg0 x z) (fun x => (hgle x z).trans (h6 x z hz)) (hW2.mul_left _)`. Establish `hEq : EqOn (fun z => G v z * (((∑' x, ENNReal.ofReal (g x z)).toReal : ℝ) : ℂ)) (fun z => G v z * ((UpperTheory.V.Af.Rs.Zc L v' s z : ℝ) : ℂ)) ModularGroup.fd`.

Introduce `z hz`. Establish `e : (∑' x, ENNReal.ofReal (g x z)).toReal = UpperTheory.V.Af.Rs.Zc L v' s z`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun x => hg0 x z) (hgs z hz), ENNReal.toReal_ofReal (tsum_nonneg fun x => hg0 x z)]`. Both sides reduce to the same expression. Simplify using `only [e]`.

Use `IntegrableOn.congr_fun ?_ hEq hF.1` and prove the remaining obligations. Use `Measure.integrableOn_of_bounded (M := 8 * C0 * W) hF.2.ne ?_ ?_` and prove the remaining obligations. Conclude with `((hGc v).measurable.mul (Complex.measurable_ofReal.comp (Measurable.ennreal_toReal (Measurable.ennreal_tsum fun x => (hgm x).ennreal_ofReal)))).aestronglyMeasurable`. Use `ae_restrict_of_forall_mem hF.1 fun z hz => ?_` and prove the remaining obligations. Establish `him0 : 0 < z.im` using `z.im_pos`.

Establish `him : 1 / 2 ≤ z.im`. Use `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `e` using `hEq hz`. Simplify using `only at e`.

Rewrite using `[e]`. Establish `hZ0 : 0 ≤ UpperTheory.V.Af.Rs.Zc L v' s z` using `tsum_nonneg fun x => hg0 x z`. Establish `hZ : UpperTheory.V.Af.Rs.Zc L v' s z ≤ 4 * z.im ^ 2 * W`. Combine the equalities or inequalities in the displayed calculation. Establish `hGb` using `hC0 v z him`.

Establish `hW0 : 0 ≤ W` using `tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ0]`. Establish `hG2 : ‖G v z‖ * z.im ^ 2 ≤ 2 * C0`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (norm_nonneg (G v z)) (sq_nonneg z.im)) (sub_nonneg.mpr him)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Af.Rs.zInt :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZInt := by
  intro hF hB hW L _ G hG s hs v v'
  obtain ⟨hGc, C0, hC0⟩ := hG
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨h1, h2, -, -, -, h6⟩ := hB s hs'
  have hW2 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  set W := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s)) with hWdef
  set g : (Fin 2 → ℤ) → ℍ → ℝ := fun x z =>
    if UpperTheory.V.Af.Rs.cls L x = v' then UpperTheory.V.Af.Rs.ker s x z else 0 with hg
  have hg0 : ∀ x z, 0 ≤ g x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [h2 x z, le_rfl]
  have hgle : ∀ x z, g x z ≤ UpperTheory.V.Af.Rs.ker s x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [le_rfl, h2 x z]
  have hgm : ∀ x, Measurable (g x) := by
    intro x
    by_cases h : UpperTheory.V.Af.Rs.cls L x = v'
    · have e : g x = UpperTheory.V.Af.Rs.ker s x := by
        funext z
        simp [hg, h]
      rw [e]
      exact (h1 x).measurable
    · have e : g x = fun _ => 0 := by
        funext z
        simp [hg, h]
      rw [e]
      exact measurable_const
  have hgs : ∀ z ∈ ModularGroup.fd, Summable fun x => g x z := fun z hz =>
    Summable.of_nonneg_of_le (fun x => hg0 x z) (fun x => (hgle x z).trans (h6 x z hz))
      (hW2.mul_left _)
  have hEq : EqOn (fun z => G v z * (((∑' x, ENNReal.ofReal (g x z)).toReal : ℝ) : ℂ))
      (fun z => G v z * ((UpperTheory.V.Af.Rs.Zc L v' s z : ℝ) : ℂ)) ModularGroup.fd := by
    intro z hz
    have e : (∑' x, ENNReal.ofReal (g x z)).toReal = UpperTheory.V.Af.Rs.Zc L v' s z := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hg0 x z) (hgs z hz),
        ENNReal.toReal_ofReal (tsum_nonneg fun x => hg0 x z)]
      rfl
    simp only [e]
  refine IntegrableOn.congr_fun ?_ hEq hF.1
  refine Measure.integrableOn_of_bounded (M := 8 * C0 * W) hF.2.ne ?_ ?_
  · exact ((hGc v).measurable.mul (Complex.measurable_ofReal.comp
      (Measurable.ennreal_toReal (Measurable.ennreal_tsum fun x => (hgm x).ennreal_ofReal)))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hF.1 fun z hz => ?_
    have him0 : 0 < z.im := z.im_pos
    have him : 1 / 2 ≤ z.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith
    have e := hEq hz
    simp only at e
    rw [e]
    have hZ0 : 0 ≤ UpperTheory.V.Af.Rs.Zc L v' s z := tsum_nonneg fun x => hg0 x z
    have hZ : UpperTheory.V.Af.Rs.Zc L v' s z ≤ 4 * z.im ^ 2 * W := by
      calc UpperTheory.V.Af.Rs.Zc L v' s z = ∑' x, g x z := rfl
        _ ≤ ∑' x : Fin 2 → ℤ, 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) :=
          Summable.tsum_le_tsum (fun x => (hgle x z).trans (h6 x z hz)) (hgs z hz) (hW2.mul_left _)
        _ = 4 * z.im ^ 2 * W := tsum_mul_left
    have hGb := hC0 v z him
    have hW0 : 0 ≤ W := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ0]
    have hG2 : ‖G v z‖ * z.im ^ 2 ≤ 2 * C0 := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (G v z)) (sq_nonneg z.im)) (sub_nonneg.mpr him)]
    calc ‖G v z‖ * UpperTheory.V.Af.Rs.Zc L v' s z ≤ ‖G v z‖ * (4 * z.im ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ ≤ 8 * C0 * W := by nlinarith [mul_le_mul_of_nonneg_left hG2 hW0]
