import Mathlib

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s` using `Set.uIcc_of_le hs.le`. Establish `hg1 : IntervalIntegrable g volume 0 s` using `(hg.mono hIcc.subset).intervalIntegrable`. Establish `hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s` using `((hg.pow 2).mono hIcc.subset).intervalIntegrable`. Take `⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s` from `⟨_, rfl⟩`. Establish `hcs : c * s = ∫ t in (0 : ℝ)..s, g t` using `by rw [hc]; exact div_mul_cancel₀ _ hs.ne'`.

Establish `h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2` using `intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)`. Establish `hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const, intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const]`.

Simplify using `only [sub_zero, smul_eq_mul] at h0`. Establish `hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t` using `by rw [← hcs]; ring`. Establish `h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2` using `by linarith`. Establish `h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t)`. Rewrite using `[← hcs]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `mul_le_mul_of_nonneg_left h1 hs.le`.
-/
theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hg1 : IntervalIntegrable g volume 0 s := (hg.mono hIcc.subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s :=
    ((hg.pow 2).mono hIcc.subset).intervalIntegrable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s := ⟨_, rfl⟩
  have hcs : c * s = ∫ t in (0 : ℝ)..s, g t := by rw [hc]; exact div_mul_cancel₀ _ hs.ne'
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)
  have hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2 := by
    funext t; ring
  rw [hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t := by rw [← hcs]; ring
  have h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2 := by linarith
  have h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t) := by
    rw [← hcs]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hs.le

/- English proof (translation)
Introduce `H _ _ _ φ φ' s hs hd hc`. Establish `hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s` using `Set.uIcc_of_le hs.le`. Establish `hφc : ContinuousOn φ (Set.Icc 0 s)` using `fun t ht => (hd t ht).continuousAt.continuousWithinAt`. Establish `hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s)` using `hc.norm`. Establish `hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s` using `(hn'.mono hIcc.subset).intervalIntegrable`.

Establish `hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s` using `((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable`. Establish `hpt : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2`. Introduce `t ht`. Establish `hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s`. Rewrite using `[Set.uIcc_of_le ht.1]`.

Conclude with `Set.Icc_subset_Icc le_rfl ht.2`. Establish `hint : IntervalIntegrable φ' volume 0 t` using `(hc.mono hsub).intervalIntegrable`. Establish `hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint`. Establish `h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖`. Rewrite using `[hftc]`.

Use `norm_sub_le (φ t) (φ t - φ 0)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖` using `intervalIntegral.norm_integral_le_integral_norm ht.1`. Establish `h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖` using `intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i`. Establish `h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖` using `by linarith`.

Use polynomial arithmetic with `[norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4), sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖), sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]`. Establish `hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤ ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2)` using `intervalIntegral.integral_mono_on hs.le intervalIntegrable_const ((hA.const_mul 2).add intervalIntegrable_const) hpt`. Rewrite `hmono` using `[intervalIntegral.integral_const, intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]`. Simplify using `only [sub_zero, smul_eq_mul] at hmono`. Establish `hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2` using `sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'`.

Establish `key : ‖φ 0‖ ^ 2 * s ≤ 2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hCS hs.le]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem sobolev_endpoint_one_variable : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp

end GlobalTheory
