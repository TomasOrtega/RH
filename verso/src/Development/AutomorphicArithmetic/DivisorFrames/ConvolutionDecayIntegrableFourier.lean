import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_` and prove the remaining obligations. Unfold `pr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (norm_le_pi_norm v _) (norm_le_pi_norm η _) (norm_nonneg _) (norm_nonneg _)`.

Use `_ = _ := by simp; ring`.
-/
private theorem norm_pr_le {ι : Type} [Fintype ι] {n : ℕ} (v η : Fin n × ι → ℂ) :
    ‖pr v η‖ ≤ n * ‖η‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
  unfold pr
  calc _ ≤ ∑ i : Fin n, ‖v (i, w) * η (i, w)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * ‖η‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm v _) (norm_le_pi_norm η _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/- English proof (translation)
Unfold `pr`. Use `fun_prop`.
-/
private theorem continuous_pr {ι : Type} [Fintype ι] {n : ℕ} (η : Fin n × ι → ℂ) :
    Continuous fun v : Fin n × ι → ℂ => pr v η := by
  unfold pr
  fun_prop

/- English proof (translation)
Use `set D : ℕ := Module.finrank ℝ (ι → ℂ) + 1 with hD`. Take `⟨C, hC⟩` from `hd (K + D)`. Establish `hC0 : 0 ≤ C`. Use `(norm_nonneg _).trans (hC 0)` as an intermediate fact. Simplify using `using this`.

Use `set A : ℝ := 1 + n * ‖η‖ with hA`. Establish `h1 : Integrable (fun s : ι → ℂ => (1 + ‖s‖) ^ (-(D : ℝ)))` using `integrable_one_add_norm (by rw [hD]; push_cast; linarith)`. Establish `h2` using `((hi (K + D)).const_mul (C * A ^ (K + D))).mul_prod h1`. Use `h2.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `AEStronglyMeasurable.mul ?_ (hg.comp measurable_snd).aestronglyMeasurable` and prove the remaining obligations.

Conclude with `((hh.comp continuous_fst).mul (hφ.comp (continuous_snd.add ((continuous_pr η).comp continuous_fst)))).aestronglyMeasurable`. Take `⟨v, s⟩` from `p`. Simplify using `only`. Rewrite using `[norm_mul, norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]`. Establish `e1 : 1 + ‖s‖ ≤ (1 + ‖s + pr v η‖) * (A * (1 + ‖v‖))`.

Establish `a1 : ‖s‖ ≤ ‖s + pr v η‖ + ‖pr v η‖`. Use `norm_sub_le (s + pr v η) (pr v η)` as an intermediate fact. Simplify using `using this`. Establish `a2` using `norm_pr_le v η`. Establish `a3 : 0 ≤ (n : ℝ) * ‖η‖` using `by positivity`.

Establish `a4 : 1 + ‖pr v η‖ ≤ A * (1 + ‖v‖)`. Rewrite using `[hA]`. Use polynomial arithmetic with `[norm_nonneg v]`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg (norm_nonneg (s + pr v η)) (norm_nonneg (pr v η))]`.

Use `_ ≤ _ := by gcongr`. Establish `e2 : (1 + ‖s‖) ^ (K + D) ≤ (1 + ‖s + pr v η‖) ^ (K + D) * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D))`. Rewrite using `[← mul_pow, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) e1 _`. Establish `e3 : ‖φ (s + pr v η)‖ ≤ C * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D)) / (1 + ‖s‖) ^ (K + D)`.

Use `(hC _).trans ?_` and prove the remaining obligations. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Conclude with `hK s`.

Use `_ = _ := by`. Rewrite using `[pow_add (1 + ‖s‖)]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem int_prod {ι : Type} [Fintype ι] {n : ℕ} (η : Fin n × ι → ℂ) (φ : (ι → ℂ) → ℂ) (hφ : Continuous φ)
    (hd : ∀ N : ℕ, ∃ C : ℝ, ∀ s, ‖φ s‖ ≤ C / (1 + ‖s‖) ^ N)
    (h : (Fin n × ι → ℂ) → ℂ) (hh : Continuous h) (hi : ∀ N : ℕ, Integrable fun v => (1 + ‖v‖) ^ N * ‖h v‖)
    (g : (ι → ℂ) → ℂ) (hg : Measurable g) (K : ℕ) (hK : ∀ s, ‖g s‖ ≤ (1 + ‖s‖) ^ K) :
    Integrable (fun p : (Fin n × ι → ℂ) × (ι → ℂ) => h p.1 * φ (p.2 + pr p.1 η) * g p.2) (volume.prod volume) := by
  set D : ℕ := Module.finrank ℝ (ι → ℂ) + 1 with hD
  obtain ⟨C, hC⟩ := hd (K + D)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  set A : ℝ := 1 + n * ‖η‖ with hA
  have h1 : Integrable (fun s : ι → ℂ => (1 + ‖s‖) ^ (-(D : ℝ))) :=
    integrable_one_add_norm (by rw [hD]; push_cast; linarith)
  have h2 := ((hi (K + D)).const_mul (C * A ^ (K + D))).mul_prod h1
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · refine AEStronglyMeasurable.mul ?_ (hg.comp measurable_snd).aestronglyMeasurable
    exact ((hh.comp continuous_fst).mul
      (hφ.comp (continuous_snd.add ((continuous_pr η).comp continuous_fst)))).aestronglyMeasurable
  · obtain ⟨v, s⟩ := p
    simp only
    rw [norm_mul, norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
    have e1 : 1 + ‖s‖ ≤ (1 + ‖s + pr v η‖) * (A * (1 + ‖v‖)) := by
      have a1 : ‖s‖ ≤ ‖s + pr v η‖ + ‖pr v η‖ := by
        have := norm_sub_le (s + pr v η) (pr v η)
        simpa using this
      have a2 := norm_pr_le v η
      have a3 : 0 ≤ (n : ℝ) * ‖η‖ := by positivity
      have a4 : 1 + ‖pr v η‖ ≤ A * (1 + ‖v‖) := by
        rw [hA]; nlinarith [norm_nonneg v]
      calc 1 + ‖s‖ ≤ (1 + ‖s + pr v η‖) * (1 + ‖pr v η‖) := by
            nlinarith [mul_nonneg (norm_nonneg (s + pr v η)) (norm_nonneg (pr v η))]
        _ ≤ _ := by gcongr
    have e2 : (1 + ‖s‖) ^ (K + D) ≤ (1 + ‖s + pr v η‖) ^ (K + D) * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D)) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) e1 _
    have e3 : ‖φ (s + pr v η)‖ ≤ C * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D)) / (1 + ‖s‖) ^ (K + D) := by
      refine (hC _).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc _ ≤ C * ((1 + ‖s + pr v η‖) ^ (K + D) * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D))) := by gcongr
        _ = _ := by ring
    calc _ ≤ ‖h v‖ * (C * (A ^ (K + D) * (1 + ‖v‖) ^ (K + D)) / (1 + ‖s‖) ^ (K + D)) * (1 + ‖s‖) ^ K := by
          gcongr
          exact hK s
      _ = _ := by
          rw [pow_add (1 + ‖s‖)]
          field_simp

/- English proof (translation)
Introduce `ι _ n κ e η φ hφ hd h hh hi`. Establish `key` using `int_prod η φ hφ hd h hh hi`. Use `⟨?_, ?_, fun y => ?_⟩` and prove the remaining obligations. Use `(key (fun _ => 1) measurable_const 0 (by simp)).integral_prod_right` as an intermediate fact. Simplify using `using this`.

Use `(key (wt κ e) (measurable_wt κ e) _ (norm_wt_le κ e)).integral_prod_right` as an intermediate fact. Simplify `this` using `only [integral_mul_const]`. Establish `hm : Measurable fun s : ι → ℂ => ec (s * y)` using `(continuous_ec.comp (continuous_id.mul continuous_const)).measurable`. Establish `k` using `key (fun s => ec (s * y)) hm 0 (by simp [norm_ec])`. Unfold `FT`.

Simplify using `only [← integral_mul_const]`. Rewrite using `[← integral_integral_swap (f := fun v s => h v * φ (s + pr v η) * ec (s * y)) k]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_const_mul, ← integral_add_right_eq_self (fun s => h v * ec (v * -sc y η) * (φ s * ec (s * y))) (pr v η)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only`. Establish `e1 : ec (v * -sc y η) * ec ((s + pr v η) * y) = ec (s * y)`. Unfold `ec`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← Complex.add_re]`.

Use `congr 4`. Simplify using `only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, pr, sc, mul_neg, Finset.sum_neg_distrib, Fintype.sum_prod_type_right, Finset.sum_mul]`. Establish `: ∑ w, ∑ i, v (i, w) * (y w * η (i, w)) = ∑ w, ∑ i, v (i, w) * η (i, w) * y w` using `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.convolution_decay_integrable_fourier :
    ∀ {ι : Type} [Fintype ι] {n : ℕ} (κ : ι → ℤ) (e : ℕ) (η : Fin n × ι → ℂ) (φ : (ι → ℂ) → ℂ), Continuous φ →
        (∀ N : ℕ, ∃ C : ℝ, ∀ s, ‖φ s‖ ≤ C / (1 + ‖s‖) ^ N) →
        ∀ h : (Fin n × ι → ℂ) → ℂ, Continuous h → (∀ N : ℕ, Integrable fun v => (1 + ‖v‖) ^ N * ‖h v‖) →
        Integrable (fun s => ∫ v, h v * φ (s + pr v η)) ∧ Integrable (fun s => (∫ v, h v * φ (s + pr v η)) * wt κ e s) ∧
          ∀ y, FT (fun s => ∫ v, h v * φ (s + pr v η)) y = FT h (-sc y η) * FT φ y := by
  intro ι _ n κ e η φ hφ hd h hh hi
  have key := int_prod η φ hφ hd h hh hi
  refine ⟨?_, ?_, fun y => ?_⟩
  · have := (key (fun _ => 1) measurable_const 0 (by simp)).integral_prod_right
    simpa using this
  · have := (key (wt κ e) (measurable_wt κ e) _ (norm_wt_le κ e)).integral_prod_right
    simpa only [integral_mul_const] using this
  · have hm : Measurable fun s : ι → ℂ => ec (s * y) :=
      (continuous_ec.comp (continuous_id.mul continuous_const)).measurable
    have k := key (fun s => ec (s * y)) hm 0 (by simp [norm_ec])
    unfold FT
    simp only [← integral_mul_const]
    rw [← integral_integral_swap (f := fun v s => h v * φ (s + pr v η) * ec (s * y)) k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (fun s => h v * ec (v * -sc y η) * (φ s * ec (s * y))) (pr v η)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only
    have e1 : ec (v * -sc y η) * ec ((s + pr v η) * y) = ec (s * y) := by
      unfold ec
      rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← Complex.add_re]
      congr 4
      simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, pr, sc, mul_neg,
        Finset.sum_neg_distrib, Fintype.sum_prod_type_right, Finset.sum_mul]
      have : ∑ w, ∑ i, v (i, w) * (y w * η (i, w)) = ∑ w, ∑ i, v (i, w) * η (i, w) * y w :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => by ring
      rw [this]; ring
    rw [← e1]; ring
