import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsProdAbsSubGeOnSegment
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffsStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory
namespace PowerSumSecond

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro m h; simpa using h m le_rfl (by simp)`. Consider the case `insert t T ht ih`. Introduce `m h`. Rewrite `h`, the goal using `[Finset.card_insert_of_notMem ht]`.

Establish `ha' : ∀ s ∈ T, ‖a s‖ ≤ 1` using `fun s hs => ha s (Finset.mem_insert_of_mem hs)`. Establish `h1` using `ih ha' (m + 1) (fun k h1 h2 => h k (by omega) (by omega))`. Establish `h2` using `ih ha' m (fun k h1 h2 => h k (by omega) (by omega))`. Establish `e : ∑ i, z i ^ m * ∏ s ∈ insert t T, (z i - a s) = ∑ i, z i ^ (m + 1) * ∏ s ∈ T, (z i - a s) - a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `h3 : ‖a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ ≤ 2 ^ T.card * B`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_sum_pow_mul_prod_le {ι κ : Type*} [Fintype ι] (z : ι → ℂ) (a : κ → ℂ) (B : ℝ)
    (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) :
    ∀ m : ℕ, (∀ k, m ≤ k → k ≤ m + T.card → ‖∑ i, z i ^ k‖ ≤ B) →
      ‖∑ i, z i ^ m * ∏ t ∈ T, (z i - a t)‖ ≤ 2 ^ T.card * B := by
  classical
  induction T using Finset.induction_on with
  | empty => intro m h; simpa using h m le_rfl (by simp)
  | insert t T ht ih =>
    intro m h
    rw [Finset.card_insert_of_notMem ht] at h ⊢
    have ha' : ∀ s ∈ T, ‖a s‖ ≤ 1 := fun s hs => ha s (Finset.mem_insert_of_mem hs)
    have h1 := ih ha' (m + 1) (fun k h1 h2 => h k (by omega) (by omega))
    have h2 := ih ha' m (fun k h1 h2 => h k (by omega) (by omega))
    have e : ∑ i, z i ^ m * ∏ s ∈ insert t T, (z i - a s)
        = ∑ i, z i ^ (m + 1) * ∏ s ∈ T, (z i - a s)
          - a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_insert ht]; ring
    rw [e]
    have h3 : ‖a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ ≤ 2 ^ T.card * B := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ :=
            mul_le_mul_of_nonneg_right (ha t (Finset.mem_insert_self _ _)) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 ^ T.card * B + 2 ^ T.card * B := add_le_add h1 h3
      _ = _ := by ring

/- English proof (translation)
Establish `h0 : Tendsto (fun w : ℂ => ‖w‖) (Filter.cocompact ℂ) atTop` using `tendsto_norm_cocompact_atTop`. Establish `h1 : Tendsto (fun w : ℂ => ‖w‖⁻¹) (Filter.cocompact ℂ) (𝓝 0)` using `h0.inv_tendsto_atTop`. Use `squeeze_zero_norm' ?_ h1` and prove the remaining obligations. Use `filter_upwards [h0.eventually_ge_atTop 2] with w hw`. Rewrite using `[norm_inv, norm_mul, norm_pow, norm_prod]`.

Establish `hp : 1 ≤ ∏ t ∈ T, ‖w - a t‖`. Combine the equalities or inequalities in the displayed calculation. Use `norm_sub_norm_le w (a t)` as an intermediate fact. Use `ha t ht` as an intermediate fact. Use the proof step `linarith)`.

Establish `hq : ‖w‖ ≤ ‖w‖ ^ (M + 1)` using `le_self_pow₀ (by linarith) (by omega)`. Apply `inv_anti₀ (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma tendsto_inv_prod {κ : Type*} (a : κ → ℂ) (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) (M : ℕ) :
    Tendsto (fun w : ℂ => (w ^ (M + 1) * ∏ t ∈ T, (w - a t))⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
  have h0 : Tendsto (fun w : ℂ => ‖w‖) (Filter.cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have h1 : Tendsto (fun w : ℂ => ‖w‖⁻¹) (Filter.cocompact ℂ) (𝓝 0) := h0.inv_tendsto_atTop
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [h0.eventually_ge_atTop 2] with w hw
  rw [norm_inv, norm_mul, norm_pow, norm_prod]
  have hp : 1 ≤ ∏ t ∈ T, ‖w - a t‖ := by
    calc (1 : ℝ) = ∏ t ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun t ht => by
        have := norm_sub_norm_le w (a t)
        have := ha t ht
        linarith)
  have hq : ‖w‖ ≤ ‖w‖ ^ (M + 1) := le_self_pow₀ (by linarith) (by omega)
  apply inv_anti₀ (by linarith)
  nlinarith

/- English proof (translation)
Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hM' : (0 : ℝ) ≤ M` using `by positivity`. Use `set u : ℝ := N / (2 * M + N) with hu`. Establish `hu0 : 0 ≤ u` using `by positivity`. Establish `h1 : (1 - (N : ℝ) / (2 * (M + N))) * (u + 1) = 1`.

Rewrite using `[hu]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : 1 ≤ r * Real.exp u`. Establish `hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N))`.

Rewrite using `[sub_nonneg, div_le_one (by positivity)]; linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hr0 : 0 ≤ r`. Establish `hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N))`. Rewrite using `[sub_nonneg, div_le_one (by positivity)]; linarith`.

Conclude with `hs.trans hr`. Establish `h3 : Real.exp u ^ M ≤ Real.exp 1 ^ N`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Rewrite using `[hu, mul_one, ← mul_div_assoc, div_le_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[mul_nonneg hM' hN'.le]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inv_pow_le_exp (N M : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 - (N : ℝ) / (2 * (M + N)) ≤ r) :
    1 ≤ r ^ M * Real.exp 1 ^ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  set u : ℝ := N / (2 * M + N) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : (1 - (N : ℝ) / (2 * (M + N))) * (u + 1) = 1 := by
    rw [hu]; field_simp; ring
  have h2 : 1 ≤ r * Real.exp u := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (1 : ℝ) = _ := h1.symm
      _ ≤ _ := mul_le_mul hr (Real.add_one_le_exp u) (by linarith) (hs.trans hr)
  have hr0 : 0 ≤ r := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    exact hs.trans hr
  have h3 : Real.exp u ^ M ≤ Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    rw [hu, mul_one, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hM' hN'.le]
  calc (1 : ℝ) ≤ (r * Real.exp u) ^ M := one_le_pow₀ h2
    _ = r ^ M * Real.exp u ^ M := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/- English proof (translation)
Establish `hN : 0 < N` using `i₁.pos`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hM' : (0 : ℝ) ≤ M` using `by positivity`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB (M + 1) le_rfl (by omega))`. Use `set δ : ℝ := N / (2 * (M + N)) with hδ`.

Establish `hδ0 : 0 < δ` using `by positivity`. Establish `hδ1 : δ ≤ 1 / 2`. Rewrite using `[hδ, div_le_iff₀ (by positivity)]; linarith`. Take `⟨r, hr1, hr2, hr3⟩` from `GlobalTheory.exists_prod_abs_sub_ge_on_segment N (fun i => ‖z i‖) (1 - δ) δ hδ0`. Establish `hr0 : 0 < r` using `by linarith`.

Establish `hr1' : r ≤ 1` using `by linarith`. Use `set D : ℝ := (δ / (2 * Real.exp 1)) ^ N with hD`. Establish `hD0 : 0 < D` using `by positivity`. Establish `hne : ∀ i, r ≠ ‖z i‖`. Introduce `i hi`.

Establish `: ∏ i, |r - ‖z i‖| = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set S : Finset (Fin N) := Finset.univ.filter (fun i => r < ‖z i‖) with hS`. Establish `hmemS : ∀ i, i ∈ S ↔ r < ‖z i‖` using `by simp [hS]`. Establish `hmemT : ∀ i ∈ Sᶜ, ‖z i‖ < r`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_compl, hmemS, not_lt]`. Conclude with `lt_of_le_of_ne hi (hne i).symm`. Establish `hi₁ : i₁ ∈ S`. Rewrite using `[hmemS]`.

Conclude with `lt_of_le_of_ne (h1 ▸ hr1') (hne i₁)`. Use `set e : Fin S.card ≃ S := S.equivFin.symm with he`. Use `set f : ℂ → ℂ := fun w => ∏ t ∈ Sᶜ, (w - z t) with hf`. Establish `hfne : ∀ w : ℂ, r ≤ ‖w‖ → w ^ (M + 1) * f w ≠ 0`. Introduce `w hw`.

Use `mul_ne_zero (pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun t ht h => ?_)` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hw`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hmemT t ht` as an intermediate fact.

Rewrite `h` using `[sub_eq_zero]`. Rewrite `hw` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set G : ℝ := (r ^ (M + 1) * D)⁻¹ with hG`. Take `⟨c, hc1, hc2⟩` from `GlobalTheory.T.exists_interpolation_exterior_small_coeffs S.card (fun j => z (e j)) (fun w => (w ^ (M + 1) * f w)⁻¹) r G hr0 hr1' (fun j => ⟨(hmemS _).1 (e j).2, hz _⟩) (by`.

Use `DifferentiableOn.inv ?_ (fun w hw => hfne w hw)` and prove the remaining obligations. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Simplify using `only [hf]`. Use the proof step `fun_prop)`. Use the proof step `(tendsto_inv_prod z Sᶜ (fun t _ => hz t) M)`.

Use the proof step `(by`. Introduce `w hw`. Establish `e1 : ∏ j, (w - z (e j)) = ∏ t ∈ S, (w - z t)`. Rewrite using `[Equiv.prod_comp e (fun s : S => w - z s), Finset.prod_coe_sort S (fun t => w - z t)]`. Establish `e2 : D ≤ ‖∏ t ∈ S, (w - z t)‖ * ‖f w‖`.

Rewrite using `[← norm_mul, hf]`. Simplify using `only`. Rewrite using `[Finset.prod_mul_prod_compl, norm_prod]`. Use `hr3.trans (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← hw]`.

Conclude with `abs_norm_sub_norm_le _ _`. Establish `e3 : 0 < ‖f w‖` using `norm_pos_iff.2 (right_ne_zero_of_mul (hfne w hw.ge))`. Rewrite using `[e1, norm_inv, norm_mul, norm_pow, hw, hG, inv_mul_eq_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `: 0 < r ^ (M + 1)` using `by positivity`. Use the proof step `nlinarith)`.

Establish `key : (S.card : ℂ) = ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i)`. Establish `e1 : ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i) = ∑ i, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ)`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, ← Finset.sum_add_sum_compl S]`. Establish `e2 : ∑ i ∈ Sᶜ, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) = 0`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `: f (z i) = 0` using `Finset.prod_eq_zero hi (sub_self _)`.

Simplify using `[this]`. Establish `e3 : (S.card : ℂ) = ∑ i ∈ S, (1 : ℂ)` using `by simp`. Rewrite using `[e2, add_zero]`. Use `e3.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Use `hc1 (e.symm ⟨i, hi⟩)` as an intermediate fact. Simplify using `only [Equiv.apply_symm_apply] at this`. Rewrite using `[this, mul_inv_cancel₀ (hfne _ ((hmemS i).1 hi).le)]`. Establish `hcard : S.card + Sᶜ.card = N` using `by simp`. Establish `hl : (1 : ℝ) ≤ S.card` using `by exact_mod_cast Finset.card_pos.2 ⟨i₁, hi₁⟩`.

Establish `hbound : (1 : ℝ) ≤ 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `hj` using `j.2`. Conclude with `norm_sum_pow_mul_prod_le z z B Sᶜ (fun t _ => hz t) _ (fun k h1 h2 => hB k (by omega) (by omega))`. Use `_ ≤ _ := by`. Rewrite using `[← Finset.sum_mul]`.

Conclude with `mul_le_mul_of_nonneg_right hc2 (by positivity)`. Establish `h4 : (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ N`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : r ^ M * D ≤ 4 ^ N * B`. Establish `: 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B) = (4 ^ S.card * 2 ^ Sᶜ.card * B) / (r ^ M * D)`.

Rewrite using `[hG]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hbound` using `[this, one_le_div (by positivity)]`. Conclude with `hbound.trans (mul_le_mul_of_nonneg_right h4 hB0)`.

Establish `h6` using `inv_pow_le_exp N M hN r hr1`. Establish `h7 : ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N = D / (4 ^ N * Real.exp 1 ^ N)`. Rewrite using `[hD, ← mul_pow, ← div_pow, hδ]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h7, div_le_iff₀ (by positivity)]`. Establish `h8 : 0 < Real.exp 1 ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma core (N M : ℕ) (z : Fin N → ℂ) (i₁ : Fin N) (h1 : ‖z i₁‖ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (B : ℝ) (hB : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ i, z i ^ k‖ ≤ B) :
    ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N ≤ B := by
  classical
  have hN : 0 < N := i₁.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (M + 1) le_rfl (by omega))
  set δ : ℝ := N / (2 * (M + N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.exists_prod_abs_sub_ge_on_segment N (fun i => ‖z i‖) (1 - δ) δ hδ0
  have hr0 : 0 < r := by linarith
  have hr1' : r ≤ 1 := by linarith
  set D : ℝ := (δ / (2 * Real.exp 1)) ^ N with hD
  have hD0 : 0 < D := by positivity
  have hne : ∀ i, r ≠ ‖z i‖ := by
    intro i hi
    have : ∏ i, |r - ‖z i‖| = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    linarith
  set S : Finset (Fin N) := Finset.univ.filter (fun i => r < ‖z i‖) with hS
  have hmemS : ∀ i, i ∈ S ↔ r < ‖z i‖ := by simp [hS]
  have hmemT : ∀ i ∈ Sᶜ, ‖z i‖ < r := by
    intro i hi
    rw [Finset.mem_compl, hmemS, not_lt] at hi
    exact lt_of_le_of_ne hi (hne i).symm
  have hi₁ : i₁ ∈ S := by
    rw [hmemS]; exact lt_of_le_of_ne (h1 ▸ hr1') (hne i₁)
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set f : ℂ → ℂ := fun w => ∏ t ∈ Sᶜ, (w - z t) with hf
  have hfne : ∀ w : ℂ, r ≤ ‖w‖ → w ^ (M + 1) * f w ≠ 0 := by
    intro w hw
    refine mul_ne_zero (pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun t ht h => ?_)
    · rintro rfl; simp at hw; linarith
    · have := hmemT t ht
      rw [sub_eq_zero] at h
      rw [h] at hw; linarith
  set G : ℝ := (r ^ (M + 1) * D)⁻¹ with hG
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_interpolation_exterior_small_coeffs S.card (fun j => z (e j))
    (fun w => (w ^ (M + 1) * f w)⁻¹) r G hr0 hr1'
    (fun j => ⟨(hmemS _).1 (e j).2, hz _⟩)
    (by
      refine DifferentiableOn.inv ?_ (fun w hw => hfne w hw)
      refine Differentiable.differentiableOn ?_
      simp only [hf]
      fun_prop)
    (tendsto_inv_prod z Sᶜ (fun t _ => hz t) M)
    (by
      intro w hw
      have e1 : ∏ j, (w - z (e j)) = ∏ t ∈ S, (w - z t) := by
        rw [Equiv.prod_comp e (fun s : S => w - z s), Finset.prod_coe_sort S (fun t => w - z t)]
      have e2 : D ≤ ‖∏ t ∈ S, (w - z t)‖ * ‖f w‖ := by
        rw [← norm_mul, hf]
        simp only
        rw [Finset.prod_mul_prod_compl, norm_prod]
        refine hr3.trans (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_)
        rw [← hw]; exact abs_norm_sub_norm_le _ _
      have e3 : 0 < ‖f w‖ := norm_pos_iff.2 (right_ne_zero_of_mul (hfne w hw.ge))
      rw [e1, norm_inv, norm_mul, norm_pow, hw, hG, inv_mul_eq_div, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < r ^ (M + 1) := by positivity
      nlinarith)
  have key : (S.card : ℂ) = ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i) := by
    have e1 : ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i)
        = ∑ i, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, ← Finset.sum_add_sum_compl S]
    have e2 : ∑ i ∈ Sᶜ, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : f (z i) = 0 := Finset.prod_eq_zero hi (sub_self _)
      simp [this]
    have e3 : (S.card : ℂ) = ∑ i ∈ S, (1 : ℂ) := by simp
    rw [e2, add_zero]
    refine e3.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hc1 (e.symm ⟨i, hi⟩)
    simp only [Equiv.apply_symm_apply] at this
    rw [this, mul_inv_cancel₀ (hfne _ ((hmemS i).1 hi).le)]
  have hcard : S.card + Sᶜ.card = N := by simp
  have hl : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 ⟨i₁, hi₁⟩
  have hbound : (1 : ℝ) ≤ 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B) := by
    calc (1 : ℝ) ≤ ‖(S.card : ℂ)‖ := by simpa using hl
      _ ≤ ∑ j, ‖c j‖ * (2 ^ Sᶜ.card * B) := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hj := j.2
        exact norm_sum_pow_mul_prod_le z z B Sᶜ (fun t _ => hz t) _
          (fun k h1 h2 => hB k (by omega) (by omega))
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have h4 : (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ N := by
    calc (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ S.card * 4 ^ Sᶜ.card := by gcongr; norm_num
      _ = 4 ^ N := by rw [← pow_add, hcard]
  have h5 : r ^ M * D ≤ 4 ^ N * B := by
    have : 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B)
        = (4 ^ S.card * 2 ^ Sᶜ.card * B) / (r ^ M * D) := by
      rw [hG]; field_simp; ring
    rw [this, one_le_div (by positivity)] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right h4 hB0)
  have h6 := inv_pow_le_exp N M hN r hr1
  have h7 : ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N = D / (4 ^ N * Real.exp 1 ^ N) := by
    rw [hD, ← mul_pow, ← div_pow, hδ]
    congr 1
    field_simp
    ring
  rw [h7, div_le_iff₀ (by positivity)]
  have h8 : 0 < Real.exp 1 ^ N := by positivity
  calc D ≤ (r ^ M * Real.exp 1 ^ N) * D := le_mul_of_one_le_left hD0.le h6
    _ = (r ^ M * D) * Real.exp 1 ^ N := by ring
    _ ≤ (4 ^ N * B) * Real.exp 1 ^ N := mul_le_mul_of_nonneg_right h5 h8.le
    _ = _ := by ring

end PowerSumSecond

open PowerSumSecond in

/- English proof (translation)
Use `⟨16 * Real.exp 1 ^ 2, ?_, fun N M z i₀ => ?_⟩` and prove the remaining obligations. Establish `: 1 ≤ Real.exp 1 ^ 2` using `one_le_pow₀ (Real.one_le_exp zero_le_one)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN : 0 < N` using `i₀.pos`. Take `⟨i₁, -, hi₁⟩` from `Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩`.

Distinguish the cases in `h0 : z i₁ = 0`. Use `⟨M + 1, le_rfl, by omega, ?_⟩` and prove the remaining obligations. Establish `: ‖z i₀‖ = 0` using `le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)`. Rewrite using `[this, zero_pow (by omega), mul_zero]`. Conclude with `norm_nonneg _`.

Establish `hR : 0 < ‖z i₁‖` using `norm_pos_iff.2 h0`. Take `⟨k, hk, hk'⟩` from `Finset.exists_max_image (Finset.Icc (M + 1) (M + N)) (fun k => ‖∑ i, (z i / z i₁) ^ k‖) ⟨M + 1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩`. Rewrite `hk` using `[Finset.mem_Icc]`. Use `⟨k, hk.1, hk.2, ?_⟩` and prove the remaining obligations. Establish `hc` using `core N M (fun i => z i / z i₁) i₁ (by simp [h0]) (fun i => by`.

Rewrite using `[norm_div, div_le_one hR]`. Conclude with `hi₁ i (Finset.mem_univ _))`. Use `_ (fun j h1 h2 => hk' j (Finset.mem_Icc.2 ⟨h1, h2⟩))`. Simplify using `only [div_pow] at hc`. Rewrite `hc` using `[← Finset.sum_div, norm_div, norm_pow, le_div_iff₀ (by positivity), ← div_pow]`.

Use `le_trans ?_ hc` and prove the remaining obligations. Use `gcongr`. Conclude with `hi₁ i₀ (Finset.mem_univ _)`.
-/
theorem powerSum_second_main :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  refine ⟨16 * Real.exp 1 ^ 2, ?_, fun N M z i₀ => ?_⟩
  · have : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ (Real.one_le_exp zero_le_one)
    linarith
  have hN : 0 < N := i₀.pos
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  by_cases h0 : z i₁ = 0
  · refine ⟨M + 1, le_rfl, by omega, ?_⟩
    have : ‖z i₀‖ = 0 := le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)
    rw [this, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  have hR : 0 < ‖z i₁‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk, hk'⟩ := Finset.exists_max_image (Finset.Icc (M + 1) (M + N))
    (fun k => ‖∑ i, (z i / z i₁) ^ k‖) ⟨M + 1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  rw [Finset.mem_Icc] at hk
  refine ⟨k, hk.1, hk.2, ?_⟩
  have hc := core N M (fun i => z i / z i₁) i₁ (by simp [h0])
    (fun i => by
      rw [norm_div, div_le_one hR]; exact hi₁ i (Finset.mem_univ _))
    _ (fun j h1 h2 => hk' j (Finset.mem_Icc.2 ⟨h1, h2⟩))
  simp only [div_pow] at hc
  rw [← Finset.sum_div, norm_div, norm_pow, le_div_iff₀ (by positivity), ← div_pow] at hc
  refine le_trans ?_ hc
  gcongr
  exact hi₁ i₀ (Finset.mem_univ _)

end GlobalTheory
