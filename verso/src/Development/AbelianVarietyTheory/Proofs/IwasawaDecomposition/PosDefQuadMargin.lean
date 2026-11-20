import Mathlib

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma quad_smul {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (a : ℝ) (c : ι → ℝ) :
    ∑ i, ∑ j, (a • c) i * (a • c) j * M i j = a ^ 2 * ∑ i, ∑ j, c i * c j * M i j := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
The claim follows from `|∑ i, ∑ j, c i * c j * E i j| ≤ (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by have hc : ∀ i, |c i| ≤ ‖c‖ := fun i => by simpa [Real.norm_eq_abs] using norm_le_pi_norm c i calc |∑ i, ∑ j, c i * c j * E i j| ≤ ∑ i, ∑ j, |c i * c j * E i j| := (Finset.abs_sum_le_sum_abs _ _).trans …`.
-/
private lemma quad_err {ι : Type} [Fintype ι] (E : ι → ι → ℝ) (η : ℝ) (_hη : 0 ≤ η)
    (hE : ∀ i j, |E i j| ≤ η) (c : ι → ℝ) :
    |∑ i, ∑ j, c i * c j * E i j| ≤ (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
  have hc : ∀ i, |c i| ≤ ‖c‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm c i
  calc |∑ i, ∑ j, c i * c j * E i j|
      ≤ ∑ i, ∑ j, |c i * c j * E i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖c‖ ^ 2 * η := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, sq]
        have h1 := hc i; have h2 := hc j; have h3 := hE i j
        have := abs_nonneg (c i); have := abs_nonneg (c j); have := abs_nonneg (E i j)
        have := norm_nonneg c
        calc |c i| * |c j| * |E i j| ≤ ‖c‖ * ‖c‖ * |E i j| := by gcongr
          _ ≤ ‖c‖ * ‖c‖ * η := by gcongr
    _ = (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Conclude with `⟨1, one_pos, fun E _ c hc => absurd (Subsingleton.elim c 0) hc⟩`. Use `set q : (ι → ℝ) → ℝ := fun c => ∑ i, ∑ j, c i * c j * M i j with hq`. Establish `hcont : Continuous q`. Simplify using `only [hq]`.

Use `fun_prop`. Establish `hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty` using `(NormedSpace.sphere_nonempty).mpr zero_le_one`. Take `⟨c₀, hc₀, hmin⟩` from `(isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn`. Establish `hc₀ne : c₀ ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hc₀`. Use `set μ := q c₀ with hμ`. Establish `hμpos : 0 < μ` using `hM c₀ hc₀ne`. Establish `hlow : ∀ c : ι → ℝ, c ≠ 0 → μ * ‖c‖ ^ 2 ≤ q c`. Introduce `c hc`.

Establish `hs : 0 < ‖c‖` using `norm_pos_iff.mpr hc`. Establish `hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ι → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']`. Establish `h1 : μ ≤ q (‖c‖⁻¹ • c)` using `hmin hmem`. Establish `h2 : q (‖c‖⁻¹ • c) = (‖c‖⁻¹) ^ 2 * q c` using `quad_smul M _ c`.

Rewrite `h1` using `[h2]`. Establish `h3 : (‖c‖⁻¹) ^ 2 * ‖c‖ ^ 2 = 1`. Rewrite using `[← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `set K : ℝ := (Fintype.card ι : ℝ) ^ 2 with hK`.

Establish `hK0 : 0 ≤ K` using `sq_nonneg _`. Use `⟨μ / (2 * K + 1), div_pos hμpos (by linarith), ?_⟩` and prove the remaining obligations. Introduce `E hE c hc`. Establish `hη0 : 0 ≤ μ / (2 * K + 1)` using `(div_pos hμpos (by linarith)).le`. Establish `herr` using `quad_err E _ hη0 hE c`.

Establish `hs : 0 < ‖c‖` using `norm_pos_iff.mpr hc`. Establish `hsplit : ∑ i, ∑ j, c i * c j * (M i j + E i j) = q c + ∑ i, ∑ j, c i * c j * E i j`. Simplify using `only [hq, mul_add, Finset.sum_add_distrib]`. Rewrite using `[hsplit]`. Establish `hKη : K * (μ / (2 * K + 1)) < μ`.

Rewrite using `[mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith`. Establish `hs2 : 0 < ‖c‖ ^ 2` using `by positivity`. Use `hlow c hc` as an intermediate fact. Establish `hlow'` using `(abs_le.mp herr).1`. Rewrite `hlow'` using `[← hK]`.

Use polynomial arithmetic with `[mul_lt_mul_of_pos_right hKη hs2]`.
-/
theorem posDef_quad_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) →
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun E _ c hc => absurd (Subsingleton.elim c 0) hc⟩
  set q : (ι → ℝ) → ℝ := fun c => ∑ i, ∑ j, c i * c j * M i j with hq
  have hcont : Continuous q := by
    simp only [hq]; fun_prop
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).mpr zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl; simp at hc₀
  set μ := q c₀ with hμ
  have hμpos : 0 < μ := hM c₀ hc₀ne
  have hlow : ∀ c : ι → ℝ, c ≠ 0 → μ * ‖c‖ ^ 2 ≤ q c := by
    intro c hc
    have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
    have h1 : μ ≤ q (‖c‖⁻¹ • c) := hmin hmem
    have h2 : q (‖c‖⁻¹ • c) = (‖c‖⁻¹) ^ 2 * q c := quad_smul M _ c
    rw [h2] at h1
    have h3 : (‖c‖⁻¹) ^ 2 * ‖c‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    calc μ * ‖c‖ ^ 2 ≤ ((‖c‖⁻¹) ^ 2 * q c) * ‖c‖ ^ 2 := by gcongr
      _ = q c := by rw [mul_comm ((‖c‖⁻¹) ^ 2), mul_assoc, h3, mul_one]
  set K : ℝ := (Fintype.card ι : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  refine ⟨μ / (2 * K + 1), div_pos hμpos (by linarith), ?_⟩
  intro E hE c hc
  have hη0 : 0 ≤ μ / (2 * K + 1) := (div_pos hμpos (by linarith)).le
  have herr := quad_err E _ hη0 hE c
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsplit : ∑ i, ∑ j, c i * c j * (M i j + E i j)
      = q c + ∑ i, ∑ j, c i * c j * E i j := by
    simp only [hq, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have hKη : K * (μ / (2 * K + 1)) < μ := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  have hs2 : 0 < ‖c‖ ^ 2 := by positivity
  have := hlow c hc
  have hlow' := (abs_le.mp herr).1
  rw [← hK] at hlow'
  nlinarith [mul_lt_mul_of_pos_right hKη hs2]

end GlobalTheory
