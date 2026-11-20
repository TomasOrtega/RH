import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.ArithmeticLatticeHypothesis

namespace Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

/- English proof (translation)
Introduce `E _ _ α T hT hw hex`. Take `⟨β, hβ⟩` from `hex`. Assume the negation of the conclusion as `hne`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`.

Apply `hne` to reduce the goal to its premises. Rewrite `hβ` using `[mul_zero, sub_eq_zero]`. Conclude with `hβ`. Establish `hβE : (α : E) - 1 = (T : E) * (β : E)`. Establish `h1` using `congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) hβ`.

Simplify using `using h1`. Establish `hT3 : (3 : ℝ) ≤ T` using `by exact_mod_cast hT`. Establish `hwβ : ∀ w : NumberField.InfinitePlace E, w (β : E) < 1`. Introduce `w`. Establish `e : ∀ x : E, w x = ‖w.embedding x‖` using `fun x => (NumberField.InfinitePlace.norm_embedding_eq w x).symm`.

Establish `h1` using `hw w`. Rewrite `h1` using `[e]`. Establish `h3 : w.embedding ((α : E) - 1) = (T : ℂ) * w.embedding (β : E)`. Rewrite using `[hβE, map_mul, map_natCast]`. Establish `h4 : ‖w.embedding ((α : E) - 1)‖ ≤ 2`.

Rewrite using `[map_sub, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h4` using `[h3, norm_mul, Complex.norm_natCast]`. Rewrite using `[e]`. Use polynomial arithmetic with `[norm_nonneg (w.embedding (β : E))]`.

Establish `hprod` using `NumberField.InfinitePlace.prod_eq_abs_norm (β : E)`. Establish `hlt : ∏ w : NumberField.InfinitePlace E, w (β : E) ^ w.mult < 1`. Take `⟨w0⟩` from `(inferInstance : Nonempty (NumberField.InfinitePlace E))`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]`. Establish `hA : w0 (β : E) ^ w0.mult < 1` using `pow_lt_one₀ (by positivity) (hwβ w0) (NumberField.InfinitePlace.mult_ne_zero)`.

Establish `hB : ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult ≤ 1` using `Finset.prod_le_one (fun w _ => by positivity) (fun w _ => pow_le_one₀ (by positivity) (hwβ w).le)`. Establish `hB0 : 0 ≤ ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult` using `Finset.prod_nonneg (fun w _ => by positivity)`. Use polynomial arithmetic with `[pow_nonneg (by positivity : (0 : ℝ) ≤ w0 (β : E)) w0.mult]`. Establish `hNz : Algebra.norm ℤ β ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hβ0`. Establish `hN : Algebra.norm ℚ (β : E) = ((Algebra.norm ℤ β : ℤ) : ℚ)` using `(Algebra.coe_norm_int β).symm`.

Establish `h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ (β : E) : ℚ) : ℝ)|`. Rewrite using `[hN]`. Use `push_cast`. Conclude with `Int.one_le_abs hNz` after adjusting the coercions. Rewrite `hlt` using `[hprod, Rat.cast_abs]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem root_of_unity_mod_t : RootUnityModT := by
  intro E _ _ α T hT hw hex
  classical
  obtain ⟨β, hβ⟩ := hex
  by_contra hne
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hne
    rw [mul_zero, sub_eq_zero] at hβ
    exact hβ
  have hβE : (α : E) - 1 = (T : E) * (β : E) := by
    have h1 := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) hβ
    simpa using h1
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hwβ : ∀ w : NumberField.InfinitePlace E, w (β : E) < 1 := by
    intro w
    have e : ∀ x : E, w x = ‖w.embedding x‖ := fun x => (NumberField.InfinitePlace.norm_embedding_eq w x).symm
    have h1 := hw w
    rw [e] at h1
    have h3 : w.embedding ((α : E) - 1) = (T : ℂ) * w.embedding (β : E) := by
      rw [hβE, map_mul, map_natCast]
    have h4 : ‖w.embedding ((α : E) - 1)‖ ≤ 2 := by
      rw [map_sub, map_one]
      calc ‖w.embedding (α : E) - 1‖ ≤ ‖w.embedding (α : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [h1, norm_one]; norm_num
    rw [h3, norm_mul, Complex.norm_natCast] at h4
    rw [e]
    nlinarith [norm_nonneg (w.embedding (β : E))]
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
  have hlt : ∏ w : NumberField.InfinitePlace E, w (β : E) ^ w.mult < 1 := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]
    have hA : w0 (β : E) ^ w0.mult < 1 :=
      pow_lt_one₀ (by positivity) (hwβ w0) (NumberField.InfinitePlace.mult_ne_zero)
    have hB : ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult ≤ 1 :=
      Finset.prod_le_one (fun w _ => by positivity) (fun w _ => pow_le_one₀ (by positivity) (hwβ w).le)
    have hB0 : 0 ≤ ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult :=
      Finset.prod_nonneg (fun w _ => by positivity)
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ w0 (β : E)) w0.mult]
  have hNz : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0
  have hN : Algebra.norm ℚ (β : E) = ((Algebra.norm ℤ β : ℤ) : ℚ) := (Algebra.coe_norm_int β).symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ (β : E) : ℚ) : ℝ)| := by
    rw [hN]
    push_cast
    exact_mod_cast Int.one_le_abs hNz
  rw [hprod, Rat.cast_abs] at hlt
  linarith

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [J]`.
-/
lemma JJ : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, JJ]`.
-/
lemma inv_eq_J (N : Matrix (Fin 2) (Fin 2) ℂ) (h : N.conjTranspose * J * N = J) :
    N⁻¹ = J * N.conjTranspose * J := by
  apply Matrix.inv_eq_left_inv
  calc J * N.conjTranspose * J * N = J * (N.conjTranspose * J * N) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, JJ]

/- English proof (translation)
Establish `j00 : J 0 0 = 1` using `by simp [J]`. Establish `j01 : J 0 1 = 0` using `by simp [J]`. Establish `j10 : J 1 0 = 0` using `by simp [J]`. Establish `j11 : J 1 1 = -1` using `by simp [J]`. Rewrite using `[inv_eq_J N h]`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, j00, j01, j10, j11, Matrix.conjTranspose_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma entry_MNinv (M N : Matrix (Fin 2) (Fin 2) ℂ) (h : N.conjTranspose * J * N = J) :
    (M * N⁻¹) 1 0 = M 1 0 * (starRingEnd ℂ) (N 0 0) - M 1 1 * (starRingEnd ℂ) (N 0 1) := by
  have j00 : J 0 0 = 1 := by simp [J]
  have j01 : J 0 1 = 0 := by simp [J]
  have j10 : J 1 0 = 0 := by simp [J]
  have j11 : J 1 1 = -1 := by simp [J]
  rw [inv_eq_J N h]
  simp [Matrix.mul_apply, Fin.sum_univ_two, j00, j01, j10, j11, Matrix.conjTranspose_apply]
  ring

/- English proof (translation)
Introduce `M N sh₁ ch₁ sh₂ ch₂ hM hN hs₁ hc₁ hcs₁ hs₂ hc₂ hcs₂ hN10 hM10`. Establish `hright : ∀ P : Matrix (Fin 2) (Fin 2) ℂ, P.conjTranspose * J * P = J → P * J * P.conjTranspose = J`. Introduce `P hP`. Establish `hl : (J * P.conjTranspose * J) * P = 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hP, JJ]`. Establish `hu` using `Matrix.isUnit_det_of_left_inverse hl`. Establish `hr : P * (J * P.conjTranspose * J) = 1`. Rewrite using `[← Matrix.inv_eq_left_inv hl]`.

Conclude with `Matrix.mul_nonsing_inv P hu`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, JJ, Matrix.mul_one]`. Use `_ = J := by rw [hr, Matrix.one_mul]`. Establish `hsq : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ)`.

Introduce `z`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hsq' : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[mul_comm, hsq]`.

Establish `hNc : ‖N 0 0‖ ^ 2 - ‖N 1 0‖ ^ 2 = 1`. Establish `h1` using `congrFun (congrFun hN 0) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1`. Rewrite `h1` using `[hsq', hsq']`. Apply the tactic sequence `all_goals exact_mod_cast h1`.

Establish `hNr : ‖N 0 0‖ ^ 2 - ‖N 0 1‖ ^ 2 = 1`. Establish `h1` using `congrFun (congrFun (hright N hN) 0) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1`. Rewrite `h1` using `[hsq, hsq]`. Apply the tactic sequence `all_goals exact_mod_cast h1`.

Establish `hMr : ‖M 1 0‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1`. Establish `h1` using `congrFun (congrFun (hright M hM) 1) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1`. Rewrite `h1` using `[hsq, hsq]`. Apply the tactic sequence `all_goals exact_mod_cast h1`.

Establish `h01 : ‖N 0 1‖ = 1 / sh₁`. Rewrite using `[← hN10]`. Establish `: ‖N 0 1‖ ^ 2 = ‖N 1 0‖ ^ 2` using `by linarith`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this`. Establish `h00 : ‖N 0 0‖ = ch₁ / sh₁`.

Establish `: ‖N 0 0‖ ^ 2 = (ch₁ / sh₁) ^ 2`. Rewrite using `[div_pow, hcs₁]`. Establish `e : ‖N 0 0‖ ^ 2 = 1 + ‖N 1 0‖ ^ 2` using `by linarith`. Rewrite using `[e, hN10]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `all_goals ring`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₁ hs₁.le) two_ne_zero).mp this`. Establish `h11 : ‖M 1 1‖ = ch₂ / sh₂`. Establish `: ‖M 1 1‖ ^ 2 = (ch₂ / sh₂) ^ 2`. Rewrite using `[div_pow, hcs₂]`.

Establish `e : ‖M 1 1‖ ^ 2 = 1 + ‖M 1 0‖ ^ 2` using `by linarith`. Rewrite using `[e, hM10]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₂ hs₂.le) two_ne_zero).mp this`.

Rewrite using `[entry_MNinv M N hN]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]`. Use `_ = (ch₁ + ch₂) / (sh₁ * sh₂) := by`. Rewrite using `[hM10, h00, h11, h01]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`.
-/
theorem theorem_B_entry_formula : ThmBEntry := by
  intro M N sh₁ ch₁ sh₂ ch₂ hM hN hs₁ hc₁ hcs₁ hs₂ hc₂ hcs₂ hN10 hM10

  have hright : ∀ P : Matrix (Fin 2) (Fin 2) ℂ, P.conjTranspose * J * P = J →
      P * J * P.conjTranspose = J := by
    intro P hP
    have hl : (J * P.conjTranspose * J) * P = 1 := by
      calc J * P.conjTranspose * J * P = J * (P.conjTranspose * J * P) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hP, JJ]
    have hu := Matrix.isUnit_det_of_left_inverse hl
    have hr : P * (J * P.conjTranspose * J) = 1 := by
      rw [← Matrix.inv_eq_left_inv hl]
      exact Matrix.mul_nonsing_inv P hu
    calc P * J * P.conjTranspose = P * (J * P.conjTranspose * J) * J := by
          simp only [Matrix.mul_assoc, JJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]
  have hsq : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq' : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, hsq]

  have hNc : ‖N 0 0‖ ^ 2 - ‖N 1 0‖ ^ 2 = 1 := by
    have h1 := congrFun (congrFun hN 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq', hsq'] at h1
    all_goals exact_mod_cast h1

  have hNr : ‖N 0 0‖ ^ 2 - ‖N 0 1‖ ^ 2 = 1 := by
    have h1 := congrFun (congrFun (hright N hN) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq, hsq] at h1
    all_goals exact_mod_cast h1
  have hMr : ‖M 1 0‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 := by
    have h1 := congrFun (congrFun (hright M hM) 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq, hsq] at h1
    all_goals exact_mod_cast h1
  have h01 : ‖N 0 1‖ = 1 / sh₁ := by
    rw [← hN10]
    have : ‖N 0 1‖ ^ 2 = ‖N 1 0‖ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have h00 : ‖N 0 0‖ = ch₁ / sh₁ := by
    have : ‖N 0 0‖ ^ 2 = (ch₁ / sh₁) ^ 2 := by
      rw [div_pow, hcs₁]
      have e : ‖N 0 0‖ ^ 2 = 1 + ‖N 1 0‖ ^ 2 := by linarith
      rw [e, hN10]
      field_simp
      all_goals ring
    exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₁ hs₁.le) two_ne_zero).mp this
  have h11 : ‖M 1 1‖ = ch₂ / sh₂ := by
    have : ‖M 1 1‖ ^ 2 = (ch₂ / sh₂) ^ 2 := by
      rw [div_pow, hcs₂]
      have e : ‖M 1 1‖ ^ 2 = 1 + ‖M 1 0‖ ^ 2 := by linarith
      rw [e, hM10]
      field_simp
      all_goals ring
    exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₂ hs₂.le) two_ne_zero).mp this
  rw [entry_MNinv M N hN]
  calc ‖M 1 0 * (starRingEnd ℂ) (N 0 0) - M 1 1 * (starRingEnd ℂ) (N 0 1)‖
      ≤ ‖M 1 0 * (starRingEnd ℂ) (N 0 0)‖ + ‖M 1 1 * (starRingEnd ℂ) (N 0 1)‖ := norm_sub_le _ _
    _ = ‖M 1 0‖ * ‖N 0 0‖ + ‖M 1 1‖ * ‖N 0 1‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ = (ch₁ + ch₂) / (sh₁ * sh₂) := by
      rw [hM10, h00, h11, h01]
      field_simp
      all_goals ring

/- English proof (translation)
Introduce `ga T T' hT hT'`. Establish `hsT : (Real.sqrt T : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'`. Establish `hsT' : (Real.sqrt T' : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'`. Establish `hv : ∀ i, (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i) ≠ 0`. Introduce `i`.

Use `fin_cases i`. Simplify using `using hsT`. Simplify using `using hsT'`. Establish `hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ = Matrix.diagonal (fun i => (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i)⁻¹)`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `Matrix.diagonal_one` and compare the differences between its conclusion and the goal. Conclude with `inv_mul_cancel₀ (hv _)`. Rewrite using `[hinv]`. Simplify using `only [Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Simplify using `[norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hT'.le]`. Clear the denominators using the available nonvanishing facts.
-/
theorem s_matrix_entry_formula : SEntry := by
  intro ga T T' hT hT'
  have hsT : (Real.sqrt T : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have hsT' : (Real.sqrt T' : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'
  have hv : ∀ i, (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hsT
    · simpa using hsT'
  have hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ =
      Matrix.diagonal (fun i => (![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)] i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact inv_mul_cancel₀ (hv _)
  rw [hinv]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hT'.le]
  field_simp

end Formalism.SLP.GlobalBoundRefinements.P
