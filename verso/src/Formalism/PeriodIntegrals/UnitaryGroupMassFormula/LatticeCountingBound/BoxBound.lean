import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeMultiplicity.EncardLeOfFinset

noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace BoxB

variable {n : ℕ}

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]`. Simplify using `only [Real.rpow_two]`. Evaluate the numerical expressions using `[Formalism.REAL.hs]`.
-/
lemma frob_sq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = Formalism.REAL.hs A := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Real.rpow_two]
  norm_num [Formalism.REAL.hs]

/- English proof (translation)
Rewrite using `[← frob_sq, Real.sqrt_sq (norm_nonneg A)]`.
-/
lemma frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ = Real.sqrt (Formalism.REAL.hs A) := by
  rw [← frob_sq, Real.sqrt_sq (norm_nonneg A)]

/- English proof (translation)
Unfold `Formalism.REAL.hs`. Establish `h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1`. Introduce `i`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne (Ne.symm hj)]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Simplify using `[h1]`.
-/
lemma hs_one : Formalism.REAL.hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold Formalism.REAL.hs
  have h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply_ne (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp [h1]

/- English proof (translation)
Rewrite using `[frob_eq, hs_one]`.
-/
lemma norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [frob_eq, hs_one]

/- English proof (translation)
Establish `hsq : 1 ≤ Real.sqrt n`. Rewrite using `[Real.one_le_sqrt]`. Conclude with `hn` after adjusting the coercions. Establish `hpow : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases.

Simplify using `[norm_one_eq]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹` using `by simp`. Establish `hf : (0 : ℝ) < k.factorial` using `by exact_mod_cast Nat.factorial_pos k`. Rewrite using `[norm_smul, hc, inv_mul_eq_div, mul_div_assoc']`.

Conclude with `div_le_div_of_nonneg_right hpow hf.le`.
-/
lemma term_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ Real.sqrt n * (‖X‖ ^ k / k.factorial) := by
  have hsq : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hpow : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [norm_one_eq]
    · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
        _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) hsq
  have hc : ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹ := by simp
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [norm_smul, hc, inv_mul_eq_div, mul_div_assoc']
  exact div_le_div_of_nonneg_right hpow hf.le

/- English proof (translation)
Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`. Establish `hs` using `(NormedSpace.expSeries_div_hasSum_exp ‖X‖).mul_left (Real.sqrt n)`. Rewrite `hs` using `[← Real.exp_eq_exp_ℝ]`. Conclude with `tsum_of_norm_bounded hs (fun k => term_le hn X k)`.
-/
lemma norm_exp_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ‖X‖).mul_left (Real.sqrt n)
  rw [← Real.exp_eq_exp_ℝ] at hs
  exact tsum_of_norm_bounded hs (fun k => term_le hn X k)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using `[Formalism.REAL.hs]`. Rewrite using `[← frob_sq, ← frob_eq]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2`.
-/
lemma hs_exp_le (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Formalism.REAL.hs]
  · rw [← frob_sq, ← frob_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2

end Frob

/- English proof (translation)
Unfold `Formalism.REAL.hs`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hs_eq_re_trace_conjTranspose_mul' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs M = (Mᴴ * M).trace.re := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Rewrite using `[hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk, Matrix.one_mul]`.
-/
lemma hs_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : kᴴ * k = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * M) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk,
    Matrix.one_mul]

end BoxB

open BoxB in
/- English proof (translation)
Introduce `n ε g`. Establish `hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1`. Introduce `k hk`. Simplify using `only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hk.1`.

Establish `hP : Formalism.REAL.Polar` using `Formalism.REAL.polar_decomposition_holds`. Establish `hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ)` using `g.2`. Take `⟨k0, X0, hk0, hX0, hg0⟩` from `(hP n ε).1 _ hgi`. Use `set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧ ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)} with hS`. Establish `hne : S.Nonempty` using `⟨_, k0, X0, hk0, hX0, hg0, rfl⟩`.

Establish `hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t`. Introduce and unpack `t ⟨k, X, hk, _, hgk, rfl⟩`. Unfold `hsN Formalism.MainNotions.S.uMat`. Rewrite using `[hgk, hs_unitary_mul (hK k hk)]`. Combine the equalities or inequalities in the displayed calculation.

Use `show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Break down `Nat.eq_zero_or_pos n with hn0 | hnpos` into its components or cases. Substitute `hn0` using the available equality.

Establish `h0 : hsN (Formalism.MainNotions.S.uMat g) = 0`. Unfold `hsN Formalism.REAL.hs`. Simplify using the standard rewrite rules. Rewrite `hlt` using `[h0]`. Simplify using `at hlt`.

Establish `hsqpos : 0 < Real.sqrt n` using `Real.sqrt_pos.mpr (by exact_mod_cast hnpos) set a := hsN (Formalism.MainNotions.S.uMat g) with ha`. Establish `hapos : 0 < a` using `lt_of_le_of_lt (by positivity) hlt`. Establish `h1 : sInf S < Real.log (a / Real.sqrt n)`. Rewrite using `[Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]`. Conclude with `hlt`.

Take `⟨t, htS, htlt⟩` from `exists_lt_of_csInf_lt hne h1`. Establish `h2` using `hbound t htS`. Establish `h3 : Real.exp t < a / Real.sqrt n`. Rewrite using `[← Real.exp_log (div_pos hapos hsqpos)]`. Conclude with `Real.exp_lt_exp.mpr htlt`.

Rewrite `h3` using `[lt_div_iff₀ hsqpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem box_lattice_point_bound : BoxBound := by
  intro n ε g
  have hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1 := by
    intro k hk
    simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hP : Formalism.REAL.Polar := Formalism.REAL.polar_decomposition_holds
  have hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k0, X0, hk0, hX0, hg0⟩ := (hP n ε).1 _ hgi
  set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (Formalism.REAL.hs X)} with hS
  have hne : S.Nonempty := ⟨_, k0, X0, hk0, hX0, hg0, rfl⟩
  have hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t := by
    rintro t ⟨k, X, hk, _, hgk, rfl⟩
    unfold hsN Formalism.MainNotions.S.uMat
    rw [hgk, hs_unitary_mul (hK k hk)]
    calc Real.sqrt (Formalism.REAL.hs (NormedSpace.exp X))
        ≤ Real.sqrt ((Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2) :=
          Real.sqrt_le_sqrt (hs_exp_le X)
      _ = Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X)) := Real.sqrt_sq (by positivity)
  show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : hsN (Formalism.MainNotions.S.uMat g) = 0 := by
      unfold hsN Formalism.REAL.hs
      simp
    rw [h0] at hlt
    simp at hlt
  · have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set a := hsN (Formalism.MainNotions.S.uMat g) with ha
    have hapos : 0 < a := lt_of_le_of_lt (by positivity) hlt
    have h1 : sInf S < Real.log (a / Real.sqrt n) := by
      rw [Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]
      exact hlt
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne h1
    have h2 := hbound t htS
    have h3 : Real.exp t < a / Real.sqrt n := by
      rw [← Real.exp_log (div_pos hapos hsqpos)]
      exact Real.exp_lt_exp.mpr htlt
    rw [lt_div_iff₀ hsqpos] at h3
    linarith

end PI.UnitaryGroupMassFormula.LCG
