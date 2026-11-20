import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
Establish `hE : NormedSpace.exp (l : ℂ) = ((Real.exp l : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_exp]`. Use `first`. Consider the case `rw [Complex.exp_eq_exp_ℂ]`. Consider the case `exact (congrFun Complex.exp_eq_exp_ℂ (l : ℂ)).symm`.

Rewrite using `[hE]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`.

Establish `h1 : ((Real.exp l : ℝ) : ℂ) = 1` using `mul_right_cancel₀ hy (h.trans (one_mul y).symm)`. Establish `h2 : Real.exp l = 1` using `by exact_mod_cast h1`. Establish `h3 : l = 0` using `Real.exp_eq_one_iff l |>.mp h2`. Simplify using `[h3]`. Introduce `h`.

Break down `mul_eq_zero.mp h with hl | hy` into its components or cases. Establish `h3 : l = 0` using `by exact_mod_cast hl`. Simplify using `[h3]`. Simplify using `[hy]`.
-/
theorem inst_exp_real_entry (l : ℝ) (y : ℂ) :
    NormedSpace.exp (l : ℂ) * y = y ↔ (l : ℂ) * y = 0 := by
  have hE : NormedSpace.exp (l : ℂ) = ((Real.exp l : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    first
      | rw [Complex.exp_eq_exp_ℂ]
      | exact (congrFun Complex.exp_eq_exp_ℂ (l : ℂ)).symm
  rw [hE]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have h1 : ((Real.exp l : ℝ) : ℂ) = 1 := mul_right_cancel₀ hy (h.trans (one_mul y).symm)
      have h2 : Real.exp l = 1 := by exact_mod_cast h1
      have h3 : l = 0 := Real.exp_eq_one_iff l |>.mp h2
      simp [h3]
  · intro h
    rcases mul_eq_zero.mp h with hl | hy
    · have h3 : l = 0 := by exact_mod_cast hl
      simp [h3]
    · simp [hy]

/- English proof (translation)
Establish `h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1` using `by first`. Consider the case `exact hX.eigenvectorUnitary.2.1`. Consider the case `exact (Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2)`. Consider the case `exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2`. Consider the case `exact unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2`.

Establish `h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1` using `by first`. Consider the case `exact hX.eigenvectorUnitary.2.2`. Consider the case `exact (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)`. Consider the case `exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2`. Consider the case `exact unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2`.

Use `⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(conv_lhs => rw [hX.spectral_theorem])`. Simplify using `[Function.comp_def]`. Consider the case `(conv_lhs => rw [hX.spectral_theorem])`.

Simplify using `[Function.comp_def, Unitary.conjStarAlgAut_apply]`. Consider the case `(have h3 := hX.star_mul_self_mul_eq_diagonal`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`.

Use `_ = _ := by rw [h3]; simp [Function.comp_def])`.
-/
private theorem exists_unitary_diagonal_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), star U * U = 1 ∧ U * star U = 1 ∧
      X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  have h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.1
      | exact (Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2)
      | exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.2
      | exact (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)
      | exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩
  first
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def]
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def, Unitary.conjStarAlgAut_apply]
    | (have h3 := hX.star_mul_self_mul_eq_diagonal
       calc X = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * X *
                (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
             simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
             rw [Matrix.mul_assoc, h2, Matrix.mul_one]
         _ = _ := by rw [h3]; simp [Function.comp_def])

/- English proof (translation)
Introduce `n X hX w`. Take `⟨U, d, hUU, hUU', hX'⟩` from `exists_unitary_diagonal_of_isHermitian X hX`. Establish `hexp : NormedSpace.exp X = U * diagonal (fun i => NormedSpace.exp (d i : ℂ)) * star U`. Establish `hunit : IsUnit U` using `⟨⟨U, star U, hUU', hUU⟩, rfl⟩`. Establish `hinv : U⁻¹ = star U` using `Matrix.inv_eq_left_inv hUU`.

Rewrite using `[hX', ← hinv]`. Establish `hd : NormedSpace.exp (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => NormedSpace.exp (d i : ℂ))`. Rewrite using `[Matrix.exp_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `first`. Consider the case `exact Pi.exp_apply _ _`. Consider the case `simp [Pi.exp_def]`. Consider the case `rfl`. Use `first`.

Consider the case `rw [Matrix.exp_conj _ _ hunit, hd]`. Consider the case `rw [Matrix.exp_conj ℂ _ _ hunit, hd]`. Establish `inj : ∀ a b : Fin n → ℂ, U *ᵥ a = U *ᵥ b → a = b`. Introduce `a b h`. Establish `h2` using `congrArg (fun v => star U *ᵥ v) h`.

Simplify `h2` using `only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]`. Take `⟨y, hy⟩ : ∃ y, y = star U *ᵥ w` from `⟨_, rfl⟩`. Establish `hw : w = U *ᵥ y` using `by rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]`. Establish `hXw : X *ᵥ w = U *ᵥ (fun i => (d i : ℂ) * y i)`. Rewrite using `[hX', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal]`. Establish `hEw : NormedSpace.exp X *ᵥ w = U *ᵥ (fun i => NormedSpace.exp (d i : ℂ) * y i)`. Rewrite using `[hexp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y`. Apply `inj` to reduce the goal to its premises. Rewrite using `[← hEw, h]`. Conclude with `hw`. Rewrite using `[hXw]`.

Establish `h0 : (fun i => (d i : ℂ) * y i) = 0`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `exact (inst_exp_real_entry (d i) (y i)).mp (congrFun h1 i)`. Rewrite using `[h0, Matrix.mulVec_zero]`. Introduce `h`.

Rewrite `h` using `[hXw]`. Establish `h2 : (fun i => (d i : ℂ) * y i) = 0` using `inj _ 0 (by rw [h, Matrix.mulVec_zero])`. Rewrite using `[hEw]`. Establish `h3 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `exact (inst_exp_real_entry (d i) (y i)).mpr (congrFun h2 i)`. Rewrite using `[h3, ← hw]`.
-/
theorem exponent_fixed_instance : InstExpFix := by
  intro n X hX w
  obtain ⟨U, d, hUU, hUU', hX'⟩ := exists_unitary_diagonal_of_isHermitian X hX
  have hexp : NormedSpace.exp X = U * diagonal (fun i => NormedSpace.exp (d i : ℂ)) * star U := by
    have hunit : IsUnit U := ⟨⟨U, star U, hUU', hUU⟩, rfl⟩
    have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hUU
    rw [hX', ← hinv]
    have hd : NormedSpace.exp (diagonal (fun i => (d i : ℂ))) =
        diagonal (fun i => NormedSpace.exp (d i : ℂ)) := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext i
      first
        | exact Pi.exp_apply _ _
        | simp [Pi.exp_def]
        | rfl
    first
      | rw [Matrix.exp_conj _ _ hunit, hd]
      | rw [Matrix.exp_conj ℂ _ _ hunit, hd]
  have inj : ∀ a b : Fin n → ℂ, U *ᵥ a = U *ᵥ b → a = b := by
    intro a b h
    have h2 := congrArg (fun v => star U *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] using h2
  obtain ⟨y, hy⟩ : ∃ y, y = star U *ᵥ w := ⟨_, rfl⟩
  have hw : w = U *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hXw : X *ᵥ w = U *ᵥ (fun i => (d i : ℂ) * y i) := by
    rw [hX', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  have hEw : NormedSpace.exp X *ᵥ w = U *ᵥ (fun i => NormedSpace.exp (d i : ℂ) * y i) := by
    rw [hexp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  constructor
  · intro h
    have h1 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      apply inj
      rw [← hEw, h]
      exact hw
    rw [hXw]
    have h0 : (fun i => (d i : ℂ) * y i) = 0 := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mp (congrFun h1 i)
    rw [h0, Matrix.mulVec_zero]
  · intro h
    rw [hXw] at h
    have h2 : (fun i => (d i : ℂ) * y i) = 0 := inj _ 0 (by rw [h, Matrix.mulVec_zero])
    rw [hEw]
    have h3 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mpr (congrFun h2 i)
    rw [h3, ← hw]

end PI.ScMuExists.UnitaryGroupMassFormula
