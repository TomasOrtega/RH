import Mathlib

open scoped Matrix

namespace PositivityTheory.Rg.Sw.KAKA

open Matrix

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
-/
theorem gram_diag_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ)
    (hM : Mᴴ * M = diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ))) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ M = U * diagonal (fun j => (s j : ℂ)) := by
  classical
  let c : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun i => M i j)
  have hin : ∀ j k, inner ℂ (c j) (c k) = (Mᴴ * M) j k := by
    intro j k
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j => ((s j : ℂ)⁻¹) • c j
  let S : Set (Fin n) := {j | s j ≠ 0}
  have hv : Orthonormal ℂ (S.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    change inner ℂ (v j) (v k) = _
    simp only [v, inner_smul_left, inner_smul_right, hin, hM, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · subst hjk
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [if_true]
      rw [Complex.ofReal_pow, map_inv₀, Complex.conj_ofReal]
      field_simp
    · have : (⟨j, hj⟩ : S) ≠ ⟨k, hk⟩ := fun h => hjk (congrArg Subtype.val h)
      simp [hjk]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hU := (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  set U := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b with hUd
  refine ⟨U, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  · have hUe : ∀ i j, U i j = (b j).ofLp i := by
      intro i j
      simp [hUd, Module.Basis.toMatrix_apply]
    ext i j
    rw [Matrix.mul_diagonal, hUe]
    by_cases hj : s j = 0
    · have hc : c j = 0 := by
        have h1 := hin j j
        rw [hM, Matrix.diagonal_apply_eq, hj] at h1
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero] at h1
        exact inner_self_eq_zero.mp h1
      have : M i j = 0 := by
        have := congrArg (fun x : EuclideanSpace ℂ (Fin n) => x.ofLp i) hc
        simpa [c] using this
      rw [this, hj]; simp
    · have hbj : b j = v j := hb j hj
      rw [hbj]
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [v, c, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      field_simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gram_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (A * W)ᴴ * (A * W) = diagonal (fun j => (l j : ℂ)) := by
  have hG : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hdiag := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hdiag
  refine ⟨(hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.eigenvalues, ?_, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      hdiag]
    rfl

end PositivityTheory.Rg.Sw.KAKA
