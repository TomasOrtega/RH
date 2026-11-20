import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Matrix Module

namespace GlobalTheory.RectSVD

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_orthonormalBasis_singularValues {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {p q : ℕ} (hp : finrank ℂ F = p) (hq : finrank ℂ E = q) (T : E →ₗ[ℂ] F) :
    ∃ (u : OrthonormalBasis (Fin p) ℂ F) (v : OrthonormalBasis (Fin q) ℂ E), ∀ i j,
      inner ℂ (u i) (T (v j)) =
        if (i : ℕ) = (j : ℕ) then ((T.singularValues i : ℝ) : ℂ) else 0 := by
  classical
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set σ : ℕ → ℝ := fun i => T.singularValues i with hσ
  have key : ∀ j k : Fin q, inner ℂ (T (v j)) (T (v k)) =
      if j = k then ((σ k : ℝ) : ℂ) ^ 2 else 0 := by
    intro j k
    have h1 := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hq k
    rw [← T.sq_singularValues_fin hq k] at h1
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (v j) ((LinearMap.adjoint T ∘ₗ T) (v k)) = _
    rw [hv, h1, inner_smul_right, orthonormal_iff_ite.mp (OrthonormalBasis.orthonormal _)]
    split_ifs <;> simp [hσ]
  have hlt : ∀ i : ℕ, σ i ≠ 0 → i < p ∧ i < q := by
    intro i hi
    have h1 : i ∈ T.singularValues.support := Finsupp.mem_support_iff.mpr hi
    rw [T.support_singularValues, Finset.mem_range] at h1
    refine ⟨h1.trans_le (hp ▸ Submodule.finrank_le _), h1.trans_le (hq ▸ LinearMap.finrank_range_le T)⟩
  let w : Fin p → F := fun i =>
    if h : (i : ℕ) < q then ((σ i : ℂ))⁻¹ • T (v ⟨i, h⟩) else 0
  have hw : Orthonormal ℂ (({i : Fin p | σ i ≠ 0} : Set (Fin p)).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨k, hk⟩
    have hi' : σ i ≠ 0 := hi
    have hk' : σ k ≠ 0 := hk
    have hkc : (σ k : ℂ) ≠ 0 := by exact_mod_cast hk'
    simp only [Set.domRestrict_apply, w, dif_pos (hlt _ hi').2, dif_pos (hlt _ hk').2,
      inner_smul_left, inner_smul_right, key, Subtype.mk.injEq, Fin.mk.injEq, Fin.ext_iff]
    split_ifs with h
    · rw [h]
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · simp
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by rw [hp, Fintype.card_fin])
  refine ⟨u, v, fun i j => ?_⟩
  by_cases hj : σ j = 0
  · have h0 : T (v j) = 0 := by
      have := key j j
      rw [if_pos rfl, hj] at this
      simpa using this
    rw [h0, inner_zero_right]
    split_ifs with h
    · have : T.singularValues i = 0 := by rw [h]; exact hj
      simp [this]
    · rfl
  · have hjc : (σ j : ℂ) ≠ 0 := by exact_mod_cast hj
    have h1 := hu ⟨j, (hlt _ hj).1⟩ hj
    have h2 : T (v j) = (σ j : ℂ) • u ⟨j, (hlt _ hj).1⟩ := by
      rw [h1]
      simp only [w, dif_pos j.isLt, Fin.eta, smul_smul, mul_inv_cancel₀ hjc, one_smul]
    rw [h2, inner_smul_right, orthonormal_iff_ite.mp u.orthonormal]
    simp only [Fin.ext_iff]
    split_ifs with h
    · simp [h, hσ]
    · simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_svd_singularValues (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
          * Vᴴ := by
  obtain ⟨u, v, h⟩ := exists_orthonormalBasis_singularValues
    (E := EuclideanSpace ℂ (Fin q)) (F := EuclideanSpace ℂ (Fin p)) (p := p) (q := q)
    (by simp) (by simp) (Matrix.toEuclideanLin B)
  have hU := (EuclideanSpace.basisFun (Fin p) ℂ).toMatrix_orthonormalBasis_mem_unitary u
  have hV := (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary v
  refine ⟨_, hU, _, hV, ?_⟩
  set U := (EuclideanSpace.basisFun (Fin p) ℂ).toBasis.toMatrix u with hUd
  set V := (EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix v with hVd
  have hD : (Matrix.of fun (i : Fin p) (j : Fin q) =>
      if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
        = Uᴴ * B * V := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.mul_assoc]
    simp [hUd, hVd, Matrix.mul_apply, Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec,
      dotProduct, mul_comm]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_svd : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  intro p q B
  obtain ⟨U, hU, V, hV, h⟩ := exists_svd_singularValues p q B
  exact ⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩

end GlobalTheory.RectSVD
