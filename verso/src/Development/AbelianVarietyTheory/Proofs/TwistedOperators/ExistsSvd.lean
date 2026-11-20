import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Matrix Module

namespace GlobalTheory.RectSVD

/- English proof (translation)
Use `set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv`. Use `set σ : ℕ → ℝ := fun i => T.singularValues i with hσ`. Establish `key : ∀ j k : Fin q, inner ℂ (T (v j)) (T (v k)) = if j = k then ((σ k : ℝ) : ℂ) ^ 2 else 0`. Introduce `j k`. Establish `h1` using `T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hq k`.

Rewrite `h1` using `[← T.sq_singularValues_fin hq k]`. Rewrite using `[← LinearMap.adjoint_inner_right]`. Express the relevant statement in the definitionally equal form `inner ℂ (v j) ((LinearMap.adjoint T ∘ₗ T) (v k)) = _`. Rewrite using `[hv, h1, inner_smul_right, orthonormal_iff_ite.mp (OrthonormalBasis.orthonormal _)]`. Apply the tactic sequence `split_ifs <;> simp [hσ]`.

Establish `hlt : ∀ i : ℕ, σ i ≠ 0 → i < p ∧ i < q`. Introduce `i hi`. Establish `h1 : i ∈ T.singularValues.support` using `Finsupp.mem_support_iff.mpr hi`. Rewrite `h1` using `[T.support_singularValues, Finset.mem_range]`. Use `⟨h1.trans_le (hp ▸ Submodule.finrank_le _), h1.trans_le (hq ▸ LinearMap.finrank_range_le T)⟩` and prove the remaining obligations.

Set `w : Fin p → F` to `fun i => if h : (i : ℕ) < q then ((σ i : ℂ))⁻¹ • T (v ⟨i, h⟩) else 0`. Establish `hw : Orthonormal ℂ (({i : Fin p | σ i ≠ 0} : Set (Fin p)).domRestrict w)`. Rewrite using `[orthonormal_iff_ite]`. Introduce and unpack `⟨i, hi⟩ ⟨k, hk⟩`. Establish `hi' : σ i ≠ 0` using `hi`.

Establish `hk' : σ k ≠ 0` using `hk`. Establish `hkc : (σ k : ℂ) ≠ 0` using `by exact_mod_cast hk'`. Simplify using `only [Set.domRestrict_apply, w, dif_pos (hlt _ hi').2, dif_pos (hlt _ hk').2, inner_smul_left, inner_smul_right, key, Subtype.mk.injEq, Fin.mk.injEq, Fin.ext_iff]`. Use `split_ifs with h`. Rewrite using `[h]`.

Simplify using `only [map_inv₀, Complex.conj_ofReal]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Take `⟨u, hu⟩` from `hw.exists_orthonormalBasis_extension_of_card_eq (by rw [hp, Fintype.card_fin])`. Use `⟨u, v, fun i j => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hj : σ j = 0`. Establish `h0 : T (v j) = 0`. Use `key j j` as an intermediate fact. Rewrite `this` using `[if_pos rfl, hj]`. Simplify using `using this`.

Rewrite using `[h0, inner_zero_right]`. Use `split_ifs with h`. Establish `: T.singularValues i = 0` using `by rw [h]; exact hj`. Simplify using `[this]`. Both sides reduce to the same expression.

Establish `hjc : (σ j : ℂ) ≠ 0` using `by exact_mod_cast hj`. Establish `h1` using `hu ⟨j, (hlt _ hj).1⟩ hj`. Establish `h2 : T (v j) = (σ j : ℂ) • u ⟨j, (hlt _ hj).1⟩`. Rewrite using `[h1]`. Simplify using `only [w, dif_pos j.isLt, Fin.eta, smul_smul, mul_inv_cancel₀ hjc, one_smul]`.

Rewrite using `[h2, inner_smul_right, orthonormal_iff_ite.mp u.orthonormal]`. Simplify using `only [Fin.ext_iff]`. Use `split_ifs with h`. Simplify using `[h, hσ]`. Simplify using the standard rewrite rules.
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
Take `⟨u, v, h⟩` from `exists_orthonormalBasis_singularValues (E := EuclideanSpace ℂ (Fin q)) (F := EuclideanSpace ℂ (Fin p)) (p := p) (q := q) (by simp) (by simp) (Matrix.toEuclideanLin B)`. Establish `hU` using `(EuclideanSpace.basisFun (Fin p) ℂ).toMatrix_orthonormalBasis_mem_unitary u`. Establish `hV` using `(EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary v`. Use `⟨_, hU, _, hV, ?_⟩` and prove the remaining obligations. Use `set U := (EuclideanSpace.basisFun (Fin p) ℂ).toBasis.toMatrix u with hUd`.

Use `set V := (EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix v with hVd`. Establish `hD : (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0) = Uᴴ * B * V`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, ← h, Matrix.mul_assoc]`. Simplify using `[hUd, hVd, Matrix.mul_apply, Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]`.

Establish `h1 : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Establish `h2 : V * Vᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hV`. Rewrite using `[hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]`.
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
Introduce `p q B`. Take `⟨U, hU, V, hV, h⟩` from `exists_svd_singularValues p q B`. Conclude with `⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩`.
-/
theorem exists_svd : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  intro p q B
  obtain ⟨U, hU, V, hV, h⟩ := exists_svd_singularValues p q B
  exact ⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩

end GlobalTheory.RectSVD
