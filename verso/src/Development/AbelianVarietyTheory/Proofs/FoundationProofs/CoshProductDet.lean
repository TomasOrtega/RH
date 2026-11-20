import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers

open scoped Matrix
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

namespace GlobalTheory.DetExpP

/- English proof (translation)
Take `⟨u, v, h⟩` from `GlobalTheory.RectSVD.exists_orthonormalBasis_singularValues (E := EuclideanSpace ℂ k) (F := EuclideanSpace ℂ m) (p := p) (q := q) (by simp [Fintype.card_congr fm]) (by simp [Fintype.card_congr fk]) (Matrix.toEuclideanLin B)`. Use `set u' := u.reindex fm.symm with hu'`. Use `set v' := v.reindex fk.symm with hv'`. Establish `hU` using `(EuclideanSpace.basisFun m ℂ).toMatrix_orthonormalBasis_mem_unitary u'`. Establish `hV` using `(EuclideanSpace.basisFun k ℂ).toMatrix_orthonormalBasis_mem_unitary v'`.

Use `⟨_, hU, _, hV, ?_⟩` and prove the remaining obligations. Use `set U := (EuclideanSpace.basisFun m ℂ).toBasis.toMatrix u' with hUd`. Use `set V := (EuclideanSpace.basisFun k ℂ).toBasis.toMatrix v' with hVd`. Establish `hD : (Matrix.of fun a b => if ((fm a : ℕ) = (fk b : ℕ)) then (((Matrix.toEuclideanLin B).singularValues (fm a) : ℝ) : ℂ) else 0) = Uᴴ * B * V`. Use extensionality with `a b`.

Rewrite using `[Matrix.of_apply, ← h (fm a) (fk b), Matrix.mul_assoc]`. Simplify using `[hUd, hVd, hu', hv', Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]`. Establish `h1 : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Establish `h2 : V * Vᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hV`. Rewrite using `[hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem exists_svd_equiv {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] {p q : ℕ}
    (fm : m ≃ Fin p) (fk : k ≃ Fin q) (B : Matrix m k ℂ) :
    ∃ U ∈ Matrix.unitaryGroup m ℂ, ∃ V ∈ Matrix.unitaryGroup k ℂ,
      B = U * Matrix.of (fun a b => if ((fm a : ℕ) = (fk b : ℕ)) then
        (((Matrix.toEuclideanLin B).singularValues (fm a) : ℝ) : ℂ) else 0) * Vᴴ := by
  obtain ⟨u, v, h⟩ := GlobalTheory.RectSVD.exists_orthonormalBasis_singularValues
    (E := EuclideanSpace ℂ k) (F := EuclideanSpace ℂ m) (p := p) (q := q)
    (by simp [Fintype.card_congr fm]) (by simp [Fintype.card_congr fk]) (Matrix.toEuclideanLin B)
  set u' := u.reindex fm.symm with hu'
  set v' := v.reindex fk.symm with hv'
  have hU := (EuclideanSpace.basisFun m ℂ).toMatrix_orthonormalBasis_mem_unitary u'
  have hV := (EuclideanSpace.basisFun k ℂ).toMatrix_orthonormalBasis_mem_unitary v'
  refine ⟨_, hU, _, hV, ?_⟩
  set U := (EuclideanSpace.basisFun m ℂ).toBasis.toMatrix u' with hUd
  set V := (EuclideanSpace.basisFun k ℂ).toBasis.toMatrix v' with hVd
  have hD : (Matrix.of fun a b => if ((fm a : ℕ) = (fk b : ℕ)) then
        (((Matrix.toEuclideanLin B).singularValues (fm a) : ℝ) : ℂ) else 0) = Uᴴ * B * V := by
    ext a b
    rw [Matrix.of_apply, ← h (fm a) (fk b), Matrix.mul_assoc]
    simp [hUd, hVd, hu', hv', Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec,
      dotProduct, mul_comm]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

/- English proof (translation)
Establish `hth : ∀ i, min p q ≤ i → Real.tanh (t i) = 0` using `fun i hi => by simp [ht i hi]`. Establish `hc : ∀ x : ℝ, Real.cosh x ^ 2 = (2 : ℝ)⁻¹ * (1 + Real.cosh (2 * x))` using `fun x => by`. Rewrite using `[Real.cosh_two_mul, Real.cosh_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ x : ℝ, Real.sinh x * Real.cosh x = (2 : ℝ)⁻¹ * Real.sinh (2 * x)` using `fun x => by`.

Rewrite using `[Real.sinh_two_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hct : ∀ x : ℝ, Real.tanh x * Real.cosh x ^ 2 = (2 : ℝ)⁻¹ * Real.sinh (2 * x)` using `fun x => by`. Rewrite using `[Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]`. Use `(Real.cosh_pos x).ne'` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `hd : ∀ x : ℝ, Real.tanh x * (Real.sinh x * Real.cosh x) + 1 = (2 : ℝ)⁻¹ * (1 + Real.cosh (2 * x))` using `fun x => by`. Rewrite using `[Real.tanh_eq_sinh_div_cosh, ← hc, Real.cosh_sq]`. Use `(Real.cosh_pos x).ne'` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Use `set A : Matrix (Fin p) (Fin p) ℂ := Matrix.diagonal fun i => ((Real.cosh (t i) ^ 2 : ℝ) : ℂ)`. Use `set B : Matrix (Fin p) (Fin q) ℂ := GlobalTheory.FockDecay.rectDiag p q fun i => Real.sinh (t i) * Real.cosh (t i)`. Use `set C : Matrix (Fin q) (Fin p) ℂ := (GlobalTheory.FockDecay.rectDiag p q fun i => Real.tanh (t i))ᴴ`. Establish `hM : (2 : ℂ)⁻¹ • (1 + GlobalTheory.FockDecay.hypMat p q t 2) = Matrix.fromBlocks 1 0 C 1 * Matrix.fromBlocks A B 0 1`. Rewrite using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, GlobalTheory.FockDecay.hypMat, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]`.

Simplify using `only [Matrix.one_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_zero]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [A, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]`. Use `split_ifs with h`.

Rewrite using `[hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Simplify using `only [B, GlobalTheory.FockDecay.rectDiag, Matrix.smul_apply, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Use extensionality with `i j`. Simplify using `only [C, A, GlobalTheory.FockDecay.rectDiag, Matrix.smul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.mul_diagonal]`. Use `split_ifs with h`. Simplify using `only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]`.

Rewrite using `[← Complex.ofReal_mul, hct, h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.FockDecay.ct_mul_rectDiag _ _ hth]`.

Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]`. Use `split_ifs with h`. Establish `e` using `congrArg (fun r : ℝ => (r : ℂ)) (hd (t i))`. Move the coercions through the operations in `at e ⊢`.

Rewrite using `[smul_eq_mul]`. Take the linear combination `(-1 : ℂ) * e`. Simplify using the standard rewrite rules. Rewrite using `[hM, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_diagonal]`. Simplify using `only [Matrix.det_one, one_mul, mul_one]`.

Establish `key : ∏ i : Fin p, Real.cosh (t i) ^ 2 = (∏ i ∈ Finset.range (min p q), Real.cosh (t i)) ^ 2`. Rewrite using `[Finset.prod_pow, Fin.prod_univ_eq_prod_range (fun i => Real.cosh (t i)) p]`. Use `congr 1`. Use `symm`. Apply `Finset.prod_subset (Finset.range_mono (min_le_left p q))` to reduce the goal to its premises.

Introduce `i hi hni`. Simplify using `only [Finset.mem_range, not_lt] at hi hni`. Rewrite using `[ht i hni, Real.cosh_zero]`. Rewrite using `[← key, Complex.ofReal_prod]`.
-/
theorem det_half_one_add_hypMat (p q : ℕ) (t : ℕ → ℝ) (ht : ∀ i, min p q ≤ i → t i = 0) :
    ((2 : ℂ)⁻¹ • (1 + GlobalTheory.FockDecay.hypMat p q t 2)).det =
      (((∏ i ∈ Finset.range (min p q), Real.cosh (t i)) ^ 2 : ℝ) : ℂ) := by
  have hth : ∀ i, min p q ≤ i → Real.tanh (t i) = 0 := fun i hi => by simp [ht i hi]
  have hc : ∀ x : ℝ, Real.cosh x ^ 2 = (2 : ℝ)⁻¹ * (1 + Real.cosh (2 * x)) := fun x => by
    rw [Real.cosh_two_mul, Real.cosh_sq]; ring
  have hs : ∀ x : ℝ, Real.sinh x * Real.cosh x = (2 : ℝ)⁻¹ * Real.sinh (2 * x) := fun x => by
    rw [Real.sinh_two_mul]; ring
  have hct : ∀ x : ℝ, Real.tanh x * Real.cosh x ^ 2 = (2 : ℝ)⁻¹ * Real.sinh (2 * x) := fun x => by
    rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    have := (Real.cosh_pos x).ne'
    field_simp
  have hd : ∀ x : ℝ, Real.tanh x * (Real.sinh x * Real.cosh x) + 1 = (2 : ℝ)⁻¹ * (1 + Real.cosh (2 * x)) :=
    fun x => by
    rw [Real.tanh_eq_sinh_div_cosh, ← hc, Real.cosh_sq]
    have := (Real.cosh_pos x).ne'
    field_simp
  set A : Matrix (Fin p) (Fin p) ℂ := Matrix.diagonal fun i => ((Real.cosh (t i) ^ 2 : ℝ) : ℂ)
  set B : Matrix (Fin p) (Fin q) ℂ := GlobalTheory.FockDecay.rectDiag p q fun i => Real.sinh (t i) * Real.cosh (t i)
  set C : Matrix (Fin q) (Fin p) ℂ := (GlobalTheory.FockDecay.rectDiag p q fun i => Real.tanh (t i))ᴴ
  have hM : (2 : ℂ)⁻¹ • (1 + GlobalTheory.FockDecay.hypMat p q t 2) =
      Matrix.fromBlocks 1 0 C 1 * Matrix.fromBlocks A B 0 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, GlobalTheory.FockDecay.hypMat, Matrix.fromBlocks_add,
      Matrix.fromBlocks_smul]
    simp only [Matrix.one_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_zero]
    congr 1
    · ext i j
      simp only [A, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs with h
      · rw [hc]; push_cast; ring
      · simp
    · ext i j
      simp only [B, GlobalTheory.FockDecay.rectDiag, Matrix.smul_apply, Matrix.of_apply]
      split_ifs with h
      · rw [hs]; push_cast; ring
      · simp
    · ext i j
      simp only [C, A, GlobalTheory.FockDecay.rectDiag, Matrix.smul_apply, Matrix.of_apply,
        Matrix.conjTranspose_apply, Matrix.mul_diagonal]
      split_ifs with h
      · simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
        rw [← Complex.ofReal_mul, hct, h]; push_cast; ring
      · simp
    · rw [GlobalTheory.FockDecay.ct_mul_rectDiag _ _ hth]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs with h
      · have e := congrArg (fun r : ℝ => (r : ℂ)) (hd (t i))
        push_cast at e ⊢
        rw [smul_eq_mul]
        linear_combination (-1 : ℂ) * e
      · simp
  rw [hM, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Matrix.det_diagonal]
  simp only [Matrix.det_one, one_mul, mul_one]
  have key : ∏ i : Fin p, Real.cosh (t i) ^ 2 = (∏ i ∈ Finset.range (min p q), Real.cosh (t i)) ^ 2 := by
    rw [Finset.prod_pow, Fin.prod_univ_eq_prod_range (fun i => Real.cosh (t i)) p]
    congr 1
    symm
    apply Finset.prod_subset (Finset.range_mono (min_le_left p q))
    intro i hi hni
    simp only [Finset.mem_range, not_lt] at hi hni
    rw [ht i hni, Real.cosh_zero]
  rw [← key, Complex.ofReal_prod]

/- English proof (translation)
Set `e : {i // ε i = true} ⊕ {i // ε i = false} ≃ Fin n` to `(Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun i => by simp))).trans (Equiv.sumCompl (fun i => ε i = true))`. Establish `he1 : ∀ a : {i // ε i = true}, e (Sum.inl a) = a.1` using `fun a => rfl`. Establish `he2 : ∀ b : {i // ε i = false}, e (Sum.inr b) = b.1` using `fun b => rfl`. Use `set x := offBlock ε X with hxd`. Establish `hX' : Matrix.reindex e.symm e.symm X = Matrix.fromBlocks 0 x xᴴ 0`.

Use extensionality with `(a|a) (b|b)`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he1, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]`. Conclude with `hX.2 _ _ (by rw [a.2, b.2])`. Simplify using `[x, offBlock, he1, he2]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he1, he2, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, x, offBlock, Matrix.of_apply]`.

Conclude with `(hX.1.apply _ _).symm`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he2, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]`. Conclude with `hX.2 _ _ (by rw [a.2, b.2])`. Establish `hdet1 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)).det = ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0) * NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0))).det`. Rewrite using `[← Matrix.det_reindex_self e.symm, ← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_smul, map_add, map_one, map_mul, Matrix.coe_reindexAlgEquiv, ← GlobalTheory.FockEmbExp.exp_reindex', hX']`.

Use `set fm := Fintype.equivFin {i // ε i = true}`. Use `set fk := Fintype.equivFin {i // ε i = false}`. Use `set p := Fintype.card {i // ε i = true}`. Use `set q := Fintype.card {i // ε i = false}`. Take `⟨U, hU, V, hV, hx⟩` from `exists_svd_equiv fm fk x`.

Use `set D := Matrix.of (fun a b => if ((fm a : ℕ) = (fk b : ℕ)) then (((Matrix.toEuclideanLin x).singularValues (fm a) : ℝ) : ℂ) else 0) with hDd`. Use `set t : ℕ → ℝ := fun i => singVal ε X i with htd`. Establish `ht : ∀ i, min p q ≤ i → t i = 0`. Introduce `i hi`. Simplify using `only [htd, singVal]`.

Break down `le_min_iff.mp (le_refl (min p q)) with ⟨h1, h2⟩` into its components or cases. Distinguish the cases in `hq : q ≤ i`. Apply `LinearMap.singularValues_of_finrank_le` to reduce the goal to its premises. Simplify `hq` using `[q]`. Establish `hp : p ≤ i` using `by omega`.

Rewrite using `[LinearMap.singularValues_eq_zero_iff_le_finrank_range]`. Use `le_trans (Submodule.finrank_le _) ?_` and prove the remaining obligations. Simplify `hp` using `[p]`. Use `set K : Matrix ({i // ε i = true} ⊕ {i // ε i = false}) ({i // ε i = true} ⊕ {i // ε i = false}) ℂ := Matrix.fromBlocks U 0 0 V with hKd`. Establish `hUU : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`.

Establish `hUU' : Uᴴ * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hVV : V * Vᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hV`. Establish `hVV' : Vᴴ * V = 1` using `Matrix.mem_unitaryGroup_iff'.mp hV`. Establish `hKK : K * Kᴴ = 1`. Simplify using `[hKd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU, hVV]`.

Establish `hKK' : Kᴴ * K = 1`. Simplify using `[hKd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU', hVV']`. Establish `hKinv : K⁻¹ = Kᴴ` using `Matrix.inv_eq_left_inv hKK'`. Establish `hKu : IsUnit K` using `(Matrix.isUnit_iff_isUnit_det K).mpr (Matrix.isUnit_det_of_right_inverse hKK)`. Use `set Y := Matrix.fromBlocks 0 D Dᴴ 0 with hYd`.

Establish `hXY : Matrix.fromBlocks 0 x xᴴ 0 = K * Y * K⁻¹`. Rewrite using `[hKinv, hx]`. Simplify using `[hKd, hYd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `hdet2 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0) * NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0))).det = ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp ((2 : ℝ) • Y))).det`. Rewrite using `[hXY, Matrix.exp_conj K Y hKu]`.

Establish `h1 : K * NormedSpace.exp Y * K⁻¹ * (K * NormedSpace.exp Y * K⁻¹) = K * (NormedSpace.exp Y * NormedSpace.exp Y) * K⁻¹`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det K).mp hKu)]`. Establish `h2 : (2 : ℂ)⁻¹ • (1 + K * (NormedSpace.exp Y * NormedSpace.exp Y) * K⁻¹) = K * ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp Y * NormedSpace.exp Y)) * K⁻¹`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det K).mp hKu)]`. Rewrite using `[h1, h2, Matrix.det_conj hKu, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), two_smul]`.

Set `σ' : {i // ε i = true} ⊕ {i // ε i = false} ≃ Fin p ⊕ Fin q` to `Equiv.sumCongr fm fk`. Establish `hYP : Matrix.reindex σ' σ' Y = GlobalTheory.FockDecay.diagP p q t`. Use extensionality with `(a|a) (b|b)`. Simplify using `[σ', hYd, GlobalTheory.FockDecay.diagP]`. Simplify using `[σ', hYd, hDd, GlobalTheory.FockDecay.diagP, GlobalTheory.FockDecay.rectDiag, htd, singVal, x]`.

Simplify using `[σ', hYd, hDd, GlobalTheory.FockDecay.diagP, GlobalTheory.FockDecay.rectDiag, htd, singVal, x]`. Simplify using `[σ', hYd, GlobalTheory.FockDecay.diagP]`. Establish `hs : Matrix.reindex σ' σ' ((2 : ℝ) • Y) = (2 : ℝ) • GlobalTheory.FockDecay.diagP p q t`. Rewrite using `[← hYP]`. Use `ext`.

Simplify using the standard rewrite rules. Establish `hdet3 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp ((2 : ℝ) • Y))).det = ((2 : ℂ)⁻¹ • (1 + GlobalTheory.FockDecay.hypMat p q t 2)).det`. Rewrite using `[← Matrix.det_reindex_self σ', ← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_smul, map_add, map_one, Matrix.coe_reindexAlgEquiv, ← GlobalTheory.FockEmbExp.exp_reindex', hs, GlobalTheory.FockDecay.exp_diagP t ht]`. Rewrite using `[hdet1, hdet2, hdet3, det_half_one_add_hypMat p q t ht]`. Both sides reduce to the same expression.
-/
theorem det_half_one_add_exp_mul_exp (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsInP ε X) :
    ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)).det = ((coshProd ε X ^ 2 : ℝ) : ℂ) := by
  classical
  let e : {i // ε i = true} ⊕ {i // ε i = false} ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun i => by simp))).trans
      (Equiv.sumCompl (fun i => ε i = true))
  have he1 : ∀ a : {i // ε i = true}, e (Sum.inl a) = a.1 := fun a => rfl
  have he2 : ∀ b : {i // ε i = false}, e (Sum.inr b) = b.1 := fun b => rfl
  set x := offBlock ε X with hxd
  have hX' : Matrix.reindex e.symm e.symm X = Matrix.fromBlocks 0 x xᴴ 0 := by
    ext (a|a) (b|b)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he1,
        Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact hX.2 _ _ (by rw [a.2, b.2])
    · simp [x, offBlock, he1, he2]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he1, he2,
        Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, x, offBlock, Matrix.of_apply]
      exact (hX.1.apply _ _).symm
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, he2,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact hX.2 _ _ (by rw [a.2, b.2])

  have hdet1 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)).det =
      ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0) *
        NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0))).det := by
    rw [← Matrix.det_reindex_self e.symm, ← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_smul, map_add, map_one,
      map_mul, Matrix.coe_reindexAlgEquiv, ← GlobalTheory.FockEmbExp.exp_reindex', hX']

  set fm := Fintype.equivFin {i // ε i = true}
  set fk := Fintype.equivFin {i // ε i = false}
  set p := Fintype.card {i // ε i = true}
  set q := Fintype.card {i // ε i = false}
  obtain ⟨U, hU, V, hV, hx⟩ := exists_svd_equiv fm fk x
  set D := Matrix.of (fun a b => if ((fm a : ℕ) = (fk b : ℕ)) then
        (((Matrix.toEuclideanLin x).singularValues (fm a) : ℝ) : ℂ) else 0) with hDd
  set t : ℕ → ℝ := fun i => singVal ε X i with htd
  have ht : ∀ i, min p q ≤ i → t i = 0 := by
    intro i hi
    simp only [htd, singVal]
    rcases le_min_iff.mp (le_refl (min p q)) with ⟨h1, h2⟩
    by_cases hq : q ≤ i
    · apply LinearMap.singularValues_of_finrank_le
      simpa [q] using hq
    · have hp : p ≤ i := by omega
      rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
      refine le_trans (Submodule.finrank_le _) ?_
      simpa [p] using hp
  set K : Matrix ({i // ε i = true} ⊕ {i // ε i = false}) ({i // ε i = true} ⊕ {i // ε i = false}) ℂ :=
    Matrix.fromBlocks U 0 0 V with hKd
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hUU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hVV' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hKK : K * Kᴴ = 1 := by
    simp [hKd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU, hVV]
  have hKK' : Kᴴ * K = 1 := by
    simp [hKd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU', hVV']
  have hKinv : K⁻¹ = Kᴴ := Matrix.inv_eq_left_inv hKK'
  have hKu : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (Matrix.isUnit_det_of_right_inverse hKK)
  set Y := Matrix.fromBlocks 0 D Dᴴ 0 with hYd
  have hXY : Matrix.fromBlocks 0 x xᴴ 0 = K * Y * K⁻¹ := by
    rw [hKinv, hx]
    simp [hKd, hYd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  have hdet2 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0) *
        NormedSpace.exp (Matrix.fromBlocks 0 x xᴴ 0))).det =
      ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp ((2 : ℝ) • Y))).det := by
    rw [hXY, Matrix.exp_conj K Y hKu]
    have h1 : K * NormedSpace.exp Y * K⁻¹ * (K * NormedSpace.exp Y * K⁻¹) =
        K * (NormedSpace.exp Y * NormedSpace.exp Y) * K⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det K).mp hKu)]
    have h2 : (2 : ℂ)⁻¹ • (1 + K * (NormedSpace.exp Y * NormedSpace.exp Y) * K⁻¹) =
        K * ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp Y * NormedSpace.exp Y)) * K⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det K).mp hKu)]
    rw [h1, h2, Matrix.det_conj hKu, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), two_smul]

  let σ' : {i // ε i = true} ⊕ {i // ε i = false} ≃ Fin p ⊕ Fin q := Equiv.sumCongr fm fk
  have hYP : Matrix.reindex σ' σ' Y = GlobalTheory.FockDecay.diagP p q t := by
    ext (a|a) (b|b)
    · simp [σ', hYd, GlobalTheory.FockDecay.diagP]
    · simp [σ', hYd, hDd, GlobalTheory.FockDecay.diagP, GlobalTheory.FockDecay.rectDiag, htd, singVal, x]
    · simp [σ', hYd, hDd, GlobalTheory.FockDecay.diagP, GlobalTheory.FockDecay.rectDiag, htd, singVal, x]
    · simp [σ', hYd, GlobalTheory.FockDecay.diagP]
  have hs : Matrix.reindex σ' σ' ((2 : ℝ) • Y) = (2 : ℝ) • GlobalTheory.FockDecay.diagP p q t := by
    rw [← hYP]; ext; simp
  have hdet3 : ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp ((2 : ℝ) • Y))).det =
      ((2 : ℂ)⁻¹ • (1 + GlobalTheory.FockDecay.hypMat p q t 2)).det := by
    rw [← Matrix.det_reindex_self σ', ← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_smul, map_add, map_one,
      Matrix.coe_reindexAlgEquiv, ← GlobalTheory.FockEmbExp.exp_reindex', hs, GlobalTheory.FockDecay.exp_diagP t ht]
  rw [hdet1, hdet2, hdet3, det_half_one_add_hypMat p q t ht]
  rfl

end GlobalTheory.DetExpP
