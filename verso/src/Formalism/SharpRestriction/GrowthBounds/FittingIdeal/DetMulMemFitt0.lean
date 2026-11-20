import ReciprocityTheory.DualLattices.MatEquivApply
import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.HasLenCokerDet
import Formalism.LocalToGlobal.CharacterGerms.ExistsStrictMonoMinor

noncomputable section

open Matrix

namespace Formalism.MainNotions.G.ValuationFitting

open ReciprocityTheory.PGsh.Up

section general

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using `only [Matrix.det_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]`. Repeatedly rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, mul_smul_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_eq_sum {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det = ∑ f : Fin m → Fin h, (∏ i, W (f i) i) * (α.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[det_mul_eq_sum]`. Use `Ideal.sum_mem _ fun f _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨f, rfl⟩)` and prove the remaining obligations.
-/
theorem det_mul_mem_fitt0 {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α := by
  rw [det_mul_eq_sum]
  refine Ideal.sum_mem _ fun f _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨f, rfl⟩)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem mul_submatrix_id {a b c e : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (g : Fin e → Fin c) : (A * B).submatrix id g = A * B.submatrix id g := by
  ext i j
  simp [Matrix.mul_apply]

def Em (R : Type) [CommRing R] (m h : ℕ) : Matrix (Fin m) (Fin h) R :=
  Matrix.of fun j k => if (k : ℕ) = (j : ℕ) then 1 else 0

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Em, Matrix.of_apply]`. Use `split_ifs with hj`. Rewrite using `[Finset.sum_eq_single ⟨j, hj⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg (fun e => hb (Fin.ext e)), zero_mul]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`.

Use `b.isLt` as an intermediate fact. Rewrite using `[if_neg (by omega), zero_mul]`.
-/
theorem Em_mulVec {m h : ℕ} (w : Fin h → R) (j : Fin m) :
    (Em R m h *ᵥ w) j = if hj : (j : ℕ) < h then w ⟨j, hj⟩ else 0 := by
  simp only [Matrix.mulVec, dotProduct, Em, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun e => hb (Fin.ext e)), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    have := b.isLt
    rw [if_neg (by omega), zero_mul]

/- English proof (translation)
Use extensionality with `j k`. Simplify using `only [Em, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.coe_castLE, Matrix.one_apply]`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (fun e => hjk (Fin.ext e.symm)), if_neg hjk]`.
-/
theorem Em_castLE {m h : ℕ} (hmh : m ≤ h) : (Em R m h).submatrix id (Fin.castLE hmh) = 1 := by
  ext j k
  simp only [Em, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.coe_castLE, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · rw [if_neg (fun e => hjk (Fin.ext e.symm)), if_neg hjk]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Take `⟨P, Q, a, hP, hQ, hPAQ⟩` from `Smith.smith_mat hv m h α`. Use `set a' : Fin m → R := fun j => if (j : ℕ) < h then a j else 0 with ha'`. Establish `hD : P * α * Q = Matrix.diagonal a' * Em R m h`. Use extensionality with `j k`. Rewrite using `[hPAQ, Matrix.diagonal_mul, Em, Matrix.of_apply]`.

Distinguish the cases in `hkj : (k : ℕ) = (j : ℕ)`. Establish `hj : (j : ℕ) < h` using `hkj ▸ k.isLt`. Simplify using `[hkj, ha', hj]`. Simplify using `[hkj]`. Use `⟨P, Q, a', hP, hQ, hD, fun j hj => by simp [ha', not_lt.mpr hj], ?_⟩` and prove the remaining obligations.

Establish `hQs : LinearMap.range Q.mulVecLin = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `y`. Use `⟨Q⁻¹ *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]`.

Set `eP : (Fin m → R) ≃ₗ[R] (Fin m → R)` to `Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP)`. Establish `h1 : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) = LinearMap.range (P * α * Q).mulVecLin`. Rewrite using `[← LinearMap.range_comp, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hQs, Matrix.mulVecLin_mul]`. Both sides reduce to the same expression. Establish `h2 : LinearMap.range (Matrix.diagonal a' * Em R m h).mulVecLin = Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R))`.

Use extensionality with `y`. Simplify using `only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩ j`. Use `⟨(Em R m h *ᵥ w) j, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, mul_comm]`. Introduce `hy choose t ht using hy`. Use `⟨fun k => if hk : (k : ℕ) < m then t ⟨k, hk⟩ else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Em_mulVec, ← ht j]`.

Apply the tactic sequence `by_cases hj : (j : ℕ) < h <;> simp [ha', hj, mul_comm]`. Establish `hrange : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) = Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R))`. Rewrite using `[h1, hD, h2]`. Set `e` to `Submodule.Quotient.equiv _ _ eP hrange`. Take `⟨d, c, ⟨e0⟩, hc⟩` from `ReciprocityTheory.PGsh.Up.hasLen_pi v a'`.

Conclude with `(ReciprocityTheory.PGsh.Up.hasLen_unique hv hx ⟨d, c, ⟨e.trans e0⟩, hc⟩).symm`.
-/
theorem smith_data (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin h) (Fin h) R) (a' : Fin m → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * α * Q = Matrix.diagonal a' * Em R m h ∧
      (∀ j : Fin m, h ≤ (j : ℕ) → a' j = 0) ∧ ∏ j, v (algebraMap R C (a' j)) = x := by
  obtain ⟨P, Q, a, hP, hQ, hPAQ⟩ := Smith.smith_mat hv m h α
  set a' : Fin m → R := fun j => if (j : ℕ) < h then a j else 0 with ha'
  have hD : P * α * Q = Matrix.diagonal a' * Em R m h := by
    ext j k
    rw [hPAQ, Matrix.diagonal_mul, Em, Matrix.of_apply]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : (j : ℕ) < h := hkj ▸ k.isLt
      simp [hkj, ha', hj]
    · simp [hkj]
  refine ⟨P, Q, a', hP, hQ, hD, fun j hj => by simp [ha', not_lt.mpr hj], ?_⟩
  have hQs : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨Q⁻¹ *ᵥ y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]
  let eP : (Fin m → R) ≃ₗ[R] (Fin m → R) := Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP)
  have h1 : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      LinearMap.range (P * α * Q).mulVecLin := by
    rw [← LinearMap.range_comp, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hQs,
      Matrix.mulVecLin_mul]
    rfl
  have h2 : LinearMap.range (Matrix.diagonal a' * Em R m h).mulVecLin =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    ext y
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ, true_implies,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩ j
      refine ⟨(Em R m h *ᵥ w) j, ?_⟩
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, mul_comm]
    · intro hy
      choose t ht using hy
      refine ⟨fun k => if hk : (k : ℕ) < m then t ⟨k, hk⟩ else 0, ?_⟩
      funext j
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Em_mulVec, ← ht j]
      by_cases hj : (j : ℕ) < h <;> simp [ha', hj, mul_comm]
  have hrange : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    rw [h1, hD, h2]
  let e := Submodule.Quotient.equiv _ _ eP hrange
  obtain ⟨d, c, ⟨e0⟩, hc⟩ := ReciprocityTheory.PGsh.Up.hasLen_pi v a'
  exact (ReciprocityTheory.PGsh.Up.hasLen_unique hv hx ⟨d, c, ⟨e.trans e0⟩, hc⟩).symm

/- English proof (translation)
Take `⟨P, Q, a', hP, hQ, hD, hz, hx'⟩` from `smith_data hv α hx`. Distinguish the cases in `hmh : m ≤ h`. Use `⟨(α * Q.submatrix id (Fin.castLE hmh)).det, det_mul_mem_fitt0 _ _, ?_⟩` and prove the remaining obligations. Establish `hαQ : α * Q = P⁻¹ * (Matrix.diagonal a' * Em R m h)`. Rewrite using `[← hD, Matrix.mul_assoc P α Q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]`.

Rewrite using `[← mul_submatrix_id, hαQ, mul_submatrix_id, mul_submatrix_id, Em_castLE hmh, Matrix.mul_one, Matrix.det_mul, Matrix.det_diagonal]`. Simplify using `only [map_mul, map_prod]`. Rewrite using `[hv.one_of_isUnit (Matrix.isUnit_nonsing_inv_det P hP), one_mul, hx']`. Use `push_neg at hmh`. Use `⟨0, Ideal.zero_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero, map_zero, ← hx']`. Use `symm`. Apply `Finset.prod_eq_zero (Finset.mem_univ ⟨h, hmh⟩)` to reduce the goal to its premises. Rewrite using `[hz ⟨h, hmh⟩ le_rfl, map_zero, map_zero]`.
-/
theorem fitt_ge (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ y ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α, v (algebraMap R C y) = x := by
  obtain ⟨P, Q, a', hP, hQ, hD, hz, hx'⟩ := smith_data hv α hx
  by_cases hmh : m ≤ h
  · refine ⟨(α * Q.submatrix id (Fin.castLE hmh)).det, det_mul_mem_fitt0 _ _, ?_⟩
    have hαQ : α * Q = P⁻¹ * (Matrix.diagonal a' * Em R m h) := by
      rw [← hD, Matrix.mul_assoc P α Q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    rw [← mul_submatrix_id, hαQ, mul_submatrix_id, mul_submatrix_id, Em_castLE hmh, Matrix.mul_one,
      Matrix.det_mul, Matrix.det_diagonal]
    simp only [map_mul, map_prod]
    rw [hv.one_of_isUnit (Matrix.isUnit_nonsing_inv_det P hP), one_mul, hx']
  · push_neg at hmh
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [map_zero, map_zero, ← hx']
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨h, hmh⟩)
    rw [hz ⟨h, hmh⟩ le_rfl, map_zero, map_zero]

/- English proof (translation)
Introduce `g`. Take `⟨P, Q, a', hP, hQ, hD, _, hx'⟩` from `smith_data hv α hx`. Establish `hα : P⁻¹ * (P * α * Q) * Q⁻¹ = α`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]`. Establish `hα' : α = P⁻¹ * (Matrix.diagonal a' * Em R m h * Q⁻¹)`.

Rewrite using `[← hD, ← Matrix.mul_assoc]`. Conclude with `hα.symm`. Establish `e1` using `hv.map_le_one (P⁻¹).det`. Establish `e2` using `hv.map_le_one ((Em R m h * Q⁻¹).submatrix id g).det`. Rewrite using `[hα', mul_submatrix_id, Matrix.det_mul, Matrix.mul_assoc, mul_submatrix_id, Matrix.det_mul, Matrix.det_diagonal, ← hx']`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_prod]`. Use `_ ≤ 1 * ((∏ j, v (algebraMap R C (a' j))) * 1) := mul_le_mul' e1 (mul_le_mul' le_rfl e2)`. Use `_ = _ := by rw [one_mul, mul_one]`.
-/
theorem fitt_le (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∀ g : Fin m → Fin h, v (algebraMap R C (α.submatrix id g).det) ≤ x := by
  intro g
  obtain ⟨P, Q, a', hP, hQ, hD, _, hx'⟩ := smith_data hv α hx
  have hα : P⁻¹ * (P * α * Q) * Q⁻¹ = α := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
  have hα' : α = P⁻¹ * (Matrix.diagonal a' * Em R m h * Q⁻¹) := by
    rw [← hD, ← Matrix.mul_assoc]
    exact hα.symm
  have e1 := hv.map_le_one (P⁻¹).det
  have e2 := hv.map_le_one ((Em R m h * Q⁻¹).submatrix id g).det
  rw [hα', mul_submatrix_id, Matrix.det_mul, Matrix.mul_assoc, mul_submatrix_id, Matrix.det_mul,
    Matrix.det_diagonal, ← hx']
  calc _ = v (algebraMap R C (P⁻¹).det) * ((∏ j, v (algebraMap R C (a' j))) *
        v (algebraMap R C ((Em R m h * Q⁻¹).submatrix id g).det)) := by
        simp only [map_mul, map_prod]
    _ ≤ 1 * ((∏ j, v (algebraMap R C (a' j))) * 1) := mul_le_mul' e1 (mul_le_mul' le_rfl e2)
    _ = _ := by rw [one_mul, mul_one]

end Formalism.MainNotions.G.ValuationFitting
