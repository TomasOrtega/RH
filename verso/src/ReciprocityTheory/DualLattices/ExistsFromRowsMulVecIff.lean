import ReciprocityTheory.DualLattices.LenIdBStatement
import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]`.
-/
private lemma smulMV {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R) (v : μ → R) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `hdet : A.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ hc h1.symm`.

Establish `key : A.det • (B * A) = A.det • (c • (1 : Matrix n n S))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]`. Use `_ = A.adjugate * ((A * B) * A) := by simp only [Matrix.mul_assoc]`. Use `_ = A.adjugate * (c • A) := by rw [h, Matrix.smul_mul, Matrix.one_mul]`.

Use `_ = c • (A.adjugate * A) := by rw [Matrix.mul_smul]`. Use `_ = A.det • (c • (1 : Matrix n n S)) := by rw [Matrix.adjugate_mul]; exact smul_comm _ _ _`. Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun key i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h2`.

Simplify `mul_left_cancel₀ hdet h2` using `only [Matrix.smul_apply, smul_eq_mul]`.
-/
private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]
    [IsDomain S] {A B : Matrix n n S} {c : S} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n S)) :
    B * A = c • (1 : Matrix n n S) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : A.det • (B * A) = A.det • (c • (1 : Matrix n n S)) := by
    calc A.det • (B * A) = (A.adjugate * A) * (B * A) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = A.adjugate * ((A * B) * A) := by simp only [Matrix.mul_assoc]
      _ = A.adjugate * (c • A) := by rw [h, Matrix.smul_mul, Matrix.one_mul]
      _ = c • (A.adjugate * A) := by rw [Matrix.mul_smul]
      _ = A.det • (c • (1 : Matrix n n S)) := by rw [Matrix.adjugate_mul]; exact smul_comm _ _ _
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa only [Matrix.smul_apply, smul_eq_mul] using mul_left_cancel₀ hdet h2

/- English proof (translation)
Establish `hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ`. Simplify `congrArg Matrix.transpose hform` using `only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul]`. Establish `hEF : Eᵀ * (Eᵀ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])`. Establish `hP : Matrix.fromCols Htᵀ Btᵀ * Matrix.fromRows (Bt * (Eᵀ)⁻¹) (-(Ht * (Eᵀ)⁻¹)) = cp • (1 : Matrix (Ix g) (Ix g) R)`. Rewrite using `[Matrix.fromCols_mul_fromRows, Matrix.mul_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.sub_mul, hT1, Matrix.smul_mul, hEF]`.

Establish `hQ` using `matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero hcp hP`. Rewrite `hQ` using `[Matrix.fromRows_mul_fromCols]`. Establish `h1 : (cp • (1 : Matrix (Ix g) (Ix g) R)) = Matrix.fromBlocks (cp • 1) 0 0 (cp • 1)`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`. Rewrite `hQ` using `[h1, Matrix.fromBlocks_inj]`.

Conclude with `hQ`.
-/
private theorem block_products_of_transpose_form_eq_smul [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R}
    {E : Matrix (Ix g) (Ix g) R} {cp : R} (hcp : cp ≠ 0) (hE : IsUnit E.det)
    (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Bt * (Eᵀ)⁻¹ * Htᵀ = cp • 1 ∧ Bt * (Eᵀ)⁻¹ * Btᵀ = 0 ∧ -(Ht * (Eᵀ)⁻¹) * Htᵀ = 0 ∧
      -(Ht * (Eᵀ)⁻¹) * Btᵀ = cp • 1 := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  have hEF : Eᵀ * (Eᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have hP : Matrix.fromCols Htᵀ Btᵀ * Matrix.fromRows (Bt * (Eᵀ)⁻¹) (-(Ht * (Eᵀ)⁻¹)) =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.sub_mul, hT1, Matrix.smul_mul, hEF]
  have hQ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero hcp hP
  rw [Matrix.fromRows_mul_fromCols] at hQ
  have h1 : (cp • (1 : Matrix (Ix g) (Ix g) R)) = Matrix.fromBlocks (cp • 1) 0 0 (cp • 1) := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, Matrix.fromBlocks_inj] at hQ
  exact hQ

/- English proof (translation)
Take `⟨h11, -, h21, -⟩` from `block_products_of_transpose_form_eq_smul hcp hE hform`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `h21` using `[Matrix.neg_mul, neg_eq_zero, Matrix.mul_assoc]`. Conclude with `h21`. Rewrite `h11` using `[Matrix.mul_assoc]`.

Conclude with `h11`.
-/
lemma hb_facts [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Ht * ((Eᵀ)⁻¹ * Htᵀ) = 0 ∧ Bt * ((Eᵀ)⁻¹ * Htᵀ) = cp • (1 : Matrix (Fin g) (Fin g) R) := by
  obtain ⟨h11, -, h21, -⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  refine ⟨?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_zero, Matrix.mul_assoc] at h21
    exact h21
  · rw [Matrix.mul_assoc] at h11
    exact h11

variable {m : ℕ}

/- English proof (translation)
Establish `hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ`. Simplify `congrArg Matrix.transpose hform` using `only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩`. Rewrite `ht` using `[Matrix.fromRows_mulVec]`.

Establish `h1 : Ht *ᵥ (εT i *ᵥ t) = 0` using `funext fun k => by simpa using congrFun ht (Sum.inl k)`. Establish `h2 : Bt *ᵥ (εT i *ᵥ t) = x` using `funext fun k => by simpa using congrFun ht (Sum.inr k)`. Use `⟨Eᵀ *ᵥ (εT i *ᵥ t), ?_⟩` and prove the remaining obligations. Rewrite using `[← smulMV, ← hT1, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, Matrix.mulVec_zero, sub_zero]`. Introduce and unpack `⟨z, hz⟩`.

Take `⟨hHF, hBF⟩` from `hb_facts hcp hE hform`. Establish `hs1 : Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = 0`. Establish `h : cp • (Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = 0`. Rewrite using `[← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.

Rewrite using `[hHF, Matrix.zero_mulVec]`. Conclude with `(smul_eq_zero.mp h).resolve_left hcp`. Establish `hs2 : Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = x`. Establish `h : cp • (Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = cp • x`. Rewrite using `[← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]`.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[hBF, smulMV, Matrix.one_mulVec]`. Conclude with `smul_right_injective _ hcp h`. Generalize the expression as in `(Eᵀ)⁻¹ *ᵥ z = s at hs1 hs2`. Establish `e1 : Ht *ᵥ (εT i *ᵥ s) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, hHt, ← Matrix.mulVec_mulVec, hs1, Matrix.mulVec_zero]`. Establish `e2 : Bt *ᵥ (εT i *ᵥ s) = x`. Rewrite using `[Matrix.mulVec_mulVec, hBt, ← Matrix.mulVec_mulVec, hs2, hx]`. Conclude with `⟨s, by rw [Matrix.fromRows_mulVec, e1, e2]⟩`.
-/
lemma exists_fromRows_mulVec_iff [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hHt : Ht * εT i = (εL (π i))ᵀ * Ht)
    (hBt : Bt * εT i = εL i * Bt) (x : Fin g → R) (hx : εL i *ᵥ x = x) :
    (∃ t, fromRows Ht Bt *ᵥ (εT i *ᵥ t) = Sum.elim (0 : Fin g → R) x) ↔
      ∃ z, Htᵀ *ᵥ x = cp • z := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  constructor
  · rintro ⟨t, ht⟩
    rw [Matrix.fromRows_mulVec] at ht
    have h1 : Ht *ᵥ (εT i *ᵥ t) = 0 := funext fun k => by simpa using congrFun ht (Sum.inl k)
    have h2 : Bt *ᵥ (εT i *ᵥ t) = x := funext fun k => by simpa using congrFun ht (Sum.inr k)
    refine ⟨Eᵀ *ᵥ (εT i *ᵥ t), ?_⟩
    rw [← smulMV, ← hT1, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
      h2, Matrix.mulVec_zero, sub_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨hHF, hBF⟩ := hb_facts hcp hE hform
    have hs1 : Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = 0 := by
      have h : cp • (Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = 0 := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hHF, Matrix.zero_mulVec]
      exact (smul_eq_zero.mp h).resolve_left hcp
    have hs2 : Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = x := by
      have h : cp • (Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = cp • x := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hBF, smulMV, Matrix.one_mulVec]
      exact smul_right_injective _ hcp h
    generalize (Eᵀ)⁻¹ *ᵥ z = s at hs1 hs2
    have e1 : Ht *ᵥ (εT i *ᵥ s) = 0 := by
      rw [Matrix.mulVec_mulVec, hHt, ← Matrix.mulVec_mulVec, hs1, Matrix.mulVec_zero]
    have e2 : Bt *ᵥ (εT i *ᵥ s) = x := by
      rw [Matrix.mulVec_mulVec, hBt, ← Matrix.mulVec_mulVec, hs2, hx]
    exact ⟨s, by rw [Matrix.fromRows_mulVec, e1, e2]⟩

/- English proof (translation)
Introduce `f hf`. Take `⟨y, rfl⟩` from `LinearMap.mem_range.mp hf`. Take `⟨-, -, -, h22⟩` from `block_products_of_transpose_form_eq_smul hcp hE hform`. Rewrite `h22` using `[Matrix.neg_mul, Matrix.mul_assoc]`. Establish `hHt' : Ht *ᵥ (-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y))) = cp • y`.

Rewrite using `[Matrix.mulVec_neg]`. Simplify using `only [Matrix.mulVec_mulVec]`. Rewrite using `[← Matrix.neg_mulVec, h22, smulMV, Matrix.one_mulVec]`. Generalize the expression as in `-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y)) = t at hHt'`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVecLin_apply]`. Rewrite using `[Matrix.mulVec_mulVec, hHt, hπi, ← Matrix.mulVec_mulVec, hHt', Matrix.mulVec_smul]`.
-/
lemma cok_kill [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hπi : π (π i) = i)
    (hHt : ∀ j, Ht * εT j = (εL (π j))ᵀ * Ht) :
    ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), ∃ t, Ht *ᵥ (εT (π i) *ᵥ t) = cp • f := by
  intro f hf
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hf
  obtain ⟨-, -, -, h22⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  rw [Matrix.neg_mul, Matrix.mul_assoc] at h22
  have hHt' : Ht *ᵥ (-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y))) = cp • y := by
    rw [Matrix.mulVec_neg]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.neg_mulVec, h22, smulMV, Matrix.one_mulVec]
  generalize -((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y)) = t at hHt'
  refine ⟨t, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, hHt, hπi, ← Matrix.mulVec_mulVec, hHt', Matrix.mulVec_smul]

end ReciprocityTheory.PGsh.Up
