import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerShOfKind

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {K K' : Type*} [CommRing K] [CommRing K'] {r : ℕ}

def ld (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : K := (A.submatrix Fin.castSucc Fin.castSucc).det

def Ec (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0

/- English proof (translation)
Unfold `ld`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[Ec, Fin.castSucc_ne_last]`.
-/
theorem ld_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) : ld (A + t • Ec r) = ld A := by
  unfold ld
  congr 1
  ext a b
  simp [Ec, Fin.castSucc_ne_last]

/- English proof (translation)
Establish `hE : A + t • Ec r = A.updateRow (Fin.last r) (A (Fin.last r) + t • Pi.single (Fin.last r) 1)`. Use extensionality with `a b`. Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Simplify using `[Ec]`. Simplify using `[Ec, hb]`. Simplify using `[Ec, ha]`. Rewrite using `[hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]`.

Use `congr 2`. Rewrite using `[Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]`. Establish `h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0`. Introduce `j`. Rewrite using `[Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]`.

Simplify using `only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self, Pi.single_eq_same, mul_one, Fin.succAbove_last]`. Establish `hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[Matrix.updateRow_ne (Fin.castSucc_ne_last a)]`.

Rewrite using `[hs, ld]`. Establish `hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1` using `Even.neg_one_pow ⟨_, rfl⟩`. Rewrite using `[hpow, one_mul]`.
-/
theorem det_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) :
    (A + t • Ec r).det = A.det + t * ld A := by
  have hE : A + t • Ec r = A.updateRow (Fin.last r) (A (Fin.last r) + t • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ec]
      · simp [Ec, hb]
    · simp [Ec, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
  rw [hs, ld]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

/- English proof (translation)
Unfold `ld`. Rewrite using `[show (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc from rfl, Matrix.det_smul, Fintype.card_fin]`.
-/
theorem ld_smul (c : K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (c • A) = c ^ r * ld A := by
  unfold ld
  rw [show (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc from rfl,
    Matrix.det_smul, Fintype.card_fin]

/- English proof (translation)
Unfold `ld`. Rewrite using `[← Matrix.det_transpose]`. Both sides reduce to the same expression.
-/
theorem ld_transpose (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld Aᵀ = ld A := by
  unfold ld
  rw [← Matrix.det_transpose]
  rfl

/- English proof (translation)
Unfold `ld`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem ld_map (f : K →+* K') (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (A.map f) = f (ld A) := by
  unfold ld
  rw [RingHom.map_det]
  rfl

def Cross (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop := ld A * A'.det = ld A' * A.det

/- English proof (translation)
Unfold `Cross at h ⊢`. Rewrite using `[ld_add_corner, ld_add_corner, det_add_corner, det_add_corner, ld_smul, ld_smul, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin]`. Take the linear combination `c ^ r * c ^ (r + 1) * h`.
-/
theorem cross_shift {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c t : K) :
    Cross (c • A + t • Ec r) (c • A' + t • Ec r) := by
  unfold Cross at h ⊢
  rw [ld_add_corner, ld_add_corner, det_add_corner, det_add_corner, ld_smul, ld_smul, Matrix.det_smul,
    Matrix.det_smul, Fintype.card_fin]
  linear_combination c ^ r * c ^ (r + 1) * h

/- English proof (translation)
Unfold `Cross at h ⊢`. Rewrite using `[ld_transpose, ld_transpose, Matrix.det_transpose, Matrix.det_transpose]`. Conclude with `h`.
-/
theorem cross_transpose {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') : Cross Aᵀ A'ᵀ := by
  unfold Cross at h ⊢
  rw [ld_transpose, ld_transpose, Matrix.det_transpose, Matrix.det_transpose]
  exact h

/- English proof (translation)
Unfold `Cross at h ⊢`. Establish `e1 : (A'.map f).det = f A'.det` using `(RingHom.map_det f A').symm`. Establish `e2 : (A.map f).det = f A.det` using `(RingHom.map_det f A).symm`. Rewrite using `[ld_map, ld_map, e1, e2, ← map_mul, ← map_mul, h]`.
-/
theorem cross_map (f : K →+* K') {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (A.map f) (A'.map f) := by
  unfold Cross at h ⊢
  have e1 : (A'.map f).det = f A'.det := (RingHom.map_det f A').symm
  have e2 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  rw [ld_map, ld_map, e1, e2, ← map_mul, ← map_mul, h]

/- English proof (translation)
Establish `e : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K, (Matrix.of fun a b => y b * x a * B a b) = Matrix.diagonal x * B * Matrix.diagonal y`. Introduce `B`. Use extensionality with `a b`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Expand and normalize the polynomial expressions, which then agree.

Establish `el : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ld (Matrix.diagonal x * B * Matrix.diagonal y) = (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * ld B`. Introduce `B`. Unfold `ld`. Establish `: (Matrix.diagonal x * B * Matrix.diagonal y).submatrix Fin.castSucc Fin.castSucc = Matrix.diagonal (fun i : Fin r => x i.castSucc) * B.submatrix Fin.castSucc Fin.castSucc * Matrix.diagonal (fun i : Fin r => y i.castSucc)`. Use extensionality with `a b`.

Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]`. Expand and normalize the polynomial expressions, which then agree. Unfold `Cross at h ⊢`. Rewrite using `[e, e, el, el, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]`.

Take the linear combination `(∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * (Matrix.diagonal x).det * (Matrix.diagonal y).det * h`.
-/
theorem cross_scale (x y : Fin (r + 1) → K) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (Matrix.of fun a b => y b * x a * A a b) (Matrix.of fun a b => y b * x a * A' a b) := by
  have e : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      (Matrix.of fun a b => y b * x a * B a b) = Matrix.diagonal x * B * Matrix.diagonal y := by
    intro B; ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
  have el : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      ld (Matrix.diagonal x * B * Matrix.diagonal y) = (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * ld B := by
    intro B
    unfold ld
    have : (Matrix.diagonal x * B * Matrix.diagonal y).submatrix Fin.castSucc Fin.castSucc =
        Matrix.diagonal (fun i : Fin r => x i.castSucc) * B.submatrix Fin.castSucc Fin.castSucc *
          Matrix.diagonal (fun i : Fin r => y i.castSucc) := by
      ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    ring
  unfold Cross at h ⊢
  rw [e, e, el, el, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * (Matrix.diagonal x).det *
    (Matrix.diagonal y).det * h

/- English proof (translation)
Establish `k1` using `SplitCoefficientComponents.inv_last_mul_det (A + c • (Ec (K := K) r)) hu`. Establish `k2` using `SplitCoefficientComponents.inv_last_mul_det (A' + c • (Ec (K := K) r)) hu'`. Establish `l1 : ((A + c • (Ec (K` using `K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A := ld_add_corner A c`. Establish `l2 : ((A' + c • (Ec (K` using `K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A' := ld_add_corner A' c`. Rewrite `k1` using `[l1, det_add_corner]`.

Rewrite `k2` using `[l2, det_add_corner]`. Rewrite `hu`, `hu'` using `[det_add_corner]`. Unfold `Cross at h`. Take `⟨v, hv⟩` from `hu`. Take `⟨v', hv'⟩` from `hu'`.

Establish `key : (A + c • (Ec (K` using `K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) = (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) := by`. Establish `e1 : (A + c • (Ec (K` using `K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) = ld A * (A'.det + c * ld A') := by rw [← mul_assoc, k1]`. Establish `e2 : (A' + c • (Ec (K` using `K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) = ld A' * (A.det + c * ld A) := by rw [mul_comm (A.det + _), ← mul_assoc, k2]`. Rewrite using `[e1, e2]`. Take the linear combination `h`.

Establish `hunit : IsUnit ((A.det + c * ld A) * (A'.det + c * ld A'))`. Rewrite using `[← hv, ← hv']`. Conclude with `(v * v').isUnit`. Conclude with `hunit.mul_right_cancel key`.
-/
theorem kappa_eq {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c : K)
    (hu : IsUnit (A + c • (Ec (K := K) r)).det) (hu' : IsUnit (A' + c • (Ec (K := K) r)).det) :
    (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) = (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) := by
  have k1 := SplitCoefficientComponents.inv_last_mul_det (A + c • (Ec (K := K) r)) hu
  have k2 := SplitCoefficientComponents.inv_last_mul_det (A' + c • (Ec (K := K) r)) hu'
  have l1 : ((A + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A := ld_add_corner A c
  have l2 : ((A' + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A' := ld_add_corner A' c
  rw [l1, det_add_corner] at k1
  rw [l2, det_add_corner] at k2
  rw [det_add_corner] at hu hu'
  unfold Cross at h
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  have key : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
      (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    have e1 : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A * (A'.det + c * ld A') := by rw [← mul_assoc, k1]
    have e2 : (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A' * (A.det + c * ld A) := by rw [mul_comm (A.det + _), ← mul_assoc, k2]
    rw [e1, e2]
    linear_combination h
  have hunit : IsUnit ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    rw [← hv, ← hv']; exact (v * v').isUnit
  exact hunit.mul_right_cancel key

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
