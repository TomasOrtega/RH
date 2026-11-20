import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => rfl)` and prove the remaining obligations. Apply `hz a c k` to reduce the goal to its premises.

Assume the negation of the conclusion as `hlt`. Conclude with `hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩`.
-/
lemma sub_mul_sub {i : ℕ} (h : i ≤ n) (M N : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ (a c : Fin i) (k : Fin n), i ≤ (k : ℕ) → M (Fin.castLE h a) k * N k (Fin.castLE h c) = 0) :
    (M * N).submatrix (Fin.castLE h) (Fin.castLE h) =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => rfl)
  apply hz a c k
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩

/- English proof (translation)
The claim follows from `hN h`.
-/
lemma upper_lt {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) {a k : Fin n} (h : a < k) :
    N k a = 0 := hN h

/- English proof (translation)
Establish `ht : (N.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id` using `fun a c hca => hN (show Fin.castLE h c < Fin.castLE h a from hca)`. Rewrite using `[Matrix.det_of_isUpperTriangular ht]`. Both sides reduce to the same expression.
-/
lemma det_sub_upper {i : ℕ} (h : i ≤ n) {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) :
    (N.submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ j : Fin i, N (Fin.castLE h j) (Fin.castLE h j) := by
  have ht : (N.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := fun a c hca =>
    hN (show Fin.castLE h c < Fin.castLE h a from hca)
  rw [Matrix.det_of_isUpperTriangular ht]
  rfl

/- English proof (translation)
Establish `h` using `Nat.le_of_lt_succ i.isLt`. Unfold `lminor`. Rewrite using `[sub_mul_sub h (Nᵀ * A) (N.map (starRingEnd ℂ)) (fun a c k hk => ?_), sub_mul_sub h Nᵀ A (fun a c k hk => ?_), Matrix.det_mul, Matrix.det_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose, det_sub_upper h hN]`. Use `congr 1`. Rewrite using `[show (N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) = (starRingEnd ℂ).mapMatrix (N.submatrix (Fin.castLE h) (Fin.castLE h)) from rfl, ← RingHom.map_det, det_sub_upper h hN]`.

Use `all_goals`. Establish `h1 : N k (Fin.castLE h c) = 0` using `upper_lt hN (show Fin.castLE h c < k by rw [Fin.lt_def]; simp; omega)`. Establish `h2 : N k (Fin.castLE h a) = 0` using `upper_lt hN (show Fin.castLE h a < k by rw [Fin.lt_def]; simp; omega)`. Simplify using `[h1, h2]`.
-/
lemma lminor_conj {N A : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) (i : Fin (n + 1)) :
    lminor (Nᵀ * A * N.map (starRingEnd ℂ)) i =
      (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        lminor A i *
        conj (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have h := Nat.le_of_lt_succ i.isLt
  unfold lminor
  rw [sub_mul_sub h (Nᵀ * A) (N.map (starRingEnd ℂ)) (fun a c k hk => ?_),
    sub_mul_sub h Nᵀ A (fun a c k hk => ?_), Matrix.det_mul, Matrix.det_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose,
    det_sub_upper h hN]
  · congr 1
    rw [show (N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
        (starRingEnd ℂ).mapMatrix (N.submatrix (Fin.castLE h) (Fin.castLE h)) from rfl,
      ← RingHom.map_det, det_sub_upper h hN]
  all_goals
    have h1 : N k (Fin.castLE h c) = 0 :=
      upper_lt hN (show Fin.castLE h c < k by rw [Fin.lt_def]; simp; omega)
    have h2 : N k (Fin.castLE h a) = 0 :=
      upper_lt hN (show Fin.castLE h a < k by rw [Fin.lt_def]; simp; omega)
    simp [h1, h2]

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
lemma gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Rewrite using `[gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
lemma gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
