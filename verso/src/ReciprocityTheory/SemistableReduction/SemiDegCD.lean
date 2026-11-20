import ReciprocityTheory.SemistableReduction.SemiDegCC

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

/- English proof (translation)
Simplify using `only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h (a • u) w = S.c a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [HermForm.h, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem hermForm_eq_mulVec {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.h u w = ∑ b, (∑ a, S.c (u a) * S.G a b) * w b := by
  simp only [HermForm.h, Finset.sum_mul]
  rw [Finset.sum_comm]

def rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i a => z i a

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[rowMat, hdiag]`. Introduce `i j hji`. Conclude with `htri i j hji`.
-/
theorem det_rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K)
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1) : (rowMat z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [rowMat, hdiag]
  · intro i j hji
    exact htri i j hji

/- English proof (translation)
Rewrite using `[hermForm_eq_mulVec]`. Simplify using `[mulVec, dotProduct, Matrix.mul_apply, rowMat]`.
-/
theorem hermForm_rows {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (z : Fin k → Fin k → K) (i : Fin k) (v : Fin k → K) :
    S.h (z i) v = (((rowMat z).map S.c * S.G) *ᵥ v) i := by
  rw [hermForm_eq_mulVec]
  simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]

/- English proof (translation)
Establish `h` using `hin (Pi.single j a) (fun i => by`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using ha`. Simplify using `[hij])`.

Simplify `h` using `[Pi.single_apply]`.
-/
theorem smul_mem_of_split {K : Type} [Field K] [NumberField K] {k : ℕ}
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (j : Fin k) {a : K}
    (ha : a ∈ C j) : a • z j ∈ X := by
  classical
  have h := hin (Pi.single j a) (fun i => by
    by_cases hij : i = j
    · subst hij; simpa using ha
    · simp [hij])
  simpa [Pi.single_apply] using h

/- English proof (translation)
Take `⟨a, ha⟩` from `Submodule.mem_one.1 hx`. Conclude with `⟨a, ha⟩`.
-/
theorem integral_of_mem_one {K : Type} [Field K] [NumberField K] {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : IsIntegralElt x := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
  exact ⟨a, ha⟩

/- English proof (translation)
Set `M : Matrix (Fin k) (Fin k) K` to `Matrix.of fun i j => S.h (S.c (s i) • z i) (t j • z j)`. Establish `hM : M = Matrix.diagonal s * (((rowMat z).map S.c * S.G) * (rowMat z)ᵀ) * Matrix.diagonal t`. Use extensionality with `i j`. Simplify using `only [M, Matrix.of_apply, hermForm_smul_smul, S.c_invol, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[hermForm_rows]`.

Simplify using `[mulVec, dotProduct, Matrix.mul_apply, rowMat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : M.det = (∏ i, s i) * S.G.det * (∏ i, t i)`. Establish `: ((rowMat z).map S.c).det = 1`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one]`.

Rewrite using `[hM]`. Simplify using `only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, det_rowMat z htri hdiag, this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hent : ∀ i j, ∃ m : 𝓞 K, algebraMap (𝓞 K) K m = M i j` using `fun i j => hint _ (smul_mem_of_split hin i (hs i)) _ (smul_mem_of_split hin j (ht j))`. Use `choose m hm using hent`.

Establish `: M = (Matrix.of m).map (algebraMap (𝓞 K) K)`. Use extensionality with `i j`. Simplify using `[hm]`. Rewrite using `[← hdet, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`.
-/
theorem split_integral {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (hint : IsIntegralOn S X)
    (s t : Fin k → K) (hs : ∀ i, S.c (s i) ∈ C i) (ht : ∀ i, t i ∈ C i) :
    (∏ i, s i) * S.G.det * (∏ i, t i) ∈ (1 : Submodule (𝓞 K) K) := by
  let M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j => S.h (S.c (s i) • z i) (t j • z j)
  have hM : M = Matrix.diagonal s * (((rowMat z).map S.c * S.G) * (rowMat z)ᵀ) *
      Matrix.diagonal t := by
    ext i j
    simp only [M, Matrix.of_apply, hermForm_smul_smul, S.c_invol, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [hermForm_rows]
    simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]
    ring
  have hdet : M.det = (∏ i, s i) * S.G.det * (∏ i, t i) := by
    have : ((rowMat z).map S.c).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one]
    rw [hM]
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      det_rowMat z htri hdiag, this]
    ring
  have hent : ∀ i j, ∃ m : 𝓞 K, algebraMap (𝓞 K) K m = M i j := fun i j =>
    hint _ (smul_mem_of_split hin i (hs i)) _ (smul_mem_of_split hin j (ht j))
  choose m hm using hent
  have : M = (Matrix.of m).map (algebraMap (𝓞 K) K) := by
    ext i j
    simp [hm]
  rw [← hdet, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

/- English proof (translation)
Use `set Q : Matrix (Fin k) (Fin k) K := (rowMat z).map S.c * S.G with hQ`. Establish `hQdet : Q.det = S.G.det`. Rewrite using `[hQ, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one, one_mul]`. Establish `hQu : IsUnit Q.det` using `by rw [hQdet]; exact isUnit_iff_ne_zero.2 hG`. Set `y : Fin k → Fin k → K` to `fun j => Q⁻¹ *ᵥ Pi.single j (u j)`.

Establish `hQy : ∀ j, Q *ᵥ y j = Pi.single j (u j)` using `fun j => by`. Simplify using `only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mulVec]`. Establish `hy : ∀ j, y j ∈ X`. Introduce `j`. Use `hsd.2 _ fun x hx => ?_` and prove the remaining obligations.

Take `⟨t, ht, rfl⟩` from `hdec x hx`. Rewrite using `[← hermForm_conj]`. Establish `: S.h (∑ i, t i • z i) (y j) = S.c (t j) * u j`. Rewrite using `[hermForm_sum_left]`. Simplify using `only [hermForm_smul_left, hermForm_rows, ← hQ, hQy, Pi.single_apply]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `integral_of_mem_one (mem_one_map S.c ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `hu j _ (by rw [S.c_invol]; exact ht j)`.

Use `choose T hT hTy using fun j => hdec (y j) (hy j)`. Set `Tm : Matrix (Fin k) (Fin k) K` to `Matrix.of fun i j => T j i`. Establish `hY1 : (Matrix.of fun a j => y j a) = (rowMat z)ᵀ * Tm`. Use extensionality with `a j`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[hTy j]`. Simplify using `[Tm, rowMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]`. Establish `hY2 : (Matrix.of fun a j => y j a) = Q⁻¹ * Matrix.diagonal u`. Use extensionality with `a j`. Simplify using `[y, Matrix.mul_diagonal, mul_comm]`.

Establish `hdet : (∏ j, u j) = S.G.det * Tm.det`. Establish `h1` using `congrArg Matrix.det hY1`. Rewrite `h1` using `[hY2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rowMat z htri hdiag, one_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hQdet, Ring.inverse_eq_inv']`. Rewrite using `[← h1]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hdet]`. Conclude with `Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) (det_mem_prod_sub C Tm fun i j => hT j i)`.
-/
theorem split_selfDual {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hdec : ∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i)
    (hsd : IsSelfDual S X) (hG : S.G.det ≠ 0) (u : Fin k → K)
    (hu : ∀ j, ∀ w, S.c w ∈ C j → u j * w ∈ (1 : Submodule (𝓞 K) K)) :
    ∏ j, u j ∈ Submodule.span (𝓞 K) {S.G.det} * ∏ i, C i := by
  classical
  set Q : Matrix (Fin k) (Fin k) K := (rowMat z).map S.c * S.G with hQ
  have hQdet : Q.det = S.G.det := by
    rw [hQ, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_rowMat z htri hdiag, map_one, one_mul]
  have hQu : IsUnit Q.det := by rw [hQdet]; exact isUnit_iff_ne_zero.2 hG
  let y : Fin k → Fin k → K := fun j => Q⁻¹ *ᵥ Pi.single j (u j)
  have hQy : ∀ j, Q *ᵥ y j = Pi.single j (u j) := fun j => by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mulVec]
  have hy : ∀ j, y j ∈ X := by
    intro j
    refine hsd.2 _ fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hdec x hx
    rw [← hermForm_conj]
    have : S.h (∑ i, t i • z i) (y j) = S.c (t j) * u j := by
      rw [hermForm_sum_left]
      simp only [hermForm_smul_left, hermForm_rows, ← hQ, hQy, Pi.single_apply]
      simp
    rw [this]
    refine integral_of_mem_one (mem_one_map S.c ?_)
    rw [mul_comm]
    exact hu j _ (by rw [S.c_invol]; exact ht j)
  choose T hT hTy using fun j => hdec (y j) (hy j)
  let Tm : Matrix (Fin k) (Fin k) K := Matrix.of fun i j => T j i
  have hY1 : (Matrix.of fun a j => y j a) = (rowMat z)ᵀ * Tm := by
    ext a j
    simp only [Matrix.of_apply]
    rw [hTy j]
    simp [Tm, rowMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have hY2 : (Matrix.of fun a j => y j a) = Q⁻¹ * Matrix.diagonal u := by
    ext a j
    simp [y, Matrix.mul_diagonal, mul_comm]
  have hdet : (∏ j, u j) = S.G.det * Tm.det := by
    have h1 := congrArg Matrix.det hY1
    rw [hY2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rowMat z htri hdiag,
      one_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hQdet, Ring.inverse_eq_inv'] at h1
    rw [← h1]
    field_simp
  rw [hdet]
  exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _)
    (det_mem_prod_sub C Tm fun i j => hT j i)

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
