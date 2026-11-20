import ReciprocityTheory.DualLattices.DiscriminantColengthStatementHolds

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] {v : Valuation C NNReal}

def blkLat {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) where
  B := Matrix.of fun x y => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0
  det_ne := by
    have h : (Matrix.of fun x y : Fin n × Fin s => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0) =
        (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
      ext x y
      simp [Matrix.blockDiagonal_apply, eq_comm]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Ls τ).det_ne

/- English proof (translation)
Establish `h : (blkLat Ls).B = (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)`. Use extensionality with `x y`. Simplify using `[blkLat, Matrix.blockDiagonal_apply, eq_comm]`. Rewrite using `[h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]`.
-/
lemma blkLat_det {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) :
    (blkLat Ls).B.det = ∏ τ, (Ls τ).B.det := by
  have h : (blkLat Ls).B =
      (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext x y
    simp [blkLat, Matrix.blockDiagonal_apply, eq_comm]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]

/- English proof (translation)
Establish `hmv : ∀ c : Fin n × Fin s → C, (blkLat Ls).B *ᵥ c = fun y => ((Ls y.1).B *ᵥ fun j => c (y.1, j)) y.2`. Introduce `c`. Use extensionality with `⟨τ, i⟩`. Simplify using `only [blkLat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_eq_single τ]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Use extensionality with `w`.

Simplify using `only [ReciprocityTheory.PGsh.Lat.pts, sumPts, Set.mem_setOf_eq, hmv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩ τ`. Conclude with `⟨fun j => c (τ, j), fun j => hc (τ, j), rfl⟩`. Introduce `hw choose c hc hce using hw`.

Use `⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Conclude with `congrFun (hce y.1) y.2`.
-/
lemma blkLat_pts {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : (blkLat Ls).pts = sumPts Ls := by
  have hmv : ∀ c : Fin n × Fin s → C, (blkLat Ls).B *ᵥ c =
      fun y => ((Ls y.1).B *ᵥ fun j => c (y.1, j)) y.2 := by
    intro c
    ext ⟨τ, i⟩
    simp only [blkLat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul]
    rw [Finset.sum_eq_single τ]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  ext w
  simp only [ReciprocityTheory.PGsh.Lat.pts, sumPts, Set.mem_setOf_eq, hmv]
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    exact ⟨fun j => c (τ, j), fun j => hc (τ, j), rfl⟩
  · intro hw
    choose c hc hce using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext y
    exact congrFun (hce y.1) y.2

/- English proof (translation)
Simplify using `only [ReciprocityTheory.PGsh.colen, blkLat_det, map_prod]`. Rewrite using `[Finset.prod_div_distrib]`.
-/
lemma colen_blk {n s : ℕ} (L's Ls : Fin n → Lat v (Fin s)) :
    colen (blkLat L's) (blkLat Ls) = ∏ τ, colen (L's τ) (Ls τ) := by
  simp only [ReciprocityTheory.PGsh.colen, blkLat_det, map_prod]
  rw [Finset.prod_div_distrib]

/- English proof (translation)
Establish `hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι), v L.B.det ≠ 0` using `fun L => (map_ne_zero v).2 L.det_ne`. Use `set S : Lat v (Fin n × Fin s) := blkLat Mτ`. Use `set S' : Lat v (Fin n × Fin s) := blkLat M'τ`. Establish `h2` using `valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hMst hMτ (blkLat_pts Mτ)`. Establish `h3` using `colength_sq_mul_le a hinj hint s h A F M' S' M'τ hF hM' hM'τ (blkLat_pts M'τ)`.

Establish `hP : colen S' S = ∏ τ, colen (M'τ τ) (Mτ τ)` using `colen_blk M'τ Mτ`. Establish `hid : colen M' M * colen M S = colen M' S' * colen S' S`. Simplify using `only [ReciprocityTheory.PGsh.colen]`. Rewrite using `[div_mul_div_cancel₀ (hdet M), div_mul_div_cancel₀ (hdet S')]`. Establish `hc : 0 < colen M S ^ 2`.

Establish `: colen M S ≠ 0` using `div_ne_zero (hdet M) (hdet S)`. Check the signs of the components of the expression. Rewrite using `[← hP]`. Use `le_of_mul_le_mul_right ?_ hc` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2 = (colen M' M * colen M S) ^ 2 * v (discr a) ^ h by ring, hid]; ring`. Use `_ ≤ v (discr a) ^ (2 * s) * colen S' S ^ 2 := by gcongr`. Use `_ = colen S' S ^ 2 * v (discr a) ^ s * v (discr a) ^ s := by ring`. Use `_ ≤ colen S' S ^ 2 * v (discr a) ^ s * colen M S ^ 2 := by gcongr`.
-/
theorem colength_sq_mul_le_prod (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) :
    colen M' M ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s := by
  have hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι), v L.B.det ≠ 0 :=
    fun L => (map_ne_zero v).2 L.det_ne
  set S : Lat v (Fin n × Fin s) := blkLat Mτ
  set S' : Lat v (Fin n × Fin s) := blkLat M'τ
  have h2 := valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hMst hMτ (blkLat_pts Mτ)
  have h3 := colength_sq_mul_le a hinj hint s h A F M' S' M'τ hF hM' hM'τ (blkLat_pts M'τ)
  have hP : colen S' S = ∏ τ, colen (M'τ τ) (Mτ τ) := colen_blk M'τ Mτ
  have hid : colen M' M * colen M S = colen M' S' * colen S' S := by
    simp only [ReciprocityTheory.PGsh.colen]
    rw [div_mul_div_cancel₀ (hdet M), div_mul_div_cancel₀ (hdet S')]
  have hc : 0 < colen M S ^ 2 := by
    have : colen M S ≠ 0 := div_ne_zero (hdet M) (hdet S)
    positivity
  rw [← hP]
  refine le_of_mul_le_mul_right ?_ hc
  calc colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2
      = colen M' S' ^ 2 * v (discr a) ^ h * colen S' S ^ 2 := by
        rw [show colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2 =
          (colen M' M * colen M S) ^ 2 * v (discr a) ^ h by ring, hid]; ring
    _ ≤ v (discr a) ^ (2 * s) * colen S' S ^ 2 := by gcongr
    _ = colen S' S ^ 2 * v (discr a) ^ s * v (discr a) ^ s := by ring
    _ ≤ colen S' S ^ 2 * v (discr a) ^ s * colen M S ^ 2 := by gcongr

end ReciprocityTheory.PGsh.Up
