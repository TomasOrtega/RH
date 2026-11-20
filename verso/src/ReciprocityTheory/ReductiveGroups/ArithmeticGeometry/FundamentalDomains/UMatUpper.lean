import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper

namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

def blk (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Matrix (Fin c) (Fin c) ℂ :=
  G.submatrix (Fin.castLE c.isLt.le) (Fin.castLE c.isLt.le)

def rowc (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Fin c → ℂ := fun m => G c (Fin.castLE c.isLt.le m)

def uMat (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j c => if j = c then 1 else
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ else 0

/- English proof (translation)
Simplify using `[uMat]`.
-/
lemma uMat_diag (G : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : uMat G j j = 1 := by
  simp [uMat]

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [id] at hij`. Simplify using `only [uMat, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_gt hij), dif_neg (not_lt.2 hij.le)]`.
-/
lemma uMat_upper (G : Matrix (Fin n) (Fin n) ℂ) : (uMat G).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  simp only [uMat, Matrix.of_apply]
  rw [if_neg (ne_of_gt hij), dif_neg (not_lt.2 hij.le)]

/- English proof (translation)
Simplify using `only [uMat, Matrix.of_apply]`. Distinguish the cases in `h1 : j = c`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : j < c`.

Simplify using `[h1, h2]`. Simplify using `[h1, h2]`.
-/
lemma uMat_term (G : Matrix (Fin n) (Fin n) ℂ) (c m j : Fin n) :
    uMat G j c * G j m = (if j = c then G c m else 0) +
      (if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0) := by
  simp only [uMat, Matrix.of_apply]
  by_cases h1 : j = c
  · subst h1
    simp
  · by_cases h2 : j < c
    · simp [h1, h2]
    · simp [h1, h2]

/- English proof (translation)
Establish `hinv : IsUnit (blk G c).det` using `isUnit_iff_ne_zero.2 hdet`. Establish `key : ∀ m' : Fin c, ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * blk G c j' m' = rowc G c m'`. Introduce `m'`. Establish `h` using `congrFun (Matrix.vecMul_vecMul (rowc G c) (blk G c)⁻¹ (blk G c)) m'`. Rewrite `h` using `[Matrix.nonsing_inv_mul _ hinv, Matrix.vecMul_one]`.

Rewrite using `[← h]`. Both sides reduce to the same expression. Set `g : Fin n → ℂ` to `fun j => if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0`. Establish `hmain : ((uMat G)ᵀ * G) c m = G c m + ∑ j : Fin n, g j`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.transpose_apply, uMat_term, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Establish `hA : ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') = -∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations.

Establish `h : Fin.castLE c.isLt.le j' < c` using `j'.isLt`. Simplify using `only [g, dif_pos h]`. Conclude with `neg_mul _ _`. Establish `hB : ∑ j : Fin n, g j = ∑ j' : Fin c, g (Fin.castLE c.isLt.le j')`. Rewrite using `[show (∑ j' : Fin c, g (Fin.castLE c.isLt.le j')) = ∑ x ∈ Finset.univ.map (Fin.castLEEmb c.isLt.le), g x from (Finset.sum_map Finset.univ (Fin.castLEEmb c.isLt.le) g).symm]`.

Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `j _ hj`. Establish `hjc : ¬ j < c`. Introduce `hlt`.

Conclude with `hj (Finset.mem_map.2 ⟨⟨j, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)`. Simplify using `only [g, dif_neg hjc]`. Establish `k2 : ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m = G c m` using `key ⟨m, hm⟩`. Rewrite using `[hmain, hB, hA, k2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma uT_G_zero (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (hdet : (blk G c).det ≠ 0) (m : Fin n)
    (hm : m < c) : ((uMat G)ᵀ * G) c m = 0 := by
  have hinv : IsUnit (blk G c).det := isUnit_iff_ne_zero.2 hdet
  have key : ∀ m' : Fin c, ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * blk G c j' m' =
      rowc G c m' := by
    intro m'
    have h := congrFun (Matrix.vecMul_vecMul (rowc G c) (blk G c)⁻¹ (blk G c)) m'
    rw [Matrix.nonsing_inv_mul _ hinv, Matrix.vecMul_one] at h
    rw [← h]
    rfl
  let g : Fin n → ℂ := fun j =>
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0
  have hmain : ((uMat G)ᵀ * G) c m = G c m + ∑ j : Fin n, g j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, uMat_term, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have hA : ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') =
      -∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h : Fin.castLE c.isLt.le j' < c := j'.isLt
    simp only [g, dif_pos h]
    exact neg_mul _ _
  have hB : ∑ j : Fin n, g j = ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') := by
    rw [show (∑ j' : Fin c, g (Fin.castLE c.isLt.le j')) =
        ∑ x ∈ Finset.univ.map (Fin.castLEEmb c.isLt.le), g x from
      (Finset.sum_map Finset.univ (Fin.castLEEmb c.isLt.le) g).symm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjc : ¬ j < c := by
      intro hlt
      exact hj (Finset.mem_map.2 ⟨⟨j, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp only [g, dif_neg hjc]
  have k2 : ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m =
      G c m := key ⟨m, hm⟩
  rw [hmain, hB, hA, k2]
  ring

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
