import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)` and prove the remaining obligations. Introduce `k hk`.

Establish `hk' : i ≤ (k : ℕ)`. Assume the negation of the conclusion as `h`. Conclude with `hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩`. Establish `ha` using `a.2`. Rewrite using `[hc _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]`.
-/
private lemma sub_lower_mul {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (c * M).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      c.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have ha := a.2
  rw [hc _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)` and prove the remaining obligations. Introduce `k hk`.

Establish `hk' : i ≤ (k : ℕ)`. Assume the negation of the conclusion as `h`. Conclude with `hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩`. Establish `hb` using `b.2`. Unfold `IsUpperTri at hc'`.

Rewrite using `[hc' _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]`.
-/
private lemma sub_mul_upper {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c')
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (M * c').submatrix (Fin.castLE hi) (Fin.castLE hi) =
      M.submatrix (Fin.castLE hi) (Fin.castLE hi) * c'.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have hb := b.2
  unfold IsUpperTri at hc'
  rw [hc' _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : a < b` using `hab`. Apply `hc` to reduce the goal to its premises. Rewrite using `[Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]`. Conclude with `hab'`.
-/
private lemma lowerTri_sub {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) :
    (c.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsLowerTriangular := by
  intro a b hab
  have hab' : a < b := hab
  apply hc
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : b < a` using `hab`. Apply `hc'` to reduce the goal to its premises. Rewrite using `[Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]`. Conclude with `hab'`.
-/
private lemma upperTri_sub {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c') :
    (c'.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
  intro a b hab
  have hab' : b < a := hab
  apply hc'
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

/- English proof (translation)
Establish `hp : ∀ f : Fin n → ℂ, ∏ a : Fin i, f (Fin.castLE hi a) = ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), f l`. Introduce `f`. Rewrite using `[Finset.prod_filter]`. Use `Fintype.prod_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Rewrite using `[if_neg]`. Introduce `hlt`. Conclude with `hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩`. Introduce `a`. Rewrite using `[if_pos (by rw [Fin.coe_castLE]; exact a.2)]`.

Unfold `lead`. Rewrite using `[dif_pos hi, dif_pos hi, sub_mul_upper hi hc', sub_lower_mul hi hc, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_lowerTriangular _ (lowerTri_sub hi hc), Matrix.det_of_upperTriangular (upperTri_sub hi hc'), Finset.prod_mul_distrib, ← hp (fun l => c l l), ← hp (fun l => c' l l)]`. Simplify using `only [Matrix.submatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lead_tri_mul {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c') (i : ℕ) (hi : i ≤ n) :
    lead i (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), c l l * c' l l) * lead i z := by
  have hp : ∀ f : Fin n → ℂ, ∏ a : Fin i, f (Fin.castLE hi a) =
      ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), f l := by
    intro f
    rw [Finset.prod_filter]
    refine Fintype.prod_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ ?_
    · intro k hk
      rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · intro a
      rw [if_pos (by rw [Fin.coe_castLE]; exact a.2)]
  unfold lead
  rw [dif_pos hi, dif_pos hi, sub_mul_upper hi hc', sub_lower_mul hi hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular _ (lowerTri_sub hi hc), Matrix.det_of_upperTriangular (upperTri_sub hi hc'),
    Finset.prod_mul_distrib, ← hp (fun l => c l l), ← hp (fun l => c' l l)]
  simp only [Matrix.submatrix_apply]
  ring

/- English proof (translation)
Establish `hp` using `(hx.submatrix (Fin.castLE_injective hi)).det_pos`. Unfold `lead`. Rewrite using `[dif_pos hi]`. Take `⟨h1, h2⟩` from `Complex.pos_iff.mp hp`. Conclude with `⟨h1, h2.symm⟩`.
-/
theorem lead_posDef {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (i : ℕ) (hi : i ≤ n) :
    0 < (lead i x).re ∧ (lead i x).im = 0 := by
  have hp := (hx.submatrix (Fin.castLE_injective hi)).det_pos
  unfold lead
  rw [dif_pos hi]
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hp
  exact ⟨h1, h2.symm⟩

end ReciprocityTheory.ChartRestriction.DS.S7
