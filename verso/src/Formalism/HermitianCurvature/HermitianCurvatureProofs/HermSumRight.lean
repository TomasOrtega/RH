import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolW

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def Flt (a : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), a ≤ i.val → x i = 0

def hermL (y : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun x := herm (Hpk k r) x y
  map_add' x x' := herm_add_left x x' y
  map_smul' c x := by simp [herm_smul_left]

/- English proof (translation)
The claim follows from `map_sum (hermL y) f s`.
-/
theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ j ∈ s, f j) y = ∑ j ∈ s, herm (Hpk k r) (f j) y :=
  map_sum (hermL y) f s

/- English proof (translation)
Rewrite using `[herm_swap, herm_sum_left, star_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => by rw [← herm_swap])`.
-/
theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (∑ j ∈ s, f j) = ∑ j ∈ s, herm (Hpk k r) x (f j) := by
  rw [herm_swap, herm_sum_left, star_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← herm_swap])

/- English proof (translation)
The claim follows from `map_sum (Matrix.mulVecLin g) f s`.
-/
theorem mulVec_sum' {ι : Type*} (s : Finset ι) (g : B.Mat k r) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    g *ᵥ (∑ j ∈ s, f j) = ∑ j ∈ s, g *ᵥ f j :=
  map_sum (Matrix.mulVecLin g) f s

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hi : i.val < a`. Rewrite using `[Finset.sum_eq_single ⟨i.val, hi⟩]`. Establish `: eI k r ⟨i.val, by omega⟩ = i` using `Fin.ext rfl`.

Simplify using `[this, bvec]`. Introduce `j _ hj`. Establish `: eI k r ⟨j.val, by omega⟩ ≠ i`. Introduce `e`. Apply `hj` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg Fin.val e` as an intermediate fact. Simplify `this` using `[eI]`. Simplify using `[bvec, Ne.symm this]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hy i (by omega)]`. Use `symm`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Establish `: eI k r ⟨j.val, by omega⟩ ≠ i`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[eI] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, Ne.symm this]`.
-/
theorem flt_decomp (a : ℕ) (ha : a ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y) :
    y = ∑ j : Fin a, y (eI k r ⟨j.val, by omega⟩) • bvec (eI k r ⟨j.val, by omega⟩) := by
  funext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < a
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
      simp [this, bvec]
    · intro j _ hj
      have : eI k r ⟨j.val, by omega⟩ ≠ i := by
        intro e; apply hj; apply Fin.ext; have := congrArg Fin.val e; simpa [eI] using this
      simp [bvec, Ne.symm this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hy i (by omega)]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : eI k r ⟨j.val, by omega⟩ ≠ i := by
      intro e; have := congrArg Fin.val e; simp [eI] at this; omega
    simp [bvec, Ne.symm this]

def Mblk (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  herm (Hpk k r) (g *ᵥ bvec (eI k r ⟨j.val, by omega⟩)) (bvec (eI k r ⟨i.val, by omega⟩))

/- English proof (translation)
Unfold `Dmin`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Mblk]`. Establish `hi : (i : ℕ) < a` using `i.isLt`.

Establish `hj : (j : ℕ) < a` using `j.isLt`. Rewrite using `[dif_pos (show i.val < r by omega), dif_pos (show j.val < r by omega)]`.
-/
theorem dmin_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) :
    Dmin k r z z' g ⟨a, by omega⟩ = (Mblk g a ha).det := by
  unfold Dmin
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Mblk]
  have hi : (i : ℕ) < a := i.isLt
  have hj : (j : ℕ) < a := j.isLt
  rw [dif_pos (show i.val < r by omega), dif_pos (show j.val < r by omega)]

/- English proof (translation)
Rewrite `hD` using `[dmin_eq z z' g a ha]`. Use `set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)`. Establish `hMy : Mblk g a ha *ᵥ y' = 0`. Use function extensionality and compare the values at `c`. Establish `hc` using `h ⟨c.val, by omega⟩ c.isLt`.

Rewrite `hc` using `[flt_decomp a ha y hy, mulVec_sum', herm_sum_left]`. Simplify using `only [mulVec_smul, herm_smul_left] at hc`. Rewrite using `[Pi.zero_apply, ← hc]`. Simplify using `only [mulVec, dotProduct, Mblk, y']`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`.

Establish `hy' : y' = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hD hMy`. Rewrite using `[flt_decomp a ha y hy]`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Establish `: y (eI k r ⟨j.val, by omega⟩) = 0` using `congrFun hy' j`. Rewrite using `[this, zero_smul]`.
-/
theorem dlem_i (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) (g *ᵥ y) (bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : Mblk g a ha *ᵥ y' = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [flt_decomp a ha y hy, mulVec_sum', herm_sum_left] at hc
    simp only [mulVec_smul, herm_smul_left] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [mulVec, dotProduct, Mblk, y']
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hy' : y' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := congrFun hy' j
  rw [this, zero_smul]

/- English proof (translation)
Rewrite `hD` using `[dmin_eq z z' g a ha]`. Use `set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)`. Establish `hMy : star y' ᵥ* Mblk g a ha = 0`. Use function extensionality and compare the values at `c`. Establish `hc` using `h ⟨c.val, by omega⟩ c.isLt`.

Rewrite `hc` using `[herm_swap, star_eq_zero, flt_decomp a ha y hy, herm_sum_right]`. Simplify using `only [herm_smul_right] at hc`. Rewrite using `[Pi.zero_apply, ← hc]`. Simplify using `only [vecMul, dotProduct, Mblk, y', Pi.star_apply]`. Establish `hy' : star y' = 0` using `Matrix.eq_zero_of_vecMul_eq_zero hD hMy`.

Rewrite using `[flt_decomp a ha y hy]`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Establish `: y (eI k r ⟨j.val, by omega⟩) = 0`. Use `congrFun hy' j` as an intermediate fact. Simplify `this` using `[y']`.

Rewrite using `[this, zero_smul]`.
-/
theorem dlem_ii (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) y (g *ᵥ bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : star y' ᵥ* Mblk g a ha = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [herm_swap, star_eq_zero, flt_decomp a ha y hy, herm_sum_right] at hc
    simp only [herm_smul_right] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [vecMul, dotProduct, Mblk, y', Pi.star_apply]
  have hy' : star y' = 0 := Matrix.eq_zero_of_vecMul_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := by
    have := congrFun hy' j
    simpa [y'] using this
  rw [this, zero_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
