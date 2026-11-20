import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Lemmata.MovedPointExistence.ExistsMoved

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.InhabA

open ReciprocityTheory.ChartRestriction.DS

section DetDeriv

open NormedSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Simplify using `only [zero_smul, exp_zero, one_mul] at h`. Set `L : Matrix ι ι ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)`. Conclude with `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`.
-/
theorem hasDerivAt_exp_entry (X : Matrix ι ι ℂ) (i j : ι) :
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at h
  let L : Matrix ι ι ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.MovedPointExistence.goal1 .. | (apply Bl.MovedPointExistence.goal1 <;> assumption) | (intros; apply Bl.MovedPointExistence.goal1 <;> assumption)`.
-/
theorem hasDerivAt_det_of_one (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.MovedPointExistence.goal1 .. | (apply Bl.MovedPointExistence.goal1 <;> assumption) | (intros; apply Bl.MovedPointExistence.goal1 <;> assumption)

end DetDeriv

variable {m : ℕ}

/- English proof (translation)
Establish `h` using `congrFun (congrFun hg i) j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j`. Conclude with `absurd (hi.trans hj.symm) hij`. Simplify using `only [hi, hj, Bool.false_eq_true, if_false, if_true] at h`.

Take the linear combination `h / 2`. Simplify using `only [hi, hj, Bool.false_eq_true, if_false, if_true] at h`. Take the linear combination `-h / 2`. Conclude with `absurd (hi.trans hj.symm) hij`.
-/
theorem eq_zero_of_comm {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g * Jm ε = Jm ε * g)
    (i j : Fin m) (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg i) j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j
  · exact absurd (hi.trans hj.symm) hij
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination h / 2
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination -h / 2
  · exact absurd (hi.trans hj.symm) hij

/- English proof (translation)
Use extensionality with `x y`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[← Finset.sum_filter_of_ne (p := fun l => ε l = s)]`. Conclude with `Finset.sum_subtype _ (fun l => by simp) (fun l => g x.1 l * h l y.1)`. Introduce `l _ hl`.

Assume the negation of the conclusion as `hne`. Conclude with `hl (by rw [hg x.1 l (by rw [x.2]; exact Ne.symm hne), zero_mul])`.
-/
theorem submatrix_mul_blk {ε : Fin m → Bool} (s : Bool) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : ∀ i j, ε i ≠ ε j → g i j = 0) (h : Matrix (Fin m) (Fin m) ℂ) :
    (g * h).submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) =
      g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) *
        h.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := fun l => ε l = s)]
  · exact Finset.sum_subtype _ (fun l => by simp) (fun l => g x.1 l * h l y.1)
  · intro l _ hl
    by_contra hne
    exact hl (by rw [hg x.1 l (by rw [x.2]; exact Ne.symm hne), zero_mul])

/- English proof (translation)
Establish `hb` using `eq_zero_of_comm hk.2`. Establish `hbs : ∀ i j, ε i ≠ ε j → kᴴ i j = 0` using `fun i j hij => by`. Rewrite using `[Matrix.conjTranspose_apply, hb j i (Ne.symm hij), star_zero]`. Establish `hu : kᴴ * k = 1`. Use `(Matrix.mem_unitaryGroup_iff').1 hk.1` as an intermediate fact.

Simplify `this` using `[Matrix.star_eq_conjTranspose]`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_mul, Matrix.conjTranspose_submatrix, ← submatrix_mul_blk s hbs k, hu, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]`.
-/
theorem star_det_mul_det {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    star (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det *
      (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det = 1 := by
  have hb := eq_zero_of_comm hk.2
  have hbs : ∀ i j, ε i ≠ ε j → kᴴ i j = 0 := fun i j hij => by
    rw [Matrix.conjTranspose_apply, hb j i (Ne.symm hij), star_zero]
  have hu : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, Matrix.conjTranspose_submatrix,
    ← submatrix_mul_blk s hbs k, hu, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

/- English proof (translation)
Introduce `h`. Use `star_det_mul_det s hk` as an intermediate fact. Rewrite `this` using `[h, mul_zero]`. Conclude with `zero_ne_one this`.
-/
theorem det_ne_zero {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det ≠ 0 := by
  intro h
  have := star_det_mul_det s hk
  rw [h, mul_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Apply the tactic sequence `have h := hasDerivAt_det_of_one (fun t : ℝ => (NormedSpace.exp (t • X)).submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)) (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)) (by simp [NormedSpace.exp_zero, Matrix.submatrix_one _ …`. Establish `ht : (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).trace = ∑ a ∈ univ.filter (fun a => ε a = s), X a a`. Rewrite using `[Matrix.trace]`. Conclude with `(Finset.sum_subtype _ (fun l => by simp) (fun l => X l l)).symm`. Rewrite `h` using `[ht]`.

Simplify `h` using `only [Complex.coe_smul]`.
-/
theorem hasDerivAt_blockDet (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) :
    HasDerivAt (fun t : ℝ => ((NormedSpace.exp ((t : ℂ) • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det)
      (∑ a ∈ univ.filter (fun a => ε a = s), X a a) 0 := by
  have h := hasDerivAt_det_of_one
    (fun t : ℝ => (NormedSpace.exp (t • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (by simp [NormedSpace.exp_zero, Matrix.submatrix_one _ Subtype.val_injective])
    (fun i j => hasDerivAt_exp_entry X i.1 j.1)
  have ht : (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).trace =
      ∑ a ∈ univ.filter (fun a => ε a = s), X a a := by
    rw [Matrix.trace]
    exact (Finset.sum_subtype _ (fun l => by simp) (fun l => X l l)).symm
  rw [ht] at h
  simpa only [Complex.coe_smul] using h

end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
