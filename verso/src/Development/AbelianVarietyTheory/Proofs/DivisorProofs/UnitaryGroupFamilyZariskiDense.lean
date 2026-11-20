import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
open Classical MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.UnitaryZariskiDense

/- English proof (translation)
The claim follows from `eval₂Hom_bind₁ _ _ _ _`.
-/
theorem eval_bind₁_subst {σ τ : Type} (y : τ → ℂ) (f : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ) :
    eval y (bind₁ f p) = eval (fun v => eval y (f v)) p :=
  eval₂Hom_bind₁ _ _ _ _

/- English proof (translation)
Use `MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ)) (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x = fun v => ((x v).re : ℂ)`. Use function extensionality and compare the values at `v`. Take `⟨r, hr⟩` from `hx v (Set.mem_univ _)`. Rewrite using `[← hr, Complex.ofReal_re]`.

Rewrite using `[hx', h, map_zero]`.
-/
theorem eq_zero_of_eval_real {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ u : σ → ℝ, eval (fun v => (u v : ℂ)) P = 0) : P = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_
  have hx' : x = fun v => ((x v).re : ℂ) := by
    funext v
    obtain ⟨r, hr⟩ := hx v (Set.mem_univ _)
    rw [← hr, Complex.ofReal_re]
  rw [hx', h, map_zero]

variable {ι : Type} {a : ℕ}

def tr (v : ι × Fin a × Fin a) : ι × Fin a × Fin a := (v.1, v.2.2, v.2.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tr_tr (v : ι × Fin a × Fin a) : tr (tr v) = v := rfl

def cα : ℂ := ⟨1 / 2, 1 / 2⟩

def cβ : ℂ := ⟨-1 / 2, 1 / 2⟩

def cγ : ℂ := ⟨1 / 2, -1 / 2⟩

def cδ : ℂ := ⟨-1 / 2, -1 / 2⟩

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [cα, cβ] <;> norm_num`.
-/
theorem conj_cα : (starRingEnd ℂ) cα = -cβ := by
  apply Complex.ext <;> simp [cα, cβ] <;> norm_num

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [cα, cβ] <;> norm_num`.
-/
theorem conj_cβ : (starRingEnd ℂ) cβ = -cα := by
  apply Complex.ext <;> simp [cα, cβ] <;> norm_num

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [cα, cβ, cγ, cδ] <;> norm_num`.
-/
theorem c_one : cα * cγ + cβ * cδ = 1 := by
  apply Complex.ext <;> simp [cα, cβ, cγ, cδ] <;> norm_num

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [cα, cβ, cγ, cδ] <;> norm_num`.
-/
theorem c_zero : cα * cδ + cβ * cγ = 0 := by
  apply Complex.ext <;> simp [cα, cβ, cγ, cδ] <;> norm_num

/- English proof (translation)
Establish `hev : ∀ y : ι × Fin a × Fin a → ℂ, eval y (bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R) = eval (fun v => cα * y v + cβ * y (tr v)) R`. Introduce `y`. Rewrite using `[eval_bind₁_subst]`. Use `congr 2`. Use function extensionality and compare the values at `v`.

Simplify using the standard rewrite rules. Establish `hS0 : bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R = 0`. Apply `eq_zero_of_eval_real` to reduce the goal to its premises. Introduce `u`. Rewrite using `[hev]`.

Apply `h` to reduce the goal to its premises. Introduce `v`. Simplify using `only [tr_tr, star_add, star_mul', Complex.star_def, Complex.conj_ofReal, conj_cα, conj_cβ]`. Expand and normalize the polynomial expressions, which then agree. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `x`. Use `hev (fun v => cγ * x v + cδ * x (tr v))` as an intermediate fact. Rewrite `this` using `[hS0, map_zero]`. Rewrite using `[map_zero, this]`. Use `congr 2`.

Use function extensionality and compare the values at `v`. Simplify using `only [tr_tr]`. Take the linear combination `(-(x v)) * c_one - x (tr v) * c_zero`.
-/
theorem eq_zero_of_eval_skew (R : MvPolynomial (ι × Fin a × Fin a) ℂ)
    (h : ∀ x : ι × Fin a × Fin a → ℂ, (∀ v, star (x (tr v)) = - x v) → eval x R = 0) : R = 0 := by
  have hev : ∀ y : ι × Fin a × Fin a → ℂ,
      eval y (bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R) =
        eval (fun v => cα * y v + cβ * y (tr v)) R := by
    intro y
    rw [eval_bind₁_subst]
    congr 2
    funext v
    simp
  have hS0 : bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R = 0 := by
    apply eq_zero_of_eval_real
    intro u
    rw [hev]
    apply h
    intro v
    simp only [tr_tr, star_add, star_mul', Complex.star_def, Complex.conj_ofReal, conj_cα, conj_cβ]
    ring
  apply MvPolynomial.funext
  intro x
  have := hev (fun v => cγ * x v + cδ * x (tr v))
  rw [hS0, map_zero] at this
  rw [map_zero, this]
  congr 2
  funext v
  simp only [tr_tr]
  linear_combination (-(x v)) * c_one - x (tr v) * c_zero

/- English proof (translation)
Introduce `h0`. Establish `hpd : (1 + Aᴴ * A).PosDef` using `Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)`. Establish `e : 1 + Aᴴ * A = (1 + A)ᴴ * (1 + A)`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA]`. Use `noncomm_ring`.

Use `hpd.det_pos.ne'` as an intermediate fact. Rewrite `this` using `[e, Matrix.det_mul, h0, mul_zero]`. Conclude with `this rfl`.
-/
theorem det_one_add_ne_zero {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : Aᴴ = -A) :
    (1 + A).det ≠ 0 := by
  intro h0
  have hpd : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have e : 1 + Aᴴ * A = (1 + A)ᴴ * (1 + A) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA]
    noncomm_ring
  have := hpd.det_pos.ne'
  rw [e, Matrix.det_mul, h0, mul_zero] at this
  exact this rfl

def cay {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) : Matrix n n ℂ := (1 - B) * (1 + B)⁻¹

/- English proof (translation)
Establish `h1 : IsUnit (1 + A).det` using `isUnit_iff_ne_zero.2 (det_one_add_ne_zero A hA)`. Establish `h2 : IsUnit (1 - A).det`. Use `det_one_add_ne_zero (-A) (by rw [Matrix.conjTranspose_neg, hA])` as an intermediate fact. Rewrite `this` using `[← sub_eq_add_neg]`. Conclude with `isUnit_iff_ne_zero.2 this`.

Rewrite using `[Matrix.mem_unitaryGroup_iff', cay, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hA, ← sub_eq_add_neg, sub_neg_eq_add]`. Establish `comm : (1 + A) * (1 - A) = (1 - A) * (1 + A)` using `by noncomm_ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cay_mem_unitary {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : Aᴴ = -A) :
    cay A ∈ Matrix.unitaryGroup n ℂ := by
  have h1 : IsUnit (1 + A).det := isUnit_iff_ne_zero.2 (det_one_add_ne_zero A hA)
  have h2 : IsUnit (1 - A).det := by
    have := det_one_add_ne_zero (-A) (by rw [Matrix.conjTranspose_neg, hA])
    rw [← sub_eq_add_neg] at this
    exact isUnit_iff_ne_zero.2 this
  rw [Matrix.mem_unitaryGroup_iff', cay, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hA, ← sub_eq_add_neg, sub_neg_eq_add]
  have comm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  calc (1 - A)⁻¹ * (1 + A) * ((1 - A) * (1 + A)⁻¹)
      = (1 - A)⁻¹ * ((1 + A) * (1 - A)) * (1 + A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = ((1 - A)⁻¹ * (1 - A)) * ((1 + A) * (1 + A)⁻¹) := by rw [comm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ h2, Matrix.mul_nonsing_inv _ h1, Matrix.one_mul]

/- English proof (translation)
Establish `hu : IsUnit (1 + B).det` using `isUnit_iff_ne_zero.2 hB`. Establish `e1 : 1 + cay B = (2 : ℂ) • (1 + B)⁻¹`. Establish `h3 : (1 + B + (1 - B)) = (2 : ℂ) • (1 : Matrix n n ℂ)` using `by rw [two_smul]; abel`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hu, cay]`.

Use `_ = (2 : ℂ) • (1 + B)⁻¹ := by rw [← Matrix.add_mul, h3, Matrix.smul_mul, Matrix.one_mul]`. Establish `e2 : 1 - cay B = (2 : ℂ) • (B * (1 + B)⁻¹)`. Establish `h3 : (1 + B - (1 - B)) = (2 : ℂ) • B` using `by rw [two_smul]; abel`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hu, cay]`.

Use `_ = (2 : ℂ) • (B * (1 + B)⁻¹) := by rw [← Matrix.sub_mul, h3, Matrix.smul_mul]`. Establish `hinv : ((2 : ℂ) • (1 + B)⁻¹)⁻¹ = (2 : ℂ)⁻¹ • (1 + B)`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hu]`. Evaluate the numerical expressions.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ two_ne_zero) (isUnit_iff_ne_zero.1 (Matrix.isUnit_nonsing_inv_det _ hu))`. Rewrite using `[cay, e1, e2, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`. Evaluate the numerical expressions.
-/
theorem cay_cay {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (hB : (1 + B).det ≠ 0) :
    (1 + cay B).det ≠ 0 ∧ cay (cay B) = B := by
  have hu : IsUnit (1 + B).det := isUnit_iff_ne_zero.2 hB
  have e1 : 1 + cay B = (2 : ℂ) • (1 + B)⁻¹ := by
    have h3 : (1 + B + (1 - B)) = (2 : ℂ) • (1 : Matrix n n ℂ) := by rw [two_smul]; abel
    calc 1 + cay B = (1 + B) * (1 + B)⁻¹ + (1 - B) * (1 + B)⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hu, cay]
      _ = (2 : ℂ) • (1 + B)⁻¹ := by rw [← Matrix.add_mul, h3, Matrix.smul_mul, Matrix.one_mul]
  have e2 : 1 - cay B = (2 : ℂ) • (B * (1 + B)⁻¹) := by
    have h3 : (1 + B - (1 - B)) = (2 : ℂ) • B := by rw [two_smul]; abel
    calc 1 - cay B = (1 + B) * (1 + B)⁻¹ - (1 - B) * (1 + B)⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hu, cay]
      _ = (2 : ℂ) • (B * (1 + B)⁻¹) := by rw [← Matrix.sub_mul, h3, Matrix.smul_mul]
  have hinv : ((2 : ℂ) • (1 + B)⁻¹)⁻¹ = (2 : ℂ)⁻¹ • (1 + B) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hu]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [e1, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (isUnit_iff_ne_zero.1 (Matrix.isUnit_nonsing_inv_det _ hu))
  · rw [cay, e1, e2, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    norm_num

def varMat (τ : ι) : Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  Matrix.of fun i j => X (τ, i, j)

def famOf (x : ι × Fin a × Fin a → ℂ) (τ : ι) : Matrix (Fin a) (Fin a) ℂ := Matrix.of fun i j => x (τ, i, j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[varMat, famOf]`.
-/
theorem mapMatrix_varMat (x : ι × Fin a × Fin a → ℂ) (τ : ι) :
    (eval x).mapMatrix (varMat (a := a) τ) = famOf x τ := by
  ext i j; simp [varMat, famOf]

/- English proof (translation)
Rewrite using `[RingHom.map_det, map_add, map_one, mapMatrix_varMat]`.
-/
theorem eval_det_one_add (x : ι × Fin a × Fin a → ℂ) (τ : ι) :
    eval x (1 + varMat (a := a) τ).det = (1 + famOf x τ).det := by
  rw [RingHom.map_det, map_add, map_one, mapMatrix_varMat]

/- English proof (translation)
Establish `e : ∀ M : Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ), eval x (M i j) = ((eval x).mapMatrix M) i j` using `fun _ => rfl`. Rewrite using `[e, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one, mapMatrix_varMat]`.
-/
theorem eval_cay_entry (x : ι × Fin a × Fin a → ℂ) (τ : ι) (i j : Fin a) :
    eval x (((1 - varMat (a := a) τ) * (1 + varMat τ).adjugate :
      Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ)) i j) =
      ((1 - famOf x τ) * (1 + famOf x τ).adjugate) i j := by
  have e : ∀ M : Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ),
      eval x (M i j) = ((eval x).mapMatrix M) i j := fun _ => rfl
  rw [e, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one, mapMatrix_varMat]

variable [Fintype ι]

def denom : MvPolynomial (ι × Fin a × Fin a) ℂ := ∏ τ, (1 + varMat τ).det

def numer (v : ι × Fin a × Fin a) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ((1 - varMat (a := a) v.1) * (1 + varMat v.1).adjugate :
      Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ)) v.2.1 v.2.2 *
    ∏ τ ∈ Finset.univ.erase v.1, (1 + varMat τ).det

def clearQ (Q : MvPolynomial (ι × Fin a × Fin a) ℂ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∑ d ∈ Q.support, C (coeff d Q) * (∏ v ∈ d.support, numer v ^ d v) *
    denom ^ (Q.totalDegree - d.sum fun _ e => e)

/- English proof (translation)
Simplify using `only [denom, map_prod, eval_det_one_add]`.
-/
theorem eval_denom (x : ι × Fin a × Fin a → ℂ) :
    eval x (denom (ι := ι) (a := a)) = ∏ τ, (1 + famOf x τ).det := by
  simp only [denom, map_prod, eval_det_one_add]

/- English proof (translation)
Simplify using `only [numer, map_mul, map_prod, eval_det_one_add, eval_cay_entry]`.
-/
theorem eval_numer (x : ι × Fin a × Fin a → ℂ) (v : ι × Fin a × Fin a) :
    eval x (numer v) = ((1 - famOf x v.1) * (1 + famOf x v.1).adjugate) v.2.1 v.2.2 *
      ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det := by
  simp only [numer, map_mul, map_prod, eval_det_one_add, eval_cay_entry]

/- English proof (translation)
Rewrite using `[eval_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hle` using `le_totalDegree hd`. Establish `hs : (d.sum fun _ e => e) = ∑ v ∈ d.support, d v` using `rfl`. Establish `hN : D ^ Q.totalDegree = D ^ (Q.totalDegree - d.sum fun _ e => e) * D ^ (∑ v ∈ d.support, d v)`.

Rewrite using `[← hs, ← pow_add, Nat.sub_add_cancel hle]`. Simplify using `only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[hN]`. Establish `key : ∀ c P F E : ℂ, E ≠ 0 → c * (P / E) * (F * E) = c * P * F`. Introduce `c P F E hE`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `key _ _ _ _ (pow_ne_zero _ hD)`.
-/
theorem eval_div_mul_pow_totalDegree_clear_denominators {σ : Type} (Q : MvPolynomial σ ℂ) (p : σ → ℂ) (D : ℂ) (hD : D ≠ 0) :
    eval (fun v => p v / D) Q * D ^ Q.totalDegree =
      ∑ d ∈ Q.support, coeff d Q * (∏ v ∈ d.support, p v ^ d v) *
        D ^ (Q.totalDegree - d.sum fun _ e => e) := by
  rw [eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hle := le_totalDegree hd
  have hs : (d.sum fun _ e => e) = ∑ v ∈ d.support, d v := rfl
  have hN : D ^ Q.totalDegree = D ^ (Q.totalDegree - d.sum fun _ e => e) * D ^ (∑ v ∈ d.support, d v) := by
    rw [← hs, ← pow_add, Nat.sub_add_cancel hle]
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hN]
  have key : ∀ c P F E : ℂ, E ≠ 0 → c * (P / E) * (F * E) = c * P * F := by
    intro c P F E hE
    calc c * (P / E) * (F * E) = c * P * F * (E / E) := by ring
      _ = c * P * F := by rw [div_self hE, mul_one]
  exact key _ _ _ _ (pow_ne_zero _ hD)

/- English proof (translation)
Establish `hD : eval x (denom (ι` using `ι) (a := a)) ≠ 0 := by`. Rewrite using `[eval_denom]`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ`. Establish `hfun : (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) = fun v => eval x (numer v) / eval x denom`. Use function extensionality and compare the values at `v`.

Rewrite using `[eval_numer, eval_denom, ← Finset.mul_prod_erase Finset.univ (fun τ => (1 + famOf x τ).det) (Finset.mem_univ v.1)]`. Establish `hE : ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ`. Rewrite using `[cay, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]`. Clear denominators, using `[hdet v.1, hE]` for the nonvanishing conditions. Rewrite using `[hfun, eval_div_mul_pow_totalDegree_clear_denominators Q _ _ hD]`.

Simplify using `only [clearQ, map_sum, map_mul, map_prod, map_pow, eval_C]`.
-/
theorem eval_clearQ (Q : MvPolynomial (ι × Fin a × Fin a) ℂ) (x : ι × Fin a × Fin a → ℂ)
    (hdet : ∀ τ, (1 + famOf x τ).det ≠ 0) :
    eval x (clearQ Q) = eval (fun v => cay (famOf x v.1) v.2.1 v.2.2) Q * (eval x denom) ^ Q.totalDegree := by
  have hD : eval x (denom (ι := ι) (a := a)) ≠ 0 := by
    rw [eval_denom]; exact Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
  have hfun : (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) =
      fun v => eval x (numer v) / eval x denom := by
    funext v
    rw [eval_numer, eval_denom,
      ← Finset.mul_prod_erase Finset.univ (fun τ => (1 + famOf x τ).det) (Finset.mem_univ v.1)]
    have hE : ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
    rw [cay, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    field_simp [hdet v.1, hE]
  rw [hfun, eval_div_mul_pow_totalDegree_clear_denominators Q _ _ hD]
  simp only [clearQ, map_sum, map_mul, map_prod, map_pow, eval_C]

/- English proof (translation)
Introduce `ι _ a Q hQ`. Establish `hR : clearQ Q = 0`. Apply `eq_zero_of_eval_skew` to reduce the goal to its premises. Introduce `x hx`. Establish `hAs : ∀ τ, (famOf x τ)ᴴ = -famOf x τ`.

Introduce `τ`. Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.neg_apply]`. Conclude with `hx (τ, i, j)`. Establish `hdet : ∀ τ, (1 + famOf x τ).det ≠ 0` using `fun τ => det_one_add_ne_zero _ (hAs τ)`.

Establish `h0` using `hQ (fun τ => ⟨cay (famOf x τ), cay_mem_unitary _ (hAs τ)⟩)`. Establish `h0' : eval (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) Q = 0` using `h0`. Rewrite using `[eval_clearQ Q x hdet, h0', zero_mul]`. Establish `hQg : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (1 + g τ).det ≠ 0) → eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) Q = 0`. Introduce `g hg`.

Establish `hA : ∀ τ, famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ = cay (g τ)` using `fun τ => Matrix.ext fun i j => rfl`. Establish `hdet : ∀ τ, (1 + famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ).det ≠ 0`. Introduce `τ`. Rewrite using `[hA]`. Conclude with `(cay_cay _ (hg τ)).1`.

Establish `h1` using `eval_clearQ Q _ hdet`. Establish `hfun : (fun v : ι × Fin a × Fin a => cay (famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) v.1) v.2.1 v.2.2) = fun v => g v.1 v.2.1 v.2.2`. Use function extensionality and compare the values at `v`. Rewrite using `[hA, (cay_cay _ (hg v.1)).2]`. Rewrite `h1` using `[hR, map_zero, hfun]`.

Establish `hD : eval (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) (denom (ι` using `ι) (a := a)) ≠ 0 := by`. Rewrite using `[eval_denom]`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_right (pow_ne_zero _ hD)`. Establish `hprod : Q * denom = 0`.

Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_mul, map_zero, eval_denom]`. Distinguish the cases in `h : ∀ τ, (1 + famOf x τ).det ≠ 0`. Establish `: eval x Q = 0` using `hQg (famOf x) h`.

Rewrite using `[this, zero_mul]`. Use `push_neg at h`. Take `⟨τ, hτ⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]`. Establish `hden : (denom (ι` using `ι) (a := a)) ≠ 0 := by`.

Introduce `h`. Use `eval_denom (ι := ι) (a := a) (fun _ => 0)` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Establish `h1 : ∀ τ, famOf (ι` using `ι) (a := a) (fun _ => 0) τ = 0 := fun τ => Matrix.ext fun i j => rfl`. Simplify using `only [h1, add_zero, Matrix.det_one, Finset.prod_const_one] at this`.

Conclude with `zero_ne_one this`. Conclude with `(mul_eq_zero.1 hprod).resolve_right hden`.
-/
theorem unitary_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ),
    (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
      MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) →
    Q = 0 := by
  intro ι _ a Q hQ
  have hR : clearQ Q = 0 := by
    apply eq_zero_of_eval_skew
    intro x hx
    have hAs : ∀ τ, (famOf x τ)ᴴ = -famOf x τ := by
      intro τ; ext i j
      rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
      exact hx (τ, i, j)
    have hdet : ∀ τ, (1 + famOf x τ).det ≠ 0 := fun τ => det_one_add_ne_zero _ (hAs τ)
    have h0 := hQ (fun τ => ⟨cay (famOf x τ), cay_mem_unitary _ (hAs τ)⟩)
    have h0' : eval (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) Q = 0 := h0
    rw [eval_clearQ Q x hdet, h0', zero_mul]
  have hQg : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (1 + g τ).det ≠ 0) →
      eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) Q = 0 := by
    intro g hg
    have hA : ∀ τ, famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ = cay (g τ) :=
      fun τ => Matrix.ext fun i j => rfl
    have hdet : ∀ τ, (1 + famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ).det ≠ 0 := by
      intro τ; rw [hA]; exact (cay_cay _ (hg τ)).1
    have h1 := eval_clearQ Q _ hdet
    have hfun : (fun v : ι × Fin a × Fin a =>
        cay (famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) v.1) v.2.1 v.2.2) =
        fun v => g v.1 v.2.1 v.2.2 := by
      funext v; rw [hA, (cay_cay _ (hg v.1)).2]
    rw [hR, map_zero, hfun] at h1
    have hD : eval (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) (denom (ι := ι) (a := a)) ≠ 0 := by
      rw [eval_denom]; exact Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
    exact (mul_eq_zero.1 h1.symm).resolve_right (pow_ne_zero _ hD)
  have hprod : Q * denom = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_denom]
    by_cases h : ∀ τ, (1 + famOf x τ).det ≠ 0
    · have : eval x Q = 0 := hQg (famOf x) h
      rw [this, zero_mul]
    · push_neg at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  have hden : (denom (ι := ι) (a := a)) ≠ 0 := by
    intro h
    have := eval_denom (ι := ι) (a := a) (fun _ => 0)
    rw [h, map_zero] at this
    have h1 : ∀ τ, famOf (ι := ι) (a := a) (fun _ => 0) τ = 0 := fun τ => Matrix.ext fun i j => rfl
    simp only [h1, add_zero, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  exact (mul_eq_zero.1 hprod).resolve_right hden

end GlobalTheory.UnitaryZariskiDense
