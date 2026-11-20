import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix MeasureTheory
open scoped ComplexOrder

/- English proof (translation)
Establish `hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i)`. Introduce `i`. Establish `h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det`. Rewrite using `[← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[h1, Matrix.det_apply']`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]`. Use `congr 1`.

Apply the tactic sequence `all_goals first`. Consider the case `(refine Finset.prod_congr rfl fun j hj => ?_`. Simplify using `[Matrix.updateCol_apply, Finset.ne_of_mem_erase hj])`. Consider the case `simp [Matrix.updateCol_apply]`. Simplify using `only [Matrix.trace, Matrix.diag, hcol]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
theorem trace_adjugate_mul_eq_sum_perm {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by
  have hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i) := by
    intro i
    have h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl fun j hj => ?_
         simp [Matrix.updateCol_apply, Finset.ne_of_mem_erase hj])
      | simp [Matrix.updateCol_apply]
  simp only [Matrix.trace, Matrix.diag, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

/- English proof (translation)
Rewrite using `[trace_adjugate_mul_eq_sum_perm]`. Establish `hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j`. Use function extensionality and compare the values at `s`. Conclude with `Matrix.det_apply' _`. Rewrite using `[hfun]`.

Establish `hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))), HasDerivAt (fun s => (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j) ((Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t` using `fun σ _ => by first`. Consider the case `exact (HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _`. Consider the case `(have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)`. Simplify using `only [Finset.prod_apply] at hp`. Conclude with `hp.const_mul _)`.

Consider the case `(have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)`. Use `hp.const_mul (Equiv.Perm.sign σ : ℂ) using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s`. Simplify using `[Finset.prod_apply])`. Use `first`.

Consider the case `exact HasDerivAt.fun_sum hσ`. Consider the case `exact HasDerivAt.sum hσ`. Consider the case `simpa using HasDerivAt.sum hσ`.
-/
theorem hasDerivAt_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ) (G' : Matrix (Fin r) (Fin r) ℂ)
    (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by
  rw [trace_adjugate_mul_eq_sum_perm]
  have hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j := by
    funext s; exact Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      HasDerivAt (fun s => (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j)
        ((Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t :=
    fun σ _ => by
      first
        | exact (HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           simp only [Finset.prod_apply] at hp
           exact hp.const_mul _)
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           convert hp.const_mul (Equiv.Perm.sign σ : ℂ) using 2
           funext s
           simp [Finset.prod_apply])
  first
    | exact HasDerivAt.fun_sum hσ
    | exact HasDerivAt.sum hσ
    | simpa using HasDerivAt.sum hσ

/- English proof (translation)
Establish `hd` using `hasDerivAt_det G G' t hG`. Establish `hre : HasDerivAt (fun s => (G s).det.re) ((G t).adjugate * G').trace.re t`. Use `Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `hdpos : 0 < (G t).det` using `hpos.det_pos`.

Establish `hre0 : 0 < (G t).det.re ∧ (G t).det.im = 0`. Use `Complex.lt_def.1 hdpos` as an intermediate fact. Simplify using `only [Complex.zero_re, Complex.zero_im] at this`. Conclude with `⟨this.1, this.2.symm⟩`. Establish `hlog` using `hre.log hre0.1.ne'`.

Use `hlog using 1` and compare the differences between its conclusion and the goal. Establish `hdet : (G t).det = (((G t).det.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [hre0.2])`. Rewrite using `[Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet, ← Complex.ofReal_inv, Complex.re_ofReal_mul]`. Simplify using `only [Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_log_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (G s).det.re) ((G t)⁻¹ * G').trace.re t := by
  have hd := hasDerivAt_det G G' t hG
  have hre : HasDerivAt (fun s => (G s).det.re) ((G t).adjugate * G').trace.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa [Function.comp_def] using this
  have hdpos : 0 < (G t).det := hpos.det_pos
  have hre0 : 0 < (G t).det.re ∧ (G t).det.im = 0 := by
    have := Complex.lt_def.1 hdpos
    simp only [Complex.zero_re, Complex.zero_im] at this
    exact ⟨this.1, this.2.symm⟩
  have hlog := hre.log hre0.1.ne'
  convert hlog using 1
  have hdet : (G t).det = (((G t).det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre0.2])
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp only [Complex.ofReal_re]
  ring

noncomputable def betaNatInt (i j : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j

/- English proof (translation)
Unfold `betaNatInt`. Simplify using `only [pow_zero, one_mul]`. Establish `h` using `intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ j) (a := 0) (b := 1) 1`. Simplify using `only [sub_zero, sub_self] at h`. Rewrite using `[h, integral_pow]`.

Establish `hj : (j : ℝ) + 1 ≠ 0` using `by positivity`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
theorem bI_zero (j : ℕ) : ((j : ℝ) + 1) * betaNatInt 0 j = 1 := by
  unfold betaNatInt
  simp only [pow_zero, one_mul]
  have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ j) (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  simp
  field_simp

/- English proof (translation)
Unfold `betaNatInt`. Establish `hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (i + 1)) (((i:ℝ) + 1) * x ^ i) x`. Introduce `x _`. Simplify using `using hasDerivAt_pow (i + 1) x`. Establish `hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => -(1 - x) ^ (j + 1)) (((j:ℝ) + 1) * (1 - x) ^ j) x`.

Introduce `x _`. Establish `h2` using `(((hasDerivAt_id x).const_sub 1).pow (j + 1)).neg`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Use `first`. Consider the case `(simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring)`.

Consider the case `(simp; ring)`. Consider the case `simp`. Establish `hparts` using `intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)`. Establish `e1 : ∫ x in (0:ℝ)..1, ((j:ℝ) + 1) * (x ^ (i + 1) * (1 - x) ^ j) = ∫ x in (0:ℝ)..1, x ^ (i + 1) * (((j:ℝ) + 1) * (1 - x) ^ j)`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * (x ^ i * (1 - x) ^ (j + 1)) = -∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * x ^ i * (-(1 - x) ^ (j + 1))`. Rewrite using `[← intervalIntegral.integral_neg]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, e1, e2, hparts]`. Simplify using the standard rewrite rules.
-/
theorem bI_succ (i j : ℕ) : ((j : ℝ) + 1) * betaNatInt (i + 1) j = ((i : ℝ) + 1) * betaNatInt i (j + 1) := by
  unfold betaNatInt
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ (i + 1)) (((i:ℝ) + 1) * x ^ i) x := by
    intro x _
    simpa using hasDerivAt_pow (i + 1) x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => -(1 - x) ^ (j + 1)) (((j:ℝ) + 1) * (1 - x) ^ j) x := by
    intro x _
    have h2 := (((hasDerivAt_id x).const_sub 1).pow (j + 1)).neg
    refine h2.congr_deriv ?_
    first
      | (simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring)
      | (simp; ring)
      | simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have e1 : ∫ x in (0:ℝ)..1, ((j:ℝ) + 1) * (x ^ (i + 1) * (1 - x) ^ j) =
      ∫ x in (0:ℝ)..1, x ^ (i + 1) * (((j:ℝ) + 1) * (1 - x) ^ j) := by
    congr 1; funext x; ring
  have e2 : ∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * (x ^ i * (1 - x) ^ (j + 1)) =
      -∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * x ^ i * (-(1 - x) ^ (j + 1)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, e1, e2, hparts]
  simp

/- English proof (translation)
Proceed by induction on `i generalizing j with`. Consider the case `zero => simpa using bI_zero j`. Consider the case `succ i ih`. Establish `h1` using `bI_succ i j`. Establish `h2` using `ih (j + 1)`.

Establish `e3 : i + (j + 1) = i + j + 1` using `by omega`. Rewrite `h2` using `[e3]`. Move the coercions through the operations in `at h2`. Establish `h3 : ((i + j + 1).choose (i + 1) : ℝ) * ((i:ℝ) + 1) = ((i + j + 1).choose i : ℝ) * ((j:ℝ) + 1)`. Use `Nat.choose_succ_right_eq (i + j + 1) i` as an intermediate fact.

Establish `e : i + j + 1 - i = j + 1` using `by omega`. Rewrite `this` using `[e]`. Conclude with `this` after adjusting the coercions. Establish `hj : ((j:ℝ) + 1) ≠ 0` using `by positivity`. Establish `e2 : i + 1 + j = i + j + 1` using `by omega`.

Rewrite using `[e2]`. Use `push_cast`. Apply `mul_right_cancel₀ hj` to reduce the goal to its premises. Take the linear combination `((i:ℝ) + j + 2) * ((i + j + 1).choose (i + 1) : ℝ) * h1 + ((i:ℝ) + j + 2) * betaNatInt i (j + 1) * h3 + ((j:ℝ) + 1) * h2`.
-/
theorem bI_closed (i j : ℕ) : ((i : ℝ) + j + 1) * ((i + j).choose i : ℝ) * betaNatInt i j = 1 := by
  induction i generalizing j with
  | zero => simpa using bI_zero j
  | succ i ih =>
    have h1 := bI_succ i j
    have h2 := ih (j + 1)
    have e3 : i + (j + 1) = i + j + 1 := by omega
    rw [e3] at h2
    push_cast at h2
    have h3 : ((i + j + 1).choose (i + 1) : ℝ) * ((i:ℝ) + 1) =
        ((i + j + 1).choose i : ℝ) * ((j:ℝ) + 1) := by
      have := Nat.choose_succ_right_eq (i + j + 1) i
      have e : i + j + 1 - i = j + 1 := by omega
      rw [e] at this
      exact_mod_cast this
    have hj : ((j:ℝ) + 1) ≠ 0 := by positivity
    have e2 : i + 1 + j = i + j + 1 := by omega
    rw [e2]
    push_cast
    apply mul_right_cancel₀ hj
    linear_combination ((i:ℝ) + j + 2) * ((i + j + 1).choose (i + 1) : ℝ) * h1 +
      ((i:ℝ) + j + 2) * betaNatInt i (j + 1) * h3 + ((j:ℝ) + 1) * h2

/- English proof (translation)
Establish `h` using `bI_closed i (D - i)`. Establish `e : i + (D - i) = D` using `by omega`. Rewrite `h` using `[e]`. Establish `hcast : ((i:ℝ) + ((D - i : ℕ) : ℝ) + 1) = (D:ℝ) + 1`. Rewrite using `[Nat.cast_sub hi]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hcast]`. Unfold `betaNatInt at h`. Establish `hD : (D:ℝ) + 1 ≠ 0` using `by positivity`. Repeatedly rewrite using `[mul_assoc]`.

Rewrite using `[intervalIntegral.integral_const_mul, eq_div_iff hD]`. Take the linear combination `h`.
-/
theorem integral_bernstein (D i : ℕ) (hi : i ≤ D) :
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / (D + 1 : ℝ) := by
  have h := bI_closed i (D - i)
  have e : i + (D - i) = D := by omega
  rw [e] at h
  have hcast : ((i:ℝ) + ((D - i : ℕ) : ℝ) + 1) = (D:ℝ) + 1 := by
    rw [Nat.cast_sub hi]; ring
  rw [hcast] at h
  unfold betaNatInt at h
  have hD : (D:ℝ) + 1 ≠ 0 := by positivity
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, eq_div_iff hD]
  linear_combination h

end ReciprocityTheory.GeometryOfNumbersTheory
