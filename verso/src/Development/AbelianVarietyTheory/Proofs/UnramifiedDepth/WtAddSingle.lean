import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.DetPowPairing

open MvPolynomial

variable {σ : Type} {C : Type} [CommRing C]

def wt (C : Type) [CommRing C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)

def pair : MvPolynomial σ C →ₗ[C] MvPolynomial σ C →ₗ[C] C :=
  (basisMonomials σ C).constr C fun A => wt C A • lcoeff C A

/- English proof (translation)
Establish `h : monomial A c = c • (basisMonomials σ C) A`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul, pair, Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul, smul_eq_mul, mul_assoc]`.
-/
theorem pair_monomial (A : σ →₀ ℕ) (c : C) (Q : MvPolynomial σ C) :
    pair (monomial A c) Q = c * wt C A * coeff A Q := by
  have h : monomial A c = c • (basisMonomials σ C) A := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pair, Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.smul_apply, lcoeff_apply,
    smul_eq_mul, smul_eq_mul, mul_assoc]

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun A _ => pair_monomial A (coeff A P) Q`.
-/
theorem pair_eq (P Q : MvPolynomial σ C) :
    pair P Q = ∑ A ∈ P.support, coeff A P * wt C A * coeff A Q := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun A _ => pair_monomial A (coeff A P) Q

/- English proof (translation)
Use `set s := A.support ∪ {j} with hs`. Establish `hA : wt C A = ∏ i ∈ s, ((A i).factorial : C)` using `Finsupp.prod_of_support_subset A Finset.subset_union_left _ (fun _ _ => by simp)`. Establish `hsupp : (A + Finsupp.single j 1).support ⊆ s`. Introduce `i hi`. Rewrite `hi` using `[Finsupp.mem_support_iff]`.

Distinguish the cases in `h : i = j`. Simplify using `[s, h]`. Establish `hAi : A i ≠ 0` using `by simpa [Finsupp.single_apply, Ne.symm h] using hi`. Simplify using `[s, Finsupp.mem_support_iff, hAi]`. Establish `hB : wt C (A + Finsupp.single j 1) = ∏ i ∈ s, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C)` using `Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)`.

Establish `hj : j ∈ s` using `by simp [s]`. Establish `hrest : ∏ i ∈ s.erase j, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) = ∏ i ∈ s.erase j, ((A i).factorial : C)`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hij : i ≠ j` using `Finset.ne_of_mem_erase hi`. Simplify using `[Ne.symm hij]`.

Rewrite using `[hA, hB, ← Finset.mul_prod_erase s _ hj, ← Finset.mul_prod_erase s _ hj, hrest]`. Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wt_add_single (A : σ →₀ ℕ) (j : σ) :
    wt C (A + Finsupp.single j 1) = wt C A * ((A j : C) + 1) := by
  classical
  set s := A.support ∪ {j} with hs
  have hA : wt C A = ∏ i ∈ s, ((A i).factorial : C) :=
    Finsupp.prod_of_support_subset A Finset.subset_union_left _ (fun _ _ => by simp)
  have hsupp : (A + Finsupp.single j 1).support ⊆ s := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = j
    · simp [s, h]
    · have hAi : A i ≠ 0 := by simpa [Finsupp.single_apply, Ne.symm h] using hi
      simp [s, Finsupp.mem_support_iff, hAi]
  have hB : wt C (A + Finsupp.single j 1) = ∏ i ∈ s, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) :=
    Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)
  have hj : j ∈ s := by simp [s]
  have hrest : ∏ i ∈ s.erase j, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) =
      ∏ i ∈ s.erase j, ((A i).factorial : C) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Ne.symm hij]
  rw [hA, hB, ← Finset.mul_prod_erase s _ hj, ← Finset.mul_prod_erase s _ hj, hrest]
  simp [Nat.factorial_succ]
  ring

/- English proof (translation)
The claim follows from `coeff_pderiv Q A`.
-/
theorem coeff_pderiv' (j : σ) (A : σ →₀ ℕ) (Q : MvPolynomial σ C) :
    coeff A (pderiv j Q) = coeff (A + Finsupp.single j 1) Q * ((A j : C) + 1) :=
  coeff_pderiv Q A

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[pair_eq P, Finset.sum_mul, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[show (X j : MvPolynomial σ C) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul, mul_one, pair_monomial, coeff_pderiv', wt_add_single]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_X_mul (j : σ) (P Q : MvPolynomial σ C) :
    pair (P * X j) Q = pair P (pderiv j Q) := by
  conv_lhs => rw [P.as_sum]
  rw [pair_eq P, Finset.sum_mul, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [show (X j : MvPolynomial σ C) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul, mul_one,
    pair_monomial, coeff_pderiv', wt_add_single]
  ring

/- English proof (translation)
Proceed by induction on `l generalizing P with`. Consider the case `nil => simp`. Consider the case `cons j l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, ih, pair_X_mul]`. Both sides reduce to the same expression.
-/
theorem pair_list {ι : Type} (f : ι → σ) (l : List ι) (P Q : MvPolynomial σ C) :
    pair (P * (l.map fun j => X (f j)).prod) Q =
      pair P (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l generalizing P with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, ih, pair_X_mul]
    rfl

/- English proof (translation)
Establish `hdet : cayDet n C = ∑ s : Equiv.Perm (Fin n), (Equiv.Perm.sign s : ℤ) • ((List.finRange n).map fun i => (X (s i, i) : MvPolynomial _ C)).prod`. Rewrite using `[cayDet, Matrix.det_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, Fin.prod_univ_def]`. Both sides reduce to the same expression.

Rewrite using `[hdet, cayOp, Finset.mul_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul]`. Conclude with `congrArg (fun t => (Equiv.Perm.sign s : ℤ) • t) (pair_list (fun i => (s i, i)) (List.finRange n) P Q)`.
-/
theorem pair_det (n : ℕ) (P Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * cayDet n C) Q = pair P (cayOp n C Q) := by
  have hdet : cayDet n C = ∑ s : Equiv.Perm (Fin n),
      (Equiv.Perm.sign s : ℤ) • ((List.finRange n).map fun i => (X (s i, i) : MvPolynomial _ C)).prod := by
    rw [cayDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.smul_def, Fin.prod_univ_def]
    rfl
  rw [hdet, cayOp, Finset.mul_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul]
  exact congrArg (fun t => (Equiv.Perm.sign s : ℤ) • t) (pair_list (fun i => (s i, i)) (List.finRange n) P Q)

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `zero`. Establish `h1 : pair (1 : MvPolynomial (Fin n × Fin n) C) 1 = 1`. Rewrite using `[show (1 : MvPolynomial (Fin n × Fin n) C) = monomial 0 1 from rfl, pair_monomial]`. Simplify using `[wt]`.

Simplify using `[h1]`. Consider the case `succ x ih`. Establish `hc` using `cayley n C (x + 1)`. Rewrite `hc` using `[Nat.add_sub_cancel]`. Establish `hp : pair (cayDet n C ^ (x + 1)) (cayDet n C ^ (x + 1)) = pair (cayDet n C ^ x) (cayOp n C (cayDet n C ^ (x + 1)))`.

Rewrite using `[← pair_det, ← pow_succ]`. Rewrite using `[hp, hc, map_nsmul, nsmul_eq_mul, Nat.cast_prod, mul_left_comm, ih, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[show x + 1 + c = (x + c) + 1 by ring, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_pow (n x : ℕ) :
    (∏ c ∈ Finset.range n, (c.factorial : C)) * pair (cayDet n C ^ x) (cayDet n C ^ x) =
      ∏ c ∈ Finset.range n, ((x + c).factorial : C) := by
  induction x with
  | zero =>
    have h1 : pair (1 : MvPolynomial (Fin n × Fin n) C) 1 = 1 := by
      rw [show (1 : MvPolynomial (Fin n × Fin n) C) = monomial 0 1 from rfl, pair_monomial]
      simp [wt]
    simp [h1]
  | succ x ih =>
    have hc := cayley n C (x + 1)
    rw [Nat.add_sub_cancel] at hc
    have hp : pair (cayDet n C ^ (x + 1)) (cayDet n C ^ (x + 1)) =
        pair (cayDet n C ^ x) (cayOp n C (cayDet n C ^ (x + 1))) := by
      rw [← pair_det, ← pow_succ]
    rw [hp, hc, map_nsmul, nsmul_eq_mul, Nat.cast_prod, mul_left_comm, ih,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [show x + 1 + c = (x + c) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring

/- English proof (translation)
Introduce `C _ _ n₀ x`. Establish `h` using `pair_pow (C := C) n₀ x`. Rewrite `h` using `[pair_eq]`. Conclude with `h`.
-/
theorem main :
    (∀ (C : Type) [Field C] [CharZero C] (n₀ x : ℕ), (∏ c ∈ Finset.range n₀, (c.factorial : C)) * (∑ A ∈ (cayDet n₀ C ^ x).support, MvPolynomial.coeff A (cayDet n₀ C ^ x) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ x)) = ∏ c ∈ Finset.range n₀, ((x + c).factorial : C)) := by
  intro C _ _ n₀ x
  have h := pair_pow (C := C) n₀ x
  rw [pair_eq] at h
  exact h

end GlobalTheory.DetPowPairing
