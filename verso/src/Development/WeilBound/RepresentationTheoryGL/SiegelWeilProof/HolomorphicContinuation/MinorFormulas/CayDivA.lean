import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

abbrev wz (n i : ℕ) : Fm n := MvPolynomial.C (Polynomial.X ^ i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hmem : Q ∈ Ideal.map (MvPolynomial.C : Polynomial ℂ →+* Fm n) (Ideal.span {(Polynomial.X ^ i : Polynomial ℂ)})`. Rewrite using `[MvPolynomial.mem_map_C_iff]`. Introduce `e`.

Conclude with `Ideal.mem_span_singleton.mpr (h e)`. Rewrite `hmem` using `[Ideal.map_span, Set.image_singleton]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hmem`. Conclude with `⟨a, ha.symm⟩`. Introduce and unpack `⟨R, rfl⟩ e`.

Rewrite using `[mul_comm, MvPolynomial.coeff_C_mul]`. Conclude with `dvd_mul_right _ _`.
-/
theorem divZ_iff (i : ℕ) (Q : Fm n) : DivZ i Q ↔ ∃ R : Fm n, Q = R * wz n i := by
  constructor
  · intro h
    have hmem : Q ∈ Ideal.map (MvPolynomial.C : Polynomial ℂ →+* Fm n)
        (Ideal.span {(Polynomial.X ^ i : Polynomial ℂ)}) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro e
      exact Ideal.mem_span_singleton.mpr (h e)
    rw [Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨a, ha.symm⟩
  · rintro ⟨R, rfl⟩ e
    rw [mul_comm, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right _ _

/- English proof (translation)
Introduce `e` and use `by simp`.
-/
theorem divZ_zero (i : ℕ) : DivZ i (0 : Fm n) := fun e => by simp

/- English proof (translation)
Introduce `e` and use `by rw [MvPolynomial.coeff_add]; exact dvd_add (hP e) (hQ e)`.
-/
theorem divZ_add {i : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ i Q) : DivZ i (P + Q) := fun e => by
  rw [MvPolynomial.coeff_add]; exact dvd_add (hP e) (hQ e)

/- English proof (translation)
Take `⟨R₁, rfl⟩` from `(divZ_iff i P).1 hP`. Take `⟨R₂, rfl⟩` from `(divZ_iff j Q).1 hQ`. Use `(divZ_iff _ _).2 ⟨R₁ * R₂, ?_⟩` and prove the remaining obligations. Simplify using `only [wz, pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem divZ_mul {i j : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ j Q) : DivZ (i + j) (P * Q) := by
  obtain ⟨R₁, rfl⟩ := (divZ_iff i P).1 hP
  obtain ⟨R₂, rfl⟩ := (divZ_iff j Q).1 hQ
  refine (divZ_iff _ _).2 ⟨R₁ * R₂, ?_⟩
  simp only [wz, pow_add, map_mul]
  ring

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def aa (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

/- English proof (translation)
Apply the tactic sequence `cases b <;>`. Simplify using `only [opH, cc, aa, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Bool.false_eq_true, if_true, if_false]`.
-/
theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    opH s m b k l Q = (-(cc s b)) • (MvPolynomial.C (aa m b) * yv b l k * Q) +
      ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * pderiv (b, a, d) Q) := by
  cases b <;>
  simp only [opH, cc, aa, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Bool.false_eq_true, if_true, if_false]

def RCP (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ (R : Fm n) (q : Polynomial ℂ), T (R * MvPolynomial.C q) = T R * MvPolynomial.C q

/- English proof (translation)
Introduce `R q`. Establish `hd : ∀ v, pderiv v (R * MvPolynomial.C q) = pderiv v R * MvPolynomial.C q`. Introduce `v`. Rewrite using `[Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul, mul_comm]`. Rewrite using `[opH_apply, opH_apply]`.

Simplify using `only [hd, add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc]`.
-/
theorem opH_rcp (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : RCP (opH s m b k l) := by
  intro R q
  have hd : ∀ v, pderiv v (R * MvPolynomial.C q) = pderiv v R * MvPolynomial.C q := by
    intro v
    rw [Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [opH_apply, opH_apply]
  simp only [hd, add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc]

/- English proof (translation)
Introduce `R q` and use `by simp only [LinearMap.comp_apply, hU R q, hT _ q]`.
-/
theorem rcp_comp {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T ∘ₗ U) := fun R q => by
  simp only [LinearMap.comp_apply, hU R q, hT _ q]

/- English proof (translation)
Introduce `R q` and use `by simp only [LinearMap.add_apply, hT R q, hU R q, add_mul]`.
-/
theorem rcp_add {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T + U) := fun R q => by
  simp only [LinearMap.add_apply, hT R q, hU R q, add_mul]

/- English proof (translation)
Introduce `R q` and use `by simp only [LinearMap.smul_apply, hT R q, smul_mul_assoc]`.
-/
theorem rcp_smul (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) : RCP (c • T) := fun R q => by
  simp only [LinearMap.smul_apply, hT R q, smul_mul_assoc]

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem rcp_id : RCP (LinearMap.id : Fm n →ₗ[ℂ] Fm n) := fun _ _ => rfl

/- English proof (translation)
Take `⟨R, rfl⟩` from `(divZ_iff i Q).1 hQ`. Conclude with `(divZ_iff i _).2 ⟨T R, hT R _⟩`.
-/
theorem divZ_of_rcp {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) {i : ℕ} {Q : Fm n} (hQ : DivZ i Q) : DivZ i (T Q) := by
  obtain ⟨R, rfl⟩ := (divZ_iff i Q).1 hQ
  exact (divZ_iff i _).2 ⟨T R, hT R _⟩

def LCP (Q' : Fm n) (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ R : Fm n, T (Q' * R) = Q' * T R

/- English proof (translation)
Introduce `R`. Establish `hd : ∀ a d : Fin n, pderiv (false, a, d) (Q' * R) = Q' * pderiv (false, a, d) R`. Introduce `a d`. Rewrite using `[Derivation.leibniz, hQ a d, smul_zero, add_zero, smul_eq_mul]`. Rewrite using `[opH_apply, opH_apply, mul_add, Finset.mul_sum]`.

Use `congr 1`. Rewrite using `[mul_smul_comm]; exact congrArg _ (by ring)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[hd, mul_smul_comm]; exact congrArg _ (by ring)`.
-/
theorem opH_false_lcp (s : ℂ) (m : ℕ) (k l : Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (opH s m false k l) := by
  intro R
  have hd : ∀ a d : Fin n, pderiv (false, a, d) (Q' * R) = Q' * pderiv (false, a, d) R := by
    intro a d
    rw [Derivation.leibniz, hQ a d, smul_zero, add_zero, smul_eq_mul]
  rw [opH_apply, opH_apply, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_smul_comm]; exact congrArg _ (by ring)
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hd, mul_smul_comm]; exact congrArg _ (by ring)

/- English proof (translation)
Introduce `R` and use `by simp only [LinearMap.comp_apply, hU R, hT _]`.
-/
theorem lcp_comp {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T ∘ₗ U) := fun R => by
  simp only [LinearMap.comp_apply, hU R, hT _]

/- English proof (translation)
Introduce `R` and use `by simp only [LinearMap.add_apply, hT R, hU R, mul_add]`.
-/
theorem lcp_add {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T + U) := fun R => by
  simp only [LinearMap.add_apply, hT R, hU R, mul_add]

/- English proof (translation)
Introduce `R` and use `by simp only [LinearMap.smul_apply, hT R, mul_smul_comm]`.
-/
theorem lcp_smul {Q' : Fm n} (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) : LCP Q' (c • T) := fun R => by
  simp only [LinearMap.smul_apply, hT R, mul_smul_comm]

/- English proof (translation)
Introduce `_` and use `rfl`.
-/
theorem lcp_id {Q' : Fm n} : LCP Q' (LinearMap.id : Fm n →ₗ[ℂ] Fm n) := fun _ => rfl

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro R`. Simplify using the standard rewrite rules. Consider the case `insert a t ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `lcp_add (hT a (Finset.mem_insert_self a t)) (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))`.
-/
theorem lcp_sum {Q' : Fm n} {ι : Type*} (t : Finset ι) (T : ι → Fm n →ₗ[ℂ] Fm n) (hT : ∀ i ∈ t, LCP Q' (T i)) :
    LCP Q' (∑ i ∈ t, T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro R; simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact lcp_add (hT a (Finset.mem_insert_self a t)) (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact lcp_id`. Consider the case `cons a L ih => exact lcp_comp (hf a) ih`.
-/
theorem lcp_foldr {Q' : Fm n} {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k, LCP Q' (f k)) (L : List (Fin ρ)) :
    LCP Q' (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) := by
  induction L with
  | nil => exact lcp_id
  | cons a L ih => exact lcp_comp (hf a) ih

/- English proof (translation)
Proceed by induction on `N generalizing R with`. Consider the case `zero => rfl`. Consider the case `succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT R, ih]`.
-/
theorem lcp_iterate {Q' : Fm n} {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (N : ℕ) (R : Fm n) :
    T^[N] (Q' * R) = Q' * T^[N] R := by
  induction N generalizing R with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT R, ih]

/- English proof (translation)
Unfold `minorOp`. Use `lcp_sum _ _ fun σ _ => lcp_smul _ (lcp_foldr _ (fun k => opH_false_lcp s m _ _ hQ) _)` and prove the remaining obligations.
-/
theorem minorOp_false_lcp (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (minorOp s m false I J) := by
  unfold minorOp
  refine lcp_sum _ _ fun σ _ => lcp_smul _ (lcp_foldr _ (fun k => opH_false_lcp s m _ _ hQ) _)

def AT (n : ℕ) : Subalgebra (Polynomial ℂ) (Fm n) :=
  Algebra.adjoin (Polynomial ℂ) (Set.range fun v : Fin n × Fin n => (MvPolynomial.X (true, v.1, v.2) : Fm n))

/- English proof (translation)
Proceed by induction on `hQ using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Conclude with `pderiv_X_of_ne (by simp)`. Consider the case `algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]`.
-/
theorem pderiv_false_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (false, a, d) Q = 0 := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact pderiv_X_of_ne (by simp)
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

/- English proof (translation)
Proceed by induction on `hQ using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Rewrite using `[pderiv_X, Pi.single_apply]`. Use `split_ifs`.

Conclude with `Subalgebra.one_mem _`. Conclude with `Subalgebra.zero_mem _`. Consider the case `algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]`. Conclude with `Subalgebra.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Subalgebra.add_mem _ hx hy`. Consider the case `mul x y hx' hy' hx hy`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx' hy) (Subalgebra.mul_mem _ hy' hx)`.
-/
theorem pderiv_true_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (true, a, d) Q ∈ AT n := by
  classical
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx' hy) (Subalgebra.mul_mem _ hy' hx)

/- English proof (translation)
Rewrite using `[← algebraMap_smul (Polynomial ℂ) c Q]`. Conclude with `Subalgebra.smul_mem _ hQ _`.
-/
theorem smul_mem_AT (c : ℂ) {Q : Fm n} (hQ : Q ∈ AT n) : c • Q ∈ AT n := by
  rw [← algebraMap_smul (Polynomial ℂ) c Q]
  exact Subalgebra.smul_mem _ hQ _

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨(i, j), rfl⟩`.
-/
theorem yv_true_mem (i j : Fin n) : yv true i j ∈ AT n := Algebra.subset_adjoin ⟨(i, j), rfl⟩

/- English proof (translation)
Rewrite using `[opH_apply]`. Use `Subalgebra.add_mem _ (smul_mem_AT _ ?_) (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun d _ => smul_mem_AT _ ?_)` and prove the remaining obligations. Use `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (yv_true_mem _ _)) hQ` and prove the remaining obligations. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `Subalgebra.algebraMap_mem _ _`.

Conclude with `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (yv_true_mem _ _) (yv_true_mem _ _)) (pderiv_true_AT hQ a d)`.
-/
theorem opH_true_AT (s : ℂ) (m : ℕ) (k l : Fin n) {Q : Fm n} (hQ : Q ∈ AT n) : opH s m true k l Q ∈ AT n := by
  rw [opH_apply]
  refine Subalgebra.add_mem _ (smul_mem_AT _ ?_) (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun d _ =>
    smul_mem_AT _ ?_)
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (yv_true_mem _ _)) hQ
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (yv_true_mem _ _) (yv_true_mem _ _)) (pderiv_true_AT hQ a d)

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact hQ`. Consider the case `cons a L ih => exact hf a _ ih`.
-/
theorem foldr_AT {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k Q, Q ∈ AT n → f k Q ∈ AT n) (L : List (Fin ρ))
    {Q : Fm n} (hQ : Q ∈ AT n) : (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) Q ∈ AT n := by
  induction L with
  | nil => exact hQ
  | cons a L ih => exact hf a _ ih

/- English proof (translation)
Unfold `minorOp`. Rewrite using `[LinearMap.sum_apply]`. Conclude with `Subalgebra.sum_mem _ fun σ _ => by`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `smul_mem_AT _ (foldr_AT _ (fun k Q hQ => opH_true_AT s m _ _ hQ) _ hQ)`.
-/
theorem minorOp_true_AT (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q : Fm n} (hQ : Q ∈ AT n) :
    minorOp s m true I J Q ∈ AT n := by
  unfold minorOp
  rw [LinearMap.sum_apply]
  exact Subalgebra.sum_mem _ fun σ _ => by
    rw [LinearMap.smul_apply]
    exact smul_mem_AT _ (foldr_AT _ (fun k Q hQ => opH_true_AT s m _ _ hQ) _ hQ)

/- English proof (translation)
Proceed by induction on `N generalizing Q with`. Consider the case `zero => exact hQ`. Consider the case `succ N ih => rw [Function.iterate_succ_apply]`. Conclude with `ih (hT Q hQ)`.
-/
theorem iterate_AT {T : Fm n →ₗ[ℂ] Fm n} (hT : ∀ Q, Q ∈ AT n → T Q ∈ AT n) (N : ℕ) {Q : Fm n} (hQ : Q ∈ AT n) :
    T^[N] Q ∈ AT n := by
  induction N generalizing Q with
  | zero => exact hQ
  | succ N ih => rw [Function.iterate_succ_apply]; exact ih (hT Q hQ)

end PositivityTheory.Rg.Sw.SP
