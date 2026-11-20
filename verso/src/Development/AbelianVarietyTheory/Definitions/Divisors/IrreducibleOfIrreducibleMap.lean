import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AevalEqZeroOfHomogeneousComponent

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

structure IsChowFormInt {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k))
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => dl) f

  irred : Irreducible f

  zero_iff : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def IsChowFormCycle {k : Type} [Field k] {N : ℕ} (Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ)
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ ∃ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
    (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
    (∀ P ∈ Z.support, P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      IsChowFormInt P e (d P) (g P)) ∧
    dl = Z.sum (fun P m => m * d P) ∧ f = C c * Z.prod (fun P m => g P ^ m)

variable {k : Type} [Field k] {N : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.Chow.isBlockHomogeneous_iff.symm`.
-/
theorem isMultiHomogeneous_iff_block {B : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) k} :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f ↔ GlobalTheory.Chow.IsBlockHomogeneous f a :=
  GlobalTheory.Chow.isBlockHomogeneous_iff.symm

/- English proof (translation)
Establish `key : ∀ a : MvPolynomial σ k, IsUnit (MvPolynomial.map (algebraMap k K) a) → IsUnit a`. Introduce `a ha`. Take `⟨c, hc, hca⟩` from `isUnit_iff_eq_C_of_isReduced.1 ha`. Establish `h0 : algebraMap k K (coeff 0 a) = c`. Use `congrArg (coeff 0) hca` as an intermediate fact.

Rewrite `this` using `[coeff_map, coeff_zero_C]`. Then use the resulting hypothesis. Establish `ha' : a = C (coeff 0 a)`. Apply `map_injective (algebraMap k K) (algebraMap k K).injective` to reduce the goal to its premises. Rewrite using `[map_C, h0, hca]`. Rewrite using `[ha']`.

Use `(IsUnit.mk0 _ fun h => hc.ne_zero ?_).map C` and prove the remaining obligations. Rewrite using `[← h0, h, map_zero]`. Use `⟨fun hu => h.not_isUnit (hu.map _), fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hab, map_mul]`. Conclude with `(h.isUnit_or_isUnit rfl).imp (key a) (key b)`.
-/
theorem irreducible_of_irreducible_map {K σ : Type} [Field K] [Algebra k K] {f : MvPolynomial σ k}
    (h : Irreducible (MvPolynomial.map (algebraMap k K) f)) : Irreducible f := by
  have key : ∀ a : MvPolynomial σ k, IsUnit (MvPolynomial.map (algebraMap k K) a) → IsUnit a := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := isUnit_iff_eq_C_of_isReduced.1 ha
    have h0 : algebraMap k K (coeff 0 a) = c := by
      have := congrArg (coeff 0) hca
      rwa [coeff_map, coeff_zero_C] at this
    have ha' : a = C (coeff 0 a) := by
      apply map_injective (algebraMap k K) (algebraMap k K).injective
      rw [map_C, h0, hca]
    rw [ha']
    refine (IsUnit.mk0 _ fun h => hc.ne_zero ?_).map C
    rw [← h0, h, map_zero]
  refine ⟨fun hu => h.not_isUnit (hu.map _), fun a b hab => ?_⟩
  rw [hab, map_mul] at h
  exact (h.isUnit_or_isUnit rfl).imp (key a) (key b)

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.homog, irreducible_of_irreducible_map h.irred, h.zero_iff⟩`.
-/
theorem IsChowForm.isChowFormInt {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowForm I e dl f) :
    IsChowFormInt I e dl f :=
  ⟨h.homog, irreducible_of_irreducible_map h.irred, h.zero_iff⟩

namespace IsChowFormInt

variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

/- English proof (translation)
The claim follows from `h.irred.ne_zero`.
-/
theorem ne_zero (h : IsChowFormInt I e dl f) : f ≠ 0 := h.irred.ne_zero

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.homog, hf, h.zero_iff⟩`.
-/
theorem isChowForm (h : IsChowFormInt I e dl f)
    (hf : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)) :
    IsChowForm I e dl f := ⟨h.homog, hf, h.zero_iff⟩

/- English proof (translation)
Use `⟨?_, (irreducible_isUnit_mul ((IsUnit.mk0 c hc).map C)).2 h.irred, fun u => ?_⟩` and prove the remaining obligations. Conclude with `isMultiHomogeneous_iff_block.2 (IsWeightedHomogeneous.C_mul (isMultiHomogeneous_iff_block.1 h.homog) c)`. Rewrite using `[map_mul, aeval_C, mul_eq_zero, map_eq_zero, ← h.zero_iff u]`. Simplify using `[hc]`.
-/
theorem C_mul (h : IsChowFormInt I e dl f) {c : k} (hc : c ≠ 0) :
    IsChowFormInt I e dl (C c * f) := by
  refine ⟨?_, (irreducible_isUnit_mul ((IsUnit.mk0 c hc).map C)).2 h.irred, fun u => ?_⟩
  · exact isMultiHomogeneous_iff_block.2
      (IsWeightedHomogeneous.C_mul (isMultiHomogeneous_iff_block.1 h.homog) c)
  · rw [map_mul, aeval_C, mul_eq_zero, map_eq_zero, ← h.zero_iff u]
    simp [hc]

/- English proof (translation)
Use `haveI : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime h.ne_zero).2 h.irred.prime`. Rewrite using `[← Ideal.mem_span_singleton, ← IsPrime.vanishingIdeal_zeroLocus (K := AlgebraicClosure k) (Ideal.span {f})]`. Conclude with `fun u hu => hp u (hu f (Ideal.subset_span rfl))`.
-/
theorem dvd_of_forall_aeval_eq_zero (h : IsChowFormInt I e dl f)
    {p : MvPolynomial (Fin (e + 1) × Fin N) k}
    (hp : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, aeval u f = 0 → aeval u p = 0) :
    f ∣ p := by
  haveI : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime h.ne_zero).2 h.irred.prime
  rw [← Ideal.mem_span_singleton,
    ← IsPrime.vanishingIdeal_zeroLocus (K := AlgebraicClosure k) (Ideal.span {f})]
  exact fun u hu => hp u (hu f (Ideal.subset_span rfl))

/- English proof (translation)
Establish `h1 : f ∣ f'` using `h.dvd_of_forall_aeval_eq_zero fun u hu => (h'.zero_iff u).2 ((h.zero_iff u).1 hu)`. Establish `h2 : f' ∣ f` using `h'.dvd_of_forall_aeval_eq_zero fun u hu => (h.zero_iff u).2 ((h'.zero_iff u).1 hu)`. Take `⟨c, hc, hf⟩` from `GlobalTheory.Chow.exists_eq_C_mul_of_span_eq (Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd h1 h2))`. Use `⟨?_, c, hc, hf⟩` and prove the remaining obligations. Establish `h3` using `(h.C_mul hc).homog`.

Rewrite `h3` using `[← hf]`. Conclude with `congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique h'.ne_zero (isMultiHomogeneous_iff_block.1 h3) (isMultiHomogeneous_iff_block.1 h'.homog)) 0`.
-/
theorem unique (h : IsChowFormInt I e dl f) (h' : IsChowFormInt I e dl' f') :
    dl = dl' ∧ ∃ c : k, c ≠ 0 ∧ f' = C c * f := by
  have h1 : f ∣ f' := h.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h'.zero_iff u).2 ((h.zero_iff u).1 hu)
  have h2 : f' ∣ f := h'.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h.zero_iff u).2 ((h'.zero_iff u).1 hu)
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq
    (Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd h1 h2))
  refine ⟨?_, c, hc, hf⟩
  have h3 := (h.C_mul hc).homog
  rw [← hf] at h3
  exact congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique h'.ne_zero
    (isMultiHomogeneous_iff_block.1 h3) (isMultiHomogeneous_iff_block.1 h'.homog)) 0

/- English proof (translation)
Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]`. Use `le_antisymm ?_ fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `fun u hu => (h.zero_iff u).2 ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).1 hu)`. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `h.dvd_of_forall_aeval_eq_zero fun u hu => hp u ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).2 ((h.zero_iff u).1 hu))`.
-/
theorem span_eq_radical_elimIdeal (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]
  refine le_antisymm ?_ fun p hp => ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact fun u hu => (h.zero_iff u).2 ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).1 hu)
  · rw [Ideal.mem_span_singleton]
    exact h.dvd_of_forall_aeval_eq_zero fun u hu =>
      hp u ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).2 ((h.zero_iff u).1 hu))

/- English proof (translation)
Rewrite using `[← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u]`. Establish `hs` using `h.span_eq_radical_elimIdeal hI`. Use `⟨fun hu p hp => ?_, fun hu => ?_⟩` and prove the remaining obligations. Establish `: p ∈ Ideal.span {f}` using `hs ▸ Ideal.le_radical hp`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 this`.

Rewrite using `[map_mul, hu, mul_zero]`. Establish `: f ∈ (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical` using `hs ▸ Ideal.subset_span rfl`. Take `⟨n, hn⟩` from `this`. Use `hu _ hn` as an intermediate fact. Rewrite `this` using `[map_pow]`.

Conclude with `eq_zero_of_pow_eq_zero this`.
-/
theorem zero_iff_of_isAlgClosed (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by
  rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u]
  have hs := h.span_eq_radical_elimIdeal hI
  refine ⟨fun hu p hp => ?_, fun hu => ?_⟩
  · have : p ∈ Ideal.span {f} := hs ▸ Ideal.le_radical hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 this
    rw [map_mul, hu, mul_zero]
  · have : f ∈ (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := hs ▸ Ideal.subset_span rfl
    obtain ⟨n, hn⟩ := this
    have := hu _ hn
    rw [map_pow] at this
    exact eq_zero_of_pow_eq_zero this

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `h.irred.not_isUnit (isUnit_of_dvd_one (h.dvd_of_forall_aeval_eq_zero fun u hu => ?_))` and prove the remaining obligations. Take `⟨y, hy, hI, -⟩` from `(h.zero_iff u).1 hu`. Conclude with `(hc ⟨y, hy, hI⟩).elim`.
-/
theorem exists_point (h : IsChowFormInt I e dl f) :
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ ∀ g ∈ I, MvPolynomial.aeval y g = 0 := by
  by_contra hc
  refine h.irred.not_isUnit (isUnit_of_dvd_one (h.dvd_of_forall_aeval_eq_zero fun u hu => ?_))
  obtain ⟨y, hy, hI, -⟩ := (h.zero_iff u).1 hu
  exact (hc ⟨y, hy, hI⟩).elim

/- English proof (translation)
Take `⟨y, hy, hyI⟩` from `h.exists_point`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hy`. Establish `: (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).IsPrime` using `GlobalTheory.Chow.isPrime_elimIdeal ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩`. Rewrite using `[h.span_eq_radical_elimIdeal hI, this.radical]`.
-/
theorem span_eq_elimIdeal (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have : (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).IsPrime :=
    GlobalTheory.Chow.isPrime_elimIdeal ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩
  rw [h.span_eq_radical_elimIdeal hI, this.radical]

/- English proof (translation)
Use `Nat.pos_of_ne_zero fun h0 => ?_` and prove the remaining obligations. Substitute `h0` using the available equality. Establish `h1` using `(isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous`. Simplify using `only [Finset.sum_const_zero] at h1`. Establish `h2` using `h1.totalDegree_le`.

Rewrite `h2` using `[Nat.le_zero, totalDegree_eq_zero_iff_eq_C]`. Use `h.irred.not_isUnit ?_` and prove the remaining obligations. Rewrite using `[h2]`. Use `(IsUnit.mk0 _ fun h3 => h.ne_zero ?_).map C` and prove the remaining obligations. Rewrite using `[h2, h3, C_0]`.
-/
theorem pos (h : IsChowFormInt I e dl f) : 0 < dl := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  have h1 := (isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous
  simp only [Finset.sum_const_zero] at h1
  have h2 := h1.totalDegree_le
  rw [Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at h2
  refine h.irred.not_isUnit ?_
  rw [h2]
  refine (IsUnit.mk0 _ fun h3 => h.ne_zero ?_).map C
  rw [h2, h3, C_0]

/- English proof (translation)
Use `⟨1, one_ne_zero, fun _ => dl, fun _ => f, fun P hP => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `rfl` from `Finset.mem_singleton.1 (Finsupp.support_single_subset hP)`. Conclude with `⟨hp, hI, h⟩`. Apply the tactic sequence `rw [Finsupp.sum_single_index] <;> simp`. Apply the tactic sequence `rw [Finsupp.prod_single_index] <;> simp`.
-/
theorem single (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    IsChowFormCycle (Finsupp.single I 1) e dl f := by
  refine ⟨1, one_ne_zero, fun _ => dl, fun _ => f, fun P hP => ?_, ?_, ?_⟩
  · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hP)
    exact ⟨hp, hI, h⟩
  · rw [Finsupp.sum_single_index] <;> simp
  · rw [Finsupp.prod_single_index] <;> simp

end IsChowFormInt

/- English proof (translation)
Introduce `h` and use `by obtain ⟨y, -, hy⟩ := h.exists_point simpa using hy 1 trivial`.
-/
theorem not_isChowFormInt_top {e dl : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin N) k) :
    ¬ IsChowFormInt (⊤ : Ideal (MvPolynomial (Fin N) k)) e dl f := fun h => by
  obtain ⟨y, -, hy⟩ := h.exists_point
  simpa using hy 1 trivial

namespace IsChowFormCycle

variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}

/- English proof (translation)
Take `⟨c, -, d, g, hg, -, -⟩` from `h`. Conclude with `⟨(hg P hP).1, (hg P hP).2.1, d P, g P, (hg P hP).2.2⟩`.
-/
theorem component (h : IsChowFormCycle Z e dl f) {P : Ideal (MvPolynomial (Fin N) k)}
    (hP : P ∈ Z.support) : P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      ∃ d g, IsChowFormInt P e d g := by
  obtain ⟨c, -, d, g, hg, -, -⟩ := h
  exact ⟨(hg P hP).1, (hg P hP).2.1, d P, g P, (hg P hP).2.2⟩

/- English proof (translation)
Take `⟨c, hc, d, g, hg, -, rfl⟩` from `h`. Conclude with `mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ (hg P hP).2.2.ne_zero)`.
-/
theorem ne_zero (h : IsChowFormCycle Z e dl f) : f ≠ 0 := by
  obtain ⟨c, hc, d, g, hg, -, rfl⟩ := h
  exact mul_ne_zero (by simpa using hc)
    (Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ (hg P hP).2.2.ne_zero)

/- English proof (translation)
Take `⟨c, hc, d, g, hg, rfl, rfl⟩` from `h`. Rewrite using `[isMultiHomogeneous_iff_block]`. Use `IsWeightedHomogeneous.C_mul ?_ c` and prove the remaining obligations. Use `IsWeightedHomogeneous.prod (w := GlobalTheory.Chow.blockWeight) Z.support (fun P => g P ^ Z P) (fun P => Z P • fun _ : Fin (e + 1) => d P) (fun P hP => IsWeightedHomogeneous.pow (isMultiHomogeneous_iff_block.1 (hg P hP).2.2.homog) (Z P))` as an intermediate fact. Establish `hd : (fun _ : Fin (e + 1) => Z.sum fun P m => m * d P) = ∑ P ∈ Z.support, Z P • fun _ : Fin (e + 1) => d P`.

Use function extensionality and compare the values at `b`. Simplify using `[Finsupp.sum, Finset.sum_apply]`. Rewrite using `[hd]`. Conclude with `this`.
-/
theorem homog (h : IsChowFormCycle Z e dl f) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => dl) f := by
  obtain ⟨c, hc, d, g, hg, rfl, rfl⟩ := h
  rw [isMultiHomogeneous_iff_block]
  refine IsWeightedHomogeneous.C_mul ?_ c
  have := IsWeightedHomogeneous.prod (w := GlobalTheory.Chow.blockWeight) Z.support
    (fun P => g P ^ Z P) (fun P => Z P • fun _ : Fin (e + 1) => d P)
    (fun P hP => IsWeightedHomogeneous.pow
      (isMultiHomogeneous_iff_block.1 (hg P hP).2.2.homog) (Z P))
  have hd : (fun _ : Fin (e + 1) => Z.sum fun P m => m * d P) =
      ∑ P ∈ Z.support, Z P • fun _ : Fin (e + 1) => d P := by
    funext b
    simp [Finsupp.sum, Finset.sum_apply]
  rw [hd]
  exact this

/- English proof (translation)
Take `⟨c, hc, d, g, hg, hd, rfl⟩` from `h`. Conclude with `⟨a * c, mul_ne_zero ha hc, d, g, hg, hd, by rw [MvPolynomial.C_mul, mul_assoc]⟩`.
-/
theorem C_mul (h : IsChowFormCycle Z e dl f) {a : k} (ha : a ≠ 0) :
    IsChowFormCycle Z e dl (C a * f) := by
  obtain ⟨c, hc, d, g, hg, hd, rfl⟩ := h
  exact ⟨a * c, mul_ne_zero ha hc, d, g, hg, hd, by rw [MvPolynomial.C_mul, mul_assoc]⟩

/- English proof (translation)
Take `⟨c, hc, d₀, g₀, hg₀, rfl, rfl⟩` from `h`. Establish `hu` using `fun P hP => (hg P hP).unique (hg₀ P hP).2.2`. Use `⟨Finset.sum_congr rfl fun P hP => by simp only [(hu P hP).1], ?_⟩` and prove the remaining obligations. Use `choose a ha hag using fun P hP => (hu P hP).2`. Set `a' : Ideal (MvPolynomial (Fin N) k) → k` to `fun P => if hP : P ∈ Z.support then a P hP else 1`.

Use `⟨c * ∏ P ∈ Z.support, a' P ^ Z P, mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_), ?_⟩` and prove the remaining obligations. Simplify using `only [a', dif_pos hP]`. Conclude with `ha P hP`. Rewrite using `[MvPolynomial.C_mul, mul_assoc, map_prod, Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations. Simplify using `only [a', dif_pos hP]`. Rewrite using `[hag P hP, mul_pow, map_pow]`.
-/
theorem eq_of_components (h : IsChowFormCycle Z e dl f)
    (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
    (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k)
    (hg : ∀ P ∈ Z.support, IsChowFormInt P e (d P) (g P)) :
    dl = Z.sum (fun P m => m * d P) ∧ ∃ c : k, c ≠ 0 ∧ f = C c * Z.prod (fun P m => g P ^ m) := by
  classical
  obtain ⟨c, hc, d₀, g₀, hg₀, rfl, rfl⟩ := h
  have hu := fun P hP => (hg P hP).unique (hg₀ P hP).2.2
  refine ⟨Finset.sum_congr rfl fun P hP => by simp only [(hu P hP).1], ?_⟩
  choose a ha hag using fun P hP => (hu P hP).2
  let a' : Ideal (MvPolynomial (Fin N) k) → k := fun P => if hP : P ∈ Z.support then a P hP else 1
  refine ⟨c * ∏ P ∈ Z.support, a' P ^ Z P, mul_ne_zero hc
    (Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_), ?_⟩
  · simp only [a', dif_pos hP]; exact ha P hP
  · rw [MvPolynomial.C_mul, mul_assoc, map_prod, Finsupp.prod, Finsupp.prod,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    simp only [a', dif_pos hP]
    rw [hag P hP, mul_pow, map_pow]

/- English proof (translation)
Take `⟨c, hc, d, g, hg, rfl, rfl⟩` from `h`. Take `⟨hd, c', hc', rfl⟩` from `h'.eq_of_components d g fun P hP => (hg P hP).2.2`. Use `⟨hd.symm, c' * c⁻¹, mul_ne_zero hc' (inv_ne_zero hc), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← MvPolynomial.C_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]`.
-/
theorem unique (h : IsChowFormCycle Z e dl f) (h' : IsChowFormCycle Z e dl' f') :
    dl = dl' ∧ ∃ c : k, c ≠ 0 ∧ f' = C c * f := by
  obtain ⟨c, hc, d, g, hg, rfl, rfl⟩ := h
  obtain ⟨hd, c', hc', rfl⟩ := h'.eq_of_components d g fun P hP => (hg P hP).2.2
  refine ⟨hd.symm, c' * c⁻¹, mul_ne_zero hc' (inv_ne_zero hc), ?_⟩
  rw [← mul_assoc, ← MvPolynomial.C_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/- English proof (translation)
Establish `hex : ∀ P, ∃ d g, P ∈ Z.support ∪ Z'.support → (P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧ IsChowFormInt P e d g)`. Introduce `P`. Distinguish the cases in `hP : P ∈ Z.support ∪ Z'.support`. Break down `Finset.mem_union.1 hP with hP | hP` into its components or cases. Take `⟨h1, h2, d, g, h3⟩` from `h.component hP`.

Conclude with `⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩`. Take `⟨h1, h2, d, g, h3⟩` from `h'.component hP`. Conclude with `⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩`. Conclude with `⟨0, 0, fun h => (hP h).elim⟩`. Use `choose d g hg using hex`.

Take `⟨rfl, c, hc, rfl⟩` from `h.eq_of_components d g fun P hP => (hg P (Finset.mem_union_left _ hP)).2.2`. Take `⟨rfl, c', hc', rfl⟩` from `h'.eq_of_components d g fun P hP => (hg P (Finset.mem_union_right _ hP)).2.2`. Use `⟨c * c', mul_ne_zero hc hc', d, g, fun P hP => hg P (Finsupp.support_add hP), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]`. Rewrite using `[Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), MvPolynomial.C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem add (h : IsChowFormCycle Z e dl f) (h' : IsChowFormCycle Z' e dl' f') :
    IsChowFormCycle (Z + Z') e (dl + dl') (f * f') := by
  classical
  have hex : ∀ P, ∃ d g, P ∈ Z.support ∪ Z'.support → (P.IsPrime ∧
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧ IsChowFormInt P e d g) := by
    intro P
    by_cases hP : P ∈ Z.support ∪ Z'.support
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨h1, h2, d, g, h3⟩ := h.component hP
        exact ⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩
      · obtain ⟨h1, h2, d, g, h3⟩ := h'.component hP
        exact ⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => (hP h).elim⟩
  choose d g hg using hex
  obtain ⟨rfl, c, hc, rfl⟩ := h.eq_of_components d g fun P hP =>
    (hg P (Finset.mem_union_left _ hP)).2.2
  obtain ⟨rfl, c', hc', rfl⟩ := h'.eq_of_components d g fun P hP =>
    (hg P (Finset.mem_union_right _ hP)).2.2
  refine ⟨c * c', mul_ne_zero hc hc', d, g, fun P hP => hg P (Finsupp.support_add hP), ?_, ?_⟩
  · rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
  · rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), MvPolynomial.C_mul]
    ring

/- English proof (translation)
Take `⟨c, hc, d, g, hg, -, rfl⟩` from `h`. Rewrite using `[map_mul, aeval_C, mul_eq_zero, map_eq_zero, or_iff_right hc, Finsupp.prod, map_prod, Finset.prod_eq_zero_iff]`. Use `exists_congr fun P => and_congr_right fun hP => ?_` and prove the remaining obligations. Rewrite using `[map_pow, pow_eq_zero_iff (Finsupp.mem_support_iff.1 hP)]`. Conclude with `(hg P hP).2.2.zero_iff_of_isAlgClosed (hg P hP).2.1 u`.
-/
theorem zero_iff_of_isAlgClosed (h : IsChowFormCycle Z e dl f)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔ ∃ P ∈ Z.support,
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ P, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨c, hc, d, g, hg, -, rfl⟩ := h
  rw [map_mul, aeval_C, mul_eq_zero, map_eq_zero, or_iff_right hc, Finsupp.prod, map_prod,
    Finset.prod_eq_zero_iff]
  refine exists_congr fun P => and_congr_right fun hP => ?_
  rw [map_pow, pow_eq_zero_iff (Finsupp.mem_support_iff.1 hP)]
  exact (hg P hP).2.2.zero_iff_of_isAlgClosed (hg P hP).2.1 u

end IsChowFormCycle

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, d, g, -, rfl, rfl⟩`. Conclude with `⟨by simp, c, hc, by simp⟩`. Introduce and unpack `⟨rfl, c, hc, rfl⟩`. Conclude with `⟨c, hc, 0, 0, by simp, by simp, by simp⟩`.
-/
theorem isChowFormCycle_zero_iff {e dl : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin N) k} :
    IsChowFormCycle 0 e dl f ↔ dl = 0 ∧ ∃ c : k, c ≠ 0 ∧ f = C c := by
  constructor
  · rintro ⟨c, hc, d, g, -, rfl, rfl⟩
    exact ⟨by simp, c, hc, by simp⟩
  · rintro ⟨rfl, c, hc, rfl⟩
    exact ⟨c, hc, 0, 0, by simp, by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using isChowFormCycle_zero_iff.2 ⟨rfl, 1, one_ne_zero, C_1.symm⟩`. Consider the case `succ m ih`. Rewrite using `[succ_nsmul, Nat.succ_mul, pow_succ]`. Conclude with `ih.add h`.
-/
theorem IsChowFormCycle.nsmul {Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowFormCycle Z e dl f) (m : ℕ) :
    IsChowFormCycle (m • Z) e (m * dl) (f ^ m) := by
  induction m with
  | zero => simpa using isChowFormCycle_zero_iff.2 ⟨rfl, 1, one_ne_zero, C_1.symm⟩
  | succ m ih =>
    rw [succ_nsmul, Nat.succ_mul, pow_succ]
    exact ih.add h

/- English proof (translation)
Use `⟨fun h => ?_, fun h => h.2.2.single h.1 h.2.1⟩` and prove the remaining obligations. Take `⟨h1, h2, d, g, h3⟩` from `h.component (P := P) (by simp)`. Take `⟨rfl, c, hc, rfl⟩` from `(h3.single h1 h2).unique h`. Conclude with `⟨h1, h2, h3.C_mul hc⟩`.
-/
theorem isChowFormCycle_single_iff {P : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} :
    IsChowFormCycle (Finsupp.single P 1) e dl f ↔
      P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧ IsChowFormInt P e dl f := by
  refine ⟨fun h => ?_, fun h => h.2.2.single h.1 h.2.1⟩
  obtain ⟨h1, h2, d, g, h3⟩ := h.component (P := P) (by simp)
  obtain ⟨rfl, c, hc, rfl⟩ := (h3.single h1 h2).unique h
  exact ⟨h1, h2, h3.C_mul hc⟩

/- English proof (translation)
Rewrite using `[← MulEquiv.irreducible_iff (finSuccEquiv ℚ 1)]`. Establish `h1 : finSuccEquiv ℚ 1 (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2)`. Use `finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)` as an intermediate fact. Rewrite using `[map_add, map_pow, map_pow, finSuccEquiv_X_zero, map_pow, ← this]`. Both sides reduce to the same expression.

Establish `hm : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).Monic` using `Polynomial.monic_X_pow_add_C _ two_ne_zero`. Establish `hd : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).natDegree = 2` using `Polynomial.natDegree_X_pow_add_C`. Rewrite using `[h1, hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega), Multiset.eq_zero_iff_forall_notMem]`. Introduce `r hr`. Establish `h2` using `congrArg (MvPolynomial.eval fun _ => (1 : ℚ)) (Polynomial.isRoot_of_mem_roots hr).eq_zero`.

Simplify using `at h2`. Use polynomial arithmetic with `[sq_nonneg (MvPolynomial.eval (fun _ => (1 : ℚ)) r)]`.
-/
theorem irreducible_sq_add_sq :
    Irreducible (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv ℚ 1)]
  have h1 : finSuccEquiv ℚ 1 (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2) := by
    have := finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)
    rw [map_add, map_pow, map_pow, finSuccEquiv_X_zero, map_pow, ← this]
    rfl
  have hm : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hd : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).natDegree = 2 :=
    Polynomial.natDegree_X_pow_add_C
  rw [h1, hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  have h2 := congrArg (MvPolynomial.eval fun _ => (1 : ℚ)) (Polynomial.isRoot_of_mem_roots hr).eq_zero
  simp at h2
  nlinarith [sq_nonneg (MvPolynomial.eval (fun _ => (1 : ℚ)) r)]

/- English proof (translation)
The claim follows from `(Ideal.span_singleton_prime irreducible_sq_add_sq.ne_zero).2 irreducible_sq_add_sq.prime`.
-/
theorem isPrime_span_sq_add_sq :
    (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}).IsPrime :=
  (Ideal.span_singleton_prime irreducible_sq_add_sq.ne_zero).2 irreducible_sq_add_sq.prime

/- English proof (translation)
Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `⟨2, (isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)⟩`.
-/
theorem isHomogeneous_span_sq_add_sq :
    (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) ℚ) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ rfl
  exact ⟨2, (isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)⟩

/- English proof (translation)
Use `⟨?_, ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[isMultiHomogeneous_iff_block]`. Establish `hX : ∀ j : Fin 2, IsWeightedHomogeneous GlobalTheory.Chow.blockWeight (X (0, j) ^ 2 : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) (fun _ => 2)`. Introduce `j`. Use `(isWeightedHomogeneous_X ℚ GlobalTheory.Chow.blockWeight ((0 : Fin (0 + 1)), j)).pow 2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `b`. Use `fin_cases b`. Simplify using `[GlobalTheory.Chow.blockWeight]`. Conclude with `(hX 0).add (hX 1)`. Use `(MulEquiv.irreducible_iff (renameEquiv ℚ (Equiv.uniqueProd (Fin 2) (Fin 1)).symm)).2 irreducible_sq_add_sq` as an intermediate fact.

Simplify using `using this`. Simplify using `only [map_add, map_pow, aeval_X]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hu : u (0, 0) = 0`.

Establish `h1 : u (0, 1) = 0` using `by simpa [hu] using h`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos`. Use `⟨![1, z], by simp, fun g hg => ?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hg`. Simplify using `[hz]`.

Use `fin_cases i`. Simplify using `[Fin.sum_univ_two, hu, h1]`. Use `⟨![u (0, 1), -u (0, 0)], by simp [hu], fun g hg => ?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hg`. Rewrite `h` using `[add_comm]`.

Simplify using `[h]`. Use `fin_cases i`. Simplify using `[Fin.sum_univ_two, mul_comm]`. Introduce and unpack `⟨y, hy, hI, hu⟩`. Establish `h1 : y 0 ^ 2 + y 1 ^ 2 = 0` using `by simpa using hI _ (Ideal.subset_span rfl)`.

Establish `h0 : y 0 ≠ 0`. Introduce `h0`. Establish `: y 1 = 0` using `by simpa [h0] using h1`. Apply the tactic sequence `exact hy (funext fun j => by fin_cases j <;> simp [h0, this])`. Establish `h2` using `hu 0`.

Rewrite `h2` using `[Fin.sum_univ_two]`. Use `(mul_eq_zero.1 ?_).resolve_right (pow_ne_zero 2 h0)` and prove the remaining obligations. Take the linear combination `u (0, 1) ^ 2 * h1 + (u (0, 0) * y 0 - u (0, 1) * y 1) * h2`.
-/
theorem isChowFormInt_sq_add_sq :
    IsChowFormInt (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 2
      (X (0, 0) ^ 2 + X (0, 1) ^ 2) := by
  refine ⟨?_, ?_, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block]
    have hX : ∀ j : Fin 2, IsWeightedHomogeneous GlobalTheory.Chow.blockWeight
        (X (0, j) ^ 2 : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) (fun _ => 2) := by
      intro j
      convert (isWeightedHomogeneous_X ℚ GlobalTheory.Chow.blockWeight ((0 : Fin (0 + 1)), j)).pow 2 using 1
      funext b
      fin_cases b
      simp [GlobalTheory.Chow.blockWeight]
    exact (hX 0).add (hX 1)
  · have := (MulEquiv.irreducible_iff
      (renameEquiv ℚ (Equiv.uniqueProd (Fin 2) (Fin 1)).symm)).2 irreducible_sq_add_sq
    simpa using this
  · simp only [map_add, map_pow, aeval_X]
    constructor
    · intro h
      by_cases hu : u (0, 0) = 0
      · have h1 : u (0, 1) = 0 := by simpa [hu] using h
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos
        refine ⟨![1, z], by simp, fun g hg => ?_, fun i => ?_⟩
        · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
          simp [hz]
        · fin_cases i
          simp [Fin.sum_univ_two, hu, h1]
      · refine ⟨![u (0, 1), -u (0, 0)], by simp [hu], fun g hg => ?_, fun i => ?_⟩
        · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
          rw [add_comm] at h
          simp [h]
        · fin_cases i
          simp [Fin.sum_univ_two, mul_comm]
    · rintro ⟨y, hy, hI, hu⟩
      have h1 : y 0 ^ 2 + y 1 ^ 2 = 0 := by simpa using hI _ (Ideal.subset_span rfl)
      have h0 : y 0 ≠ 0 := by
        intro h0
        have : y 1 = 0 := by simpa [h0] using h1
        exact hy (funext fun j => by fin_cases j <;> simp [h0, this])
      have h2 := hu 0
      rw [Fin.sum_univ_two] at h2
      refine (mul_eq_zero.1 ?_).resolve_right (pow_ne_zero 2 h0)
      linear_combination u (0, 1) ^ 2 * h1 + (u (0, 0) * y 0 - u (0, 1) * y 1) * h2

/- English proof (translation)
Introduce `h`. Take `⟨-, c, hc, rfl⟩` from `isChowFormInt_sq_add_sq.unique h.isChowFormInt`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos`. Establish `hz' : (C z : MvPolynomial (Fin (0 + 1) × Fin 2) (AlgebraicClosure ℚ)) ^ 2 = -1`. Rewrite using `[← map_pow, hz, map_neg, map_one]`.

Take `⟨φ, hi⟩ : ∃ φ : ℚ →+* AlgebraicClosure ℚ, Irreducible (MvPolynomial.map φ (C c * (X (0, 0) ^ 2 + X (0, 1) ^ 2) : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ))` from `⟨_, h.irred⟩`. Use `hi.isUnit_or_isUnit (a := C (φ c) * (X (0, 0) + C z * X (0, 1))) (b := X (0, 0) - C z * X (0, 1)) (by` as an intermediate fact. Simplify using `only [map_mul, map_C, map_add, map_pow, map_X]`. Take the linear combination `(C (φ c) * X (0, 1) ^ 2) * hz')`. Apply the tactic sequence `rcases this with h1 | h1 <;> simpa using h1.map constantCoeff`.
-/
theorem not_isChowForm_sq_add_sq (δ : ℕ) (f : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) :
    ¬ IsChowForm (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 δ f := by
  intro h
  obtain ⟨-, c, hc, rfl⟩ := isChowFormInt_sq_add_sq.unique h.isChowFormInt
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos
  have hz' : (C z : MvPolynomial (Fin (0 + 1) × Fin 2) (AlgebraicClosure ℚ)) ^ 2 = -1 := by
    rw [← map_pow, hz, map_neg, map_one]
  obtain ⟨φ, hi⟩ : ∃ φ : ℚ →+* AlgebraicClosure ℚ, Irreducible (MvPolynomial.map φ
      (C c * (X (0, 0) ^ 2 + X (0, 1) ^ 2) : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ)) := ⟨_, h.irred⟩
  have := hi.isUnit_or_isUnit
    (a := C (φ c) * (X (0, 0) + C z * X (0, 1))) (b := X (0, 0) - C z * X (0, 1)) (by
      simp only [map_mul, map_C, map_add, map_pow, map_X]
      linear_combination (C (φ c) * X (0, 1) ^ 2) * hz')
  rcases this with h1 | h1 <;> simpa using h1.map constantCoeff

/- English proof (translation)
Simplify using `using (isChowFormInt_sq_add_sq.single isPrime_span_sq_add_sq isHomogeneous_span_sq_add_sq).nsmul 2`.
-/
theorem isChowFormCycle_two_sq_add_sq :
    IsChowFormCycle
      (Finsupp.single (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 2) 0 4
      ((X (0, 0) ^ 2 + X (0, 1) ^ 2) ^ 2) := by
  simpa using (isChowFormInt_sq_add_sq.single isPrime_span_sq_add_sq
    isHomogeneous_span_sq_add_sq).nsmul 2

/- English proof (translation)
Introduce `h` and use `absurd (h.unique isChowFormInt_sq_add_sq).1 (by norm_num)`.
-/
example (f : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) :
    ¬ IsChowFormInt (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 1 f :=
  fun h => absurd (h.unique isChowFormInt_sq_add_sq).1 (by norm_num)

/- English proof (translation)
Introduce `h` and use `not_isChowFormInt_top f (isChowFormCycle_single_iff.1 h).2.2`.
-/
example (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) :
    ¬ IsChowFormCycle (Finsupp.single (⊤ : Ideal (MvPolynomial (Fin N) k)) 1) e dl f :=
  fun h => not_isChowFormInt_top f (isChowFormCycle_single_iff.1 h).2.2

end GlobalTheory.ChowHt
