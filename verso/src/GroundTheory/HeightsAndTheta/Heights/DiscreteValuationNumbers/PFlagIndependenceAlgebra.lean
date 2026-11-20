import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Finiteness

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
  [IsNoetherianRing R]

/- English proof (translation)
Use `((P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing).subset ?_` and prove the remaining obligations. Introduce `W hW`. Assume the negation of the conclusion as `h`. Rewrite `hW` using `[Function.mem_support]`. Unfold `divCycle at hW`.

Rewrite `hW` using `[dif_neg (fun h' => h h'.1)]`. Conclude with `hW rfl`.
-/
theorem divCycle_finite_support (P : Ideal (MRing ι R)) (f : MRing ι R) :
    (Function.support (divCycle P f)).Finite := by
  refine ((P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing).subset ?_
  intro W hW
  by_contra h
  rw [Function.mem_support] at hW
  unfold divCycle at hW
  rw [dif_neg (fun h' => h h'.1)] at hW
  exact hW rfl

/- English proof (translation)
The claim follows from `((divCycle_finite_support P f).union (divCycle_finite_support P g)).subset (Function.support_sub (divCycle P f) (divCycle P g))`.
-/
theorem ratDiv_finite_support (P : Ideal (MRing ι R)) (f g : MRing ι R) :
    (Function.support (ratDiv P f g)).Finite :=
  ((divCycle_finite_support P f).union (divCycle_finite_support P g)).subset
    (Function.support_sub (divCycle P f) (divCycle P g))

end Finiteness

section CycEval

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `cycEval`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `W hW`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `Function.support_mul_subset_left _ _ hW`.
-/
theorem cycEval_eq_sum {Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (n : Ideal (MRing ι R) → ℤ) : cycEval n Z = ∑ W ∈ hZ.toFinset, Z W * n W := by
  unfold cycEval
  apply finsum_eq_sum_of_support_subset
  intro W hW
  rw [Set.Finite.coe_toFinset]
  exact Function.support_mul_subset_left _ _ hW

end CycEval

section ClassNum

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
The claim follows from `Finset.sum_subset hS fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]`.
-/
theorem classNum_eq_sum {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]

/- English proof (translation)
Simplify using `[classNum]`.
-/
theorem classNum_zero_poly {σ : Type*} (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (0 : MvPolynomial σ ℤ) Q W = 0 := by
  simp [classNum]

/- English proof (translation)
Rewrite using `[classNum_eq_sum cls (H₁ + H₂) Q W support_add, classNum_eq_sum cls H₁ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_left, classNum_eq_sum cls H₂ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_right]`. Simplify using `only [coeff_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem classNum_add_poly {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (H₁ + H₂) Q W = classNum cls H₁ Q W + classNum cls H₂ Q W := by
  rw [classNum_eq_sum cls (H₁ + H₂) Q W support_add,
    classNum_eq_sum cls H₁ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_left,
    classNum_eq_sum cls H₂ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_right]
  simp only [coeff_add, add_mul, Finset.sum_add_distrib]

def classNumAddHom {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    MvPolynomial σ ℤ →+ ℤ where
  toFun H := classNum cls H Q W
  map_zero' := classNum_zero_poly cls Q W
  map_add' H₁ H₂ := classNum_add_poly cls H₁ H₂ Q W

/- English proof (translation)
Rewrite using `[classNum_eq_sum cls _ Q W support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]`.
-/
theorem classNum_monomial_eq {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    classNum cls (monomial μ c) Q W = c * vNumL W (classList cls μ ++ Q) := by
  classical
  rw [classNum_eq_sum cls _ Q W support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

omit [DecidableEq K] in
/- English proof (translation)
Unfold `classList`. Use `congr 1`. Rewrite using `[← Finsupp.toMultiset_map μ φ, Multiset.map_map]`.
-/
theorem classList_mapDomain {σ τ : Type*} (cls : τ → K → ℤ) (φ : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (μ.mapDomain φ) = classList (cls ∘ φ) μ := by
  unfold classList
  congr 1
  rw [← Finsupp.toMultiset_map μ φ, Multiset.map_map]

/- English proof (translation)
Proceed by induction on `H using MvPolynomial.induction_on' with`. Consider the case `monomial μ c => rw [rename_monomial, classNum_monomial_eq, classNum_monomial_eq, classList_mapDomain]`. Consider the case `add p q hp hq => rw [map_add, classNum_add_poly, classNum_add_poly, hp, hq]`.
-/
theorem classNum_rename_vars {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] (cls : τ → K → ℤ) (φ : σ → τ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename φ H) Q W = classNum (cls ∘ φ) H Q W := by
  induction H using MvPolynomial.induction_on' with
  | monomial μ c => rw [rename_monomial, classNum_monomial_eq, classNum_monomial_eq, classList_mapDomain]
  | add p q hp hq => rw [map_add, classNum_add_poly, classNum_add_poly, hp, hq]

end ClassNum

section PairNum

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def pairNumHom {n : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin n → K → ℤ) (f g : Fin n → MRing ι O)
    (Q : List (K → ℤ)) : (Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) →+ ℤ where
  toFun Gs := pairNum P x x' f g Gs Q
  map_zero' := by
    unfold pairNum
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [cycEval_eq_sum (ratDiv_finite_support P (f i) (g i))]
    simp [classNum_zero_poly]
  map_add' Gs Hs := by
    unfold pairNum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cycEval_eq_sum (ratDiv_finite_support P (f i) (g i)), Pi.add_apply, classNum_add_poly,
      mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairNumHom_apply {n : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin n → K → ℤ)
    (f g : Fin n → MRing ι O) (Q : List (K → ℤ)) (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    pairNumHom P x x' f g Q Gs = pairNum P x x' f g Gs Q := rfl

def pushExpansion {n n' : ℕ} (σ : Fin n → Fin n') (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    Fin n' → MvPolynomial (Fin n' ⊕ Fin n') ℤ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)

/- English proof (translation)
Establish `hcls : Sum.elim x x' ∘ Sum.map σ σ = Sum.elim (x ∘ σ) (x' ∘ σ)`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `cases s <;> rfl`. Unfold `pairNum pushExpansion`. Establish `h1 : ∀ j, cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim x x') (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W) (ratDiv P (f j) (g j)) = ∑ i ∈ Finset.univ.filter (fun i => σ i = j), cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.e …`.

Introduce `j`. Establish `hsum : ∀ W : Ideal (MRing ι O), classNum (Sum.elim x x') (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W = ∑ i ∈ Finset.univ.filter (fun i => σ i = j), classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W`. Introduce `W`. Use `map_sum (classNumAddHom (Sum.elim x x') Q W) (fun i => rename (Sum.map σ σ) (Gs i)) (Finset.univ.filter (fun i => σ i = j))` as an intermediate fact. Simplify using `only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this`.

Rewrite using `[this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[classNum_rename_vars, hcls]`. Simplify using `only [hsum]`. Rewrite using `[cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hi).2, cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]`. Simplify using `only [h1]`.

Conclude with `Finset.sum_fiberwise Finset.univ σ (fun i => cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W) (ratDiv P (f (σ i)) (g (σ i))))`.
-/
theorem pairNum_pushExpansion {n n' : ℕ} (σ : Fin n → Fin n') (P : Ideal (MRing ι O))
    (x x' : Fin n' → K → ℤ) (f g : Fin n' → MRing ι O)
    (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (pushExpansion σ Gs) Q =
      pairNum P (x ∘ σ) (x' ∘ σ) (f ∘ σ) (g ∘ σ) Gs Q := by
  have hcls : Sum.elim x x' ∘ Sum.map σ σ = Sum.elim (x ∘ σ) (x' ∘ σ) := by
    funext s
    cases s <;> rfl
  unfold pairNum pushExpansion
  have h1 : ∀ j, cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim x x')
        (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W)
        (ratDiv P (f j) (g j)) =
      ∑ i ∈ Finset.univ.filter (fun i => σ i = j),
        cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W)
          (ratDiv P (f (σ i)) (g (σ i))) := by
    intro j
    have hsum : ∀ W : Ideal (MRing ι O), classNum (Sum.elim x x')
        (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W =
        ∑ i ∈ Finset.univ.filter (fun i => σ i = j),
          classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W := by
      intro W
      have := map_sum (classNumAddHom (Sum.elim x x') Q W)
        (fun i => rename (Sum.map σ σ) (Gs i)) (Finset.univ.filter (fun i => σ i = j))
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [classNum_rename_vars, hcls]
    simp only [hsum]
    rw [cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2, cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]
  simp only [h1]
  exact Finset.sum_fiberwise Finset.univ σ
    (fun i => cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W)
      (ratDiv P (f (σ i)) (g (σ i))))

end PairNum

section Expansions

/- English proof (translation)
Use `⟨?_, fun i => (hA.homogeneous i).add (hB.homogeneous i)⟩` and prove the remaining obligations. Simplify using `only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hA.expansion, ← hB.expansion]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPairExpansion_add {n m : ℕ} {A B : MvPolynomial (Fin n) ℤ}
    {As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (hA : IsPairExpansion m A As)
    (hB : IsPairExpansion m B Bs) : IsPairExpansion m (A + B) (As + Bs) := by
  refine ⟨?_, fun i => (hA.homogeneous i).add (hB.homogeneous i)⟩
  simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hA.expansion,
    ← hB.expansion]
  ring

/- English proof (translation)
Use `⟨?_, fun j => IsHomogeneous.sum _ _ _ fun i _ => (h.homogeneous i).rename_isHomogeneous⟩` and prove the remaining obligations. Establish `e1 : rename Sum.inl (rename σ A) = rename (Sum.map σ σ) (rename Sum.inl A)`. Rewrite using `[rename_rename, rename_rename]`. Both sides reduce to the same expression. Establish `e2 : rename Sum.inr (rename σ A) = rename (Sum.map σ σ) (rename Sum.inr A)`.

Rewrite using `[rename_rename, rename_rename]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, ← map_sub, h.expansion, map_sum]`. Simplify using `only [map_mul, map_sub, rename_X, Sum.map_inl, Sum.map_inr, pushExpansion, Finset.mul_sum]`. Use `(Finset.sum_fiberwise Finset.univ σ _).symm.trans ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hi).2]`.
-/
theorem isPairExpansion_push {n n' m : ℕ} (σ : Fin n → Fin n') {A : MvPolynomial (Fin n) ℤ}
    {Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (h : IsPairExpansion m A Gs) :
    IsPairExpansion m (rename σ A) (pushExpansion σ Gs) := by
  refine ⟨?_, fun j => IsHomogeneous.sum _ _ _ fun i _ => (h.homogeneous i).rename_isHomogeneous⟩
  have e1 : rename Sum.inl (rename σ A) = rename (Sum.map σ σ) (rename Sum.inl A) := by
    rw [rename_rename, rename_rename]
    rfl
  have e2 : rename Sum.inr (rename σ A) = rename (Sum.map σ σ) (rename Sum.inr A) := by
    rw [rename_rename, rename_rename]
    rfl
  rw [e1, e2, ← map_sub, h.expansion, map_sum]
  simp only [map_mul, map_sub, rename_X, Sum.map_inl, Sum.map_inr, pushExpansion, Finset.mul_sum]
  refine (Finset.sum_fiberwise Finset.univ σ _).symm.trans ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/- English proof (translation)
Proceed by induction on `A using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, by simp⟩`. Consider the case `add p q hp hq`. Take `⟨Ps, hP⟩` from `hp`. Take `⟨Qs, hQ⟩` from `hq`.

Use `⟨Ps + Qs, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hP, ← hQ]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p j hp`. Take `⟨Ps, hP⟩` from `hp`.

Use `⟨fun i => X (Sum.inl j) * Ps i + if i = j then rename Sum.inr p else 0, ?_⟩` and prove the remaining obligations. Simplify using `only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `: ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * (X (Sum.inl j) * Ps i) = X (Sum.inl j) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Ps i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, ← hP]`. Simplify using `only [map_mul, rename_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_expansion {n : ℕ} (A : MvPolynomial (Fin n) ℤ) :
    ∃ Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
      rename Sum.inl A - rename Sum.inr A = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i := by
  induction A using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p q hp hq =>
    obtain ⟨Ps, hP⟩ := hp
    obtain ⟨Qs, hQ⟩ := hq
    refine ⟨Ps + Qs, ?_⟩
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hP, ← hQ]
    ring
  | mul_X p j hp =>
    obtain ⟨Ps, hP⟩ := hp
    refine ⟨fun i => X (Sum.inl j) * Ps i + if i = j then rename Sum.inr p else 0, ?_⟩
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have : ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * (X (Sum.inl j) * Ps i) =
        X (Sum.inl j) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Ps i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, ← hP]
    simp only [map_mul, rename_X]
    ring

/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent P, Finset.mul_sum, map_sum]`. Establish `h : ∀ j, homogeneousComponent t (L * homogeneousComponent j P) = if j = t - 1 ∧ t ≠ 0 then L * homogeneousComponent j P else 0`. Introduce `j`. Establish `hm` using `hL.mul (homogeneousComponent_isHomogeneous j P)`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hm)]`.

Distinguish the cases in `hjt : j = t - 1 ∧ t ≠ 0`. Rewrite using `[if_pos (by omega), if_pos hjt]`. Rewrite using `[if_neg (by omega), if_neg hjt]`. Simplify using `only [h]`. Distinguish the cases in `ht : t = 0`.

Simplify using `[ht]`. Simplify using `only [ht, ne_eq, not_false_eq_true, and_true, if_false]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hmem`. Both sides reduce to the same expression.

Rewrite using `[homogeneousComponent_eq_zero, mul_zero]`. Rewrite `hmem` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem homogeneousComponent_linear_mul {σ : Type*} {L : MvPolynomial σ ℤ} (hL : L.IsHomogeneous 1)
    (P : MvPolynomial σ ℤ) (t : ℕ) :
    homogeneousComponent t (L * P) = if t = 0 then 0 else L * homogeneousComponent (t - 1) P := by
  conv_lhs => rw [← sum_homogeneousComponent P, Finset.mul_sum, map_sum]
  have h : ∀ j, homogeneousComponent t (L * homogeneousComponent j P) =
      if j = t - 1 ∧ t ≠ 0 then L * homogeneousComponent j P else 0 := by
    intro j
    have hm := hL.mul (homogeneousComponent_isHomogeneous j P)
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hm)]
    by_cases hjt : j = t - 1 ∧ t ≠ 0
    · rw [if_pos (by omega), if_pos hjt]
    · rw [if_neg (by omega), if_neg hjt]
  simp only [h]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ne_eq, not_false_eq_true, and_true, if_false]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      rw [Finset.mem_range] at hmem
      omega

/- English proof (translation)
Take `⟨Gs, hG⟩` from `exists_expansion A`. Establish `hL : ∀ i, (X (Sum.inl i) - X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin n) ℤ).IsHomogeneous 1` using `fun i => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)`. Establish `hD : (rename Sum.inl A - rename Sum.inr A).IsHomogeneous m` using `hA.rename_isHomogeneous.sub hA.rename_isHomogeneous`. Establish `key` using `congrArg (homogeneousComponent m) hG`. Rewrite `key` using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hD), if_pos rfl, map_sum]`.

Simplify using `only [homogeneousComponent_linear_mul (hL _)] at key`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Use `⟨0, ?_, fun i => isHomogeneous_zero _ _ _⟩` and prove the remaining obligations. Simplify using `using key`. Use `⟨fun i => homogeneousComponent (m - 1) (Gs i), ?_, fun i => homogeneousComponent_isHomogeneous _ _⟩` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using `only [hm.ne', if_false]`.
-/
theorem exists_isPairExpansion {n m : ℕ} {A : MvPolynomial (Fin n) ℤ} (hA : A.IsHomogeneous m) :
    ∃ Gs, IsPairExpansion m A Gs := by
  obtain ⟨Gs, hG⟩ := exists_expansion A
  have hL : ∀ i, (X (Sum.inl i) - X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin n) ℤ).IsHomogeneous 1 :=
    fun i => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  have hD : (rename Sum.inl A - rename Sum.inr A).IsHomogeneous m :=
    hA.rename_isHomogeneous.sub hA.rename_isHomogeneous
  have key := congrArg (homogeneousComponent m) hG
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hD), if_pos rfl, map_sum]
    at key
  simp only [homogeneousComponent_linear_mul (hL _)] at key
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, ?_, fun i => isHomogeneous_zero _ _ _⟩
    simpa using key
  · refine ⟨fun i => homogeneousComponent (m - 1) (Gs i), ?_,
      fun i => homogeneousComponent_isHomogeneous _ _⟩
    rw [key]
    simp only [hm.ne', if_false]

end Expansions

end

end GroundTheory.Heights₂.Heights.NumbersDVR
