import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

open Polynomial

namespace GlobalTheory.LocalFiniteOddFixed

/- English proof (translation)
Rewrite using `[← AdicCompletion.of_surjective_iff]`. Introduce `z`. Take `⟨t, rfl⟩` from `AdicCompletion.ofTensorProduct_surjective_of_finite I M z`. Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul r x`. Take `⟨a, rfl⟩` from `AdicCompletion.of_surjective I O r`. Use `⟨a • x, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.ofTensorProduct_tmul, map_smul]`. Use extensionality with `n`.

Both sides reduce to the same expression. Consider the case `add a b ha hb`. Take `⟨x, hx⟩` from `ha`. Take `⟨y, hy⟩` from `hb`. Conclude with `⟨x + y, by rw [map_add, map_add, hx, hy]⟩`.
-/
theorem precomplete_of_finite (O : Type) [CommRing O] (I : Ideal O) [IsPrecomplete I O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro z
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M z
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    ext n
    rfl
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩

/- English proof (translation)
Establish `key : ∀ i j : ℕ, i < j → x ^ i = x ^ j → ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n`. Introduce `i j hij h`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Establish `h1 : ∀ k : ℕ, x ^ (i + k * (d + 1)) = x ^ i`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `: i + (k + 1) * (d + 1) = (i + d + 1) + k * (d + 1)` using `by ring`. Rewrite using `[this, pow_add, ← h, ← pow_add, ih]`.

Use `⟨(i + 1) * (d + 1), by positivity, ?_⟩` and prove the remaining obligations. Establish `e1 : (i + 1) * (d + 1) = i + (i * d + d + 1)` using `by ring`. Establish `e2 : (i + 1) * (d + 1) + (i + 1) * (d + 1) = (i + (i + 1) * (d + 1)) + (i * d + d + 1)` using `by ring`. Rewrite using `[← pow_add, e2, pow_add, h1, ← pow_add, ← e1]`. Take `⟨i, j, hne, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)`.

Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Conclude with `key i j hlt h`. Conclude with `key j i hlt h.symm`.
-/
theorem exists_pow_idem (M : Type) [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
  have key : ∀ i j : ℕ, i < j → x ^ i = x ^ j → ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
    intro i j hij h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : ∀ k : ℕ, x ^ (i + k * (d + 1)) = x ^ i := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : i + (k + 1) * (d + 1) = (i + d + 1) + k * (d + 1) := by ring
        rw [this, pow_add, ← h, ← pow_add, ih]
    refine ⟨(i + 1) * (d + 1), by positivity, ?_⟩
    have e1 : (i + 1) * (d + 1) = i + (i * d + d + 1) := by ring
    have e2 : (i + 1) * (d + 1) + (i + 1) * (d + 1)
        = (i + (i + 1) * (d + 1)) + (i * d + d + 1) := by ring
    rw [← pow_add, e2, pow_add, h1, ← pow_add, ← e1]
  obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm

/- English proof (translation)
Use `set J : Ideal R := (IsLocalRing.maximalIdeal O).map (algebraMap O R) with hJ`. Use `haveI : IsPrecomplete (IsLocalRing.maximalIdeal O) R := precomplete_of_finite O _ R`. Use `haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) R := {}`. Use `haveI : IsAdicComplete J R := (IsAdicComplete.map_algebraMap_iff _ R).2 inferInstance`. Use `haveI hH : HenselianRing R J := IsAdicComplete.henselianRing R J`.

Use `haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›`. Use `haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (R ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _`. Use `haveI : Finite (R ⧸ J) := Module.finite_of_finite (O ⧸ IsLocalRing.maximalIdeal O)`. Establish `hjac : ∀ y ∈ J, IsUnit (1 + y)`. Introduce `y hy`.

Use `Ideal.mem_jacobson_bot.1 (hH.jac hy) 1` as an intermediate fact. Simplify `this` using `[add_comm]`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Take `⟨n, hn, h⟩` from `exists_pow_idem (R ⧸ J) (Ideal.Quotient.mk J x)`. Establish `hm : (X ^ 2 - X : R[X]).Monic` using `by monicity!`.

Take `⟨e, he, hex⟩` from `hH.is_henselian (X ^ 2 - X) hm (x ^ n) (by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `only [eval_sub, eval_pow, eval_X, map_sub, map_pow]`. Rewrite using `[sq, h, sub_self])`. Use the proof step `(by`.

Establish `: Ideal.Quotient.mk J (eval (x ^ n) (derivative (X ^ 2 - X : R[X]))) = 2 * (Ideal.Quotient.mk J x) ^ n - 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `IsUnit.of_mul_eq_one (2 * (Ideal.Quotient.mk J x) ^ n - 1) ?_` and prove the remaining obligations.

Take the linear combination `4 * h)`. Establish `he' : e * (e - 1) = 0`. Establish `: e ^ 2 - e = 0` using `by simpa using he`. Take the linear combination `this`. Break down `mul_eq_zero.1 he' with h0 | h1` into its components or cases.

Use `right`. Rewrite `hex` using `[h0, zero_sub]`. Establish `hu` using `hjac _ hex`. Rewrite `hu` using `[← sub_eq_add_neg, ← mul_neg_geom_sum]`. Conclude with `isUnit_of_mul_isUnit_left hu`.

Use `left`. Establish `h1' : e = 1` using `sub_eq_zero.1 h1`. Rewrite `hex` using `[h1']`. Establish `hu` using `hjac _ (J.neg_mem hex)`. Establish `: 1 + -(1 - x ^ n) = x ^ n` using `by ring`.

Rewrite `hu` using `[this]`. Conclude with `(isUnit_pow_iff hn.ne').1 hu`.
-/
theorem isLocalRing_of_finite (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Module.Finite O R] : IsLocalRing R := by
  set J : Ideal R := (IsLocalRing.maximalIdeal O).map (algebraMap O R) with hJ
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal O) R := precomplete_of_finite O _ R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) R := {}
  haveI : IsAdicComplete J R := (IsAdicComplete.map_algebraMap_iff _ R).2 inferInstance
  haveI hH : HenselianRing R J := IsAdicComplete.henselianRing R J
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Module.Finite (O ⧸ IsLocalRing.maximalIdeal O) (R ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (R ⧸ J) := Module.finite_of_finite (O ⧸ IsLocalRing.maximalIdeal O)
  have hjac : ∀ y ∈ J, IsUnit (1 + y) := by
    intro y hy
    have := Ideal.mem_jacobson_bot.1 (hH.jac hy) 1
    simpa [add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, hn, h⟩ := exists_pow_idem (R ⧸ J) (Ideal.Quotient.mk J x)
  have hm : (X ^ 2 - X : R[X]).Monic := by monicity!
  obtain ⟨e, he, hex⟩ := hH.is_henselian (X ^ 2 - X) hm (x ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow]
      rw [sq, h, sub_self])
    (by
      have : Ideal.Quotient.mk J (eval (x ^ n) (derivative (X ^ 2 - X : R[X])))
          = 2 * (Ideal.Quotient.mk J x) ^ n - 1 := by
        simp
        ring
      rw [this]
      refine IsUnit.of_mul_eq_one (2 * (Ideal.Quotient.mk J x) ^ n - 1) ?_
      linear_combination 4 * h)
  have he' : e * (e - 1) = 0 := by
    have : e ^ 2 - e = 0 := by simpa using he
    linear_combination this
  rcases mul_eq_zero.1 he' with h0 | h1
  · right
    rw [h0, zero_sub] at hex
    have hu := hjac _ hex
    rw [← sub_eq_add_neg, ← mul_neg_geom_sum] at hu
    exact isUnit_of_mul_isUnit_left hu
  · left
    have h1' : e = 1 := sub_eq_zero.1 h1
    rw [h1'] at hex
    have hu := hjac _ (J.neg_mem hex)
    have : 1 + -(1 - x ^ n) = x ^ n := by ring
    rw [this] at hu
    exact (isUnit_pow_iff hn.ne').1 hu

/- English proof (translation)
Set `F : Subfield k` to `RingHom.eqLocusField τ (RingHom.id k)`. Establish `hF : ∀ x, x ∈ F ↔ τ x = x` using `fun x => Iff.rfl`. Establish `hδ : a - τ a ≠ 0` using `sub_ne_zero.2 hta.symm`. Set `φ : F × F → k` to `fun p => p.1.1 + p.2.1 * a`. Establish `hbij : Function.Bijective φ`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h`. Establish `h1 : u + v * a = u' + v' * a` using `h`. Establish `h2` using `congrArg τ h1`. Rewrite `h2` using `[map_add, map_add, map_mul, map_mul, (hF _).1 hu, (hF _).1 hv, (hF _).1 hu', (hF _).1 hv']`.

Establish `h3 : (v - v') * (a - τ a) = 0` using `by linear_combination h1 - h2`. Establish `h4 : v = v'` using `sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hδ)`. Substitute `h4` using the available equality. Establish `h5 : u = u'` using `add_right_cancel h1`. Substitute `h5` using the available equality.

Both sides reduce to the same expression. Introduce `x`. Establish `hδ' : τ a - a ≠ 0` using `sub_ne_zero.2 hta`. Establish `hv : τ ((x - τ x) / (a - τ a)) = (x - τ x) / (a - τ a)`. Rewrite using `[map_div₀, map_sub, map_sub, hτ, hτ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hu : τ (x - (x - τ x) / (a - τ a) * a) = x - (x - τ x) / (a - τ a) * a`. Rewrite using `[map_sub, map_mul, hv]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨(⟨_, (hF _).2 hu⟩, ⟨_, (hF _).2 hv⟩), by simp [φ]⟩`. Establish `hcard : Nat.card F = q ^ f`. Establish `h1` using `Nat.card_eq_of_bijective φ hbij`. Rewrite `h1` using `[Nat.card_prod, hc, ← sq, ← pow_mul, mul_comm, pow_mul]`.

Conclude with `Nat.pow_left_injective two_ne_zero h1`. Assume the negation of the conclusion as `hodd`. Take `⟨g, hg⟩` from `Nat.not_odd_iff_even.1 hodd`. Establish `hpow : ∀ m : ℕ, a ^ ((q ^ 2) ^ m) = a`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, pow_mul, ih, ha]`. Establish `has : a ^ (q ^ f) = a`. Establish `: q ^ f = (q ^ 2) ^ g` using `by rw [hg, ← pow_mul, two_mul]`.

Rewrite using `[this, hpow]`. Use `haveI : Fintype k := Fintype.ofFinite k`. Use `haveI : Fintype F := Fintype.ofFinite F`. Establish `hcF : Fintype.card F = q ^ f` using `by rw [← hcard, Nat.card_eq_fintype_card]`. Establish `h1s : 1 < q ^ f` using `by rw [← hcF]; exact Fintype.one_lt_card`.

Establish `haF : a ∉ (F : Set k).toFinset`. Rewrite using `[Set.mem_toFinset]`. Conclude with `fun h => hta ((hF a).1 h)`. Use `FiniteField.X_pow_card_sub_X_ne_zero k h1s ?_` and prove the remaining obligations. Use `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (insert a (F : Set k).toFinset) ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Simplify using `[has]`. Rewrite `hx` using `[Set.mem_toFinset]`. Use `congrArg Subtype.val (FiniteField.pow_card (⟨x, hx⟩ : F))` as an intermediate fact.

Rewrite `this` using `[hcF]`. Simplify using `only [eval_sub, eval_pow, eval_X]`. Conclude with `sub_eq_zero.2 this`. Rewrite using `[FiniteField.X_pow_card_sub_X_natDegree_eq k h1s, Finset.card_insert_of_notMem haF, Set.toFinset_card]`. Establish `: Fintype.card (F : Set k) = q ^ f`.

Rewrite using `[← hcard, Nat.card_eq_fintype_card]`. Conclude with `Fintype.card_congr (Equiv.refl _)`. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_of_involution (k : Type) [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x)
    (q f : ℕ) (hc : Nat.card k = (q ^ 2) ^ f) (a : k) (ha : a ^ (q ^ 2) = a) (hta : τ a ≠ a) :
    Odd f := by
  classical
  let F : Subfield k := RingHom.eqLocusField τ (RingHom.id k)
  have hF : ∀ x, x ∈ F ↔ τ x = x := fun x => Iff.rfl
  have hδ : a - τ a ≠ 0 := sub_ne_zero.2 hta.symm
  let φ : F × F → k := fun p => p.1.1 + p.2.1 * a
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      have h1 : u + v * a = u' + v' * a := h
      have h2 := congrArg τ h1
      rw [map_add, map_add, map_mul, map_mul, (hF _).1 hu, (hF _).1 hv, (hF _).1 hu',
        (hF _).1 hv'] at h2
      have h3 : (v - v') * (a - τ a) = 0 := by linear_combination h1 - h2
      have h4 : v = v' := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hδ)
      subst h4
      have h5 : u = u' := add_right_cancel h1
      subst h5
      rfl
    · intro x
      have hδ' : τ a - a ≠ 0 := sub_ne_zero.2 hta
      have hv : τ ((x - τ x) / (a - τ a)) = (x - τ x) / (a - τ a) := by
        rw [map_div₀, map_sub, map_sub, hτ, hτ]
        field_simp
        ring
      have hu : τ (x - (x - τ x) / (a - τ a) * a) = x - (x - τ x) / (a - τ a) * a := by
        rw [map_sub, map_mul, hv]
        field_simp
        ring
      exact ⟨(⟨_, (hF _).2 hu⟩, ⟨_, (hF _).2 hv⟩), by simp [φ]⟩
  have hcard : Nat.card F = q ^ f := by
    have h1 := Nat.card_eq_of_bijective φ hbij
    rw [Nat.card_prod, hc, ← sq, ← pow_mul, mul_comm, pow_mul] at h1
    exact Nat.pow_left_injective two_ne_zero h1
  by_contra hodd
  obtain ⟨g, hg⟩ := Nat.not_odd_iff_even.1 hodd
  have hpow : ∀ m : ℕ, a ^ ((q ^ 2) ^ m) = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, ha]
  have has : a ^ (q ^ f) = a := by
    have : q ^ f = (q ^ 2) ^ g := by rw [hg, ← pow_mul, two_mul]
    rw [this, hpow]
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype F := Fintype.ofFinite F
  have hcF : Fintype.card F = q ^ f := by rw [← hcard, Nat.card_eq_fintype_card]
  have h1s : 1 < q ^ f := by rw [← hcF]; exact Fintype.one_lt_card
  have haF : a ∉ (F : Set k).toFinset := by
    rw [Set.mem_toFinset]; exact fun h => hta ((hF a).1 h)
  refine FiniteField.X_pow_card_sub_X_ne_zero k h1s ?_
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (insert a (F : Set k).toFinset) ?_ ?_
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simp [has]
    · rw [Set.mem_toFinset] at hx
      have := congrArg Subtype.val (FiniteField.pow_card (⟨x, hx⟩ : F))
      rw [hcF] at this
      simp only [eval_sub, eval_pow, eval_X]
      exact sub_eq_zero.2 this
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq k h1s, Finset.card_insert_of_notMem haF,
      Set.toFinset_card]
    have : Fintype.card (F : Set k) = q ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card]; exact Fintype.card_congr (Equiv.refl _)
    omega

open GlobalTheory.UnitLemma

/- English proof (translation)
Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {p}` using `hp.maximalIdeal_eq`. Rewrite `h` using `[hm, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]`. Take `⟨u, hu⟩` from `h.symm`. Establish `h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation p = WithZero.exp (-1)` using `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hp.ne_zero hm`.

Establish `h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `fun hmem => (IsLocalRing.mem_maximalIdeal _).1 hmem u.isUnit`. Establish `h3` using `(IsDiscreteValuationRing.maximalIdeal O).valuation_of_algebraMap (K := E) x`. Unfold `val`.

Rewrite using `[h3, ← hu, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]`. Simplify using the standard rewrite rules.
-/
theorem val_of_span_eq (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type}
    [Field E] [Algebra O E] [IsFractionRing O E] (x : O) (n : ℕ)
    (h : Ideal.span {x} = IsLocalRing.maximalIdeal O ^ n) : val O (algebraMap O E x) = n := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h.symm
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation p = WithZero.exp (-1) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hp.ne_zero hm
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hmem => (IsLocalRing.mem_maximalIdeal _).1 hmem u.isUnit
  have h3 := (IsDiscreteValuationRing.maximalIdeal O).valuation_of_algebraMap (K := E) x
  unfold val
  rw [h3, ← hu, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

/- English proof (translation)
Use `choose c hc using K.c_int`. Establish `inj` using `IsFractionRing.injective K.O K.E`. Use `⟨⟨⟨⟨c, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, fun x => (hc x).symm⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Simplify using the standard rewrite rules.

Simplify using `only [map_mul, ← hc]`. Simplify using `only [← hc]`. Simplify using the standard rewrite rules. Simplify using `only [map_add, ← hc]`.
-/
theorem exists_conj_int (K : UQ) :
    ∃ c : K.O →+* K.O, ∀ x, algebraMap K.O K.E (c x) = K.c (algebraMap K.O K.E x) := by
  choose c hc using K.c_int
  have inj := IsFractionRing.injective K.O K.E
  refine ⟨⟨⟨⟨c, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, fun x => (hc x).symm⟩
  · rw [← hc]; simp
  · simp only [map_mul, ← hc]
  · simp only [← hc]; simp
  · simp only [map_add, ← hc]

/- English proof (translation)
Take `⟨c, hcO⟩` from `exists_conj_int K`. Establish `hτO : ∀ x : K.O, τ (algebraMap K.O L x) = algebraMap K.O L (c x)`. Introduce `x`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E L, hc, ← hcO, ← IsScalarTower.algebraMap_apply]`. Set `R` to `integralClosure K.O L`.

Use `haveI : Module.Finite K.O R := IsIntegralClosure.finite K.O K.E L R`. Use `haveI : IsDedekindDomain R := IsIntegralClosure.isDedekindDomain K.O K.E L R`. Use `haveI : IsLocalRing R := isLocalRing_of_finite K.O R`. Establish `injL : Function.Injective (algebraMap K.O L)`. Rewrite using `[IsScalarTower.algebraMap_eq K.O K.E L]`.

Conclude with `(algebraMap K.E L).injective.comp (IsFractionRing.injective K.O K.E)`. Establish `injR : Function.Injective (algebraMap K.O R)`. Introduce `x y h`. Apply `injL` to reduce the goal to its premises. Rewrite using `[IsScalarTower.algebraMap_apply K.O R L, h, ← IsScalarTower.algebraMap_apply]`.

Use `haveI : FaithfulSMul K.O R := (faithfulSMul_iff_algebraMap_injective _ _).2 injR`. Use `haveI : Module.IsTorsionFree K.O R := inferInstance`. Establish `hnf : ¬ IsField R` using `fun h => IsDiscreteValuationRing.not_isField K.O ((Algebra.IsIntegral.isField_iff_isField injR).2 h)`. Use `haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 2 0).1 ‹IsDedekindDomain R›`. Establish `hint : ∀ x : R, τ (x : L) ∈ R`.

Introduce `x`. Conclude with `IsIntegral.map_of_comp_eq c τ (by ext z; simp [hτO]) x.2`. Set `t : R →+* R` to `RingHom.codRestrict (τ.comp (algebraMap R L)) R hint`. Establish `ht : ∀ x : R, ((t x : R) : L) = τ x` using `fun x => rfl`. Establish `htt : ∀ x, t (t x) = x` using `fun x => Subtype.ext (by rw [ht, ht, hτ])`.

Establish `htO : ∀ x : K.O, t (algebraMap K.O R x) = algebraMap K.O R (c x)` using `fun x => Subtype.ext (hτO x)`. Use `haveI : IsLocalHom t := ⟨fun x hx => by simpa [htt] using hx.map t⟩`. Use `haveI : IsLocalHom (algebraMap K.O R) := inferInstance`. Take `⟨a, b, hab, hnm⟩` from `K.c_res`. Establish `hb : c a = b` using `IsFractionRing.injective K.O K.E (by rw [hcO, hab])`.

Establish `hδ : algebraMap K.O R a - t (algebraMap K.O R a) ∉ IsLocalRing.maximalIdeal R`. Rewrite using `[htO, hb, ← map_sub]`. Introduce `h`. Apply `(IsLocalRing.mem_maximalIdeal _).1 h` to reduce the goal to its premises. Conclude with `(IsLocalRing.notMem_maximalIdeal.1 hnm).map _`.

Establish `hunif : ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p}`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hm : IsLocalRing.maximalIdeal R = Ideal.span {p}` using `hp.maximalIdeal_eq`. Establish `hpm : t p ∈ Ideal.span {p}`. Rewrite using `[← hm]`.

Conclude with `map_nonunit t p ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit)`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 hpm`. Establish `key : ∀ s : R, s + t s * u ∉ IsLocalRing.maximalIdeal R → ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p}`. Introduce `s hs`. Use `⟨s * p + t (s * p), by rw [map_add, htt, add_comm], ?_⟩` and prove the remaining obligations.

Establish `: s * p + t (s * p) = (s + t s * u) * p` using `by rw [map_mul, ← hu]; ring`. Rewrite using `[this, hm, Ideal.span_singleton_mul_left_unit (IsLocalRing.notMem_maximalIdeal.1 hs)]`. Distinguish the cases in `h1 : 1 + t 1 * u ∈ IsLocalRing.maximalIdeal R`. Use `key (algebraMap K.O R a) fun h2 => hδ ?_` and prove the remaining obligations. Rewrite `h1` using `[map_one, one_mul]`.

Use `Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ (t (algebraMap K.O R a)) h1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `key 1 h1`. Take `⟨p, htp, hm⟩` from `hunif`.

Establish `hp0 : p ≠ 0`. Introduce and unpack `rfl`. Conclude with `IsDiscreteValuationRing.not_a_field R (by rw [hm]; simp)`. Use `haveI : (IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal K.O) := inferInstance`. Use `haveI : CharZero K.O := RingHom.charZero (algebraMap K.O K.E)`.

Use `haveI : PerfectField (FractionRing K.O) := inferInstance`. Use `set f := (IsLocalRing.maximalIdeal R).inertiaDeg K.O with hf`. Establish `hN : Ideal.span {Algebra.intNorm K.O R p} = IsLocalRing.maximalIdeal K.O ^ f`. Rewrite using `[← Ideal.relNorm_singleton, ← hm]`. Conclude with `Ideal.relNorm_eq_pow_of_isMaximal _ _`.

Establish `hval : val K.O (Algebra.norm K.E (p : L)) = f`. Use `Algebra.algebraMap_intNorm (A := K.O) (K := K.E) (L := L) (B := R) p` as an intermediate fact. Rewrite using `[← val_of_span_eq (E := K.E) K.O _ f hN, this]`. Both sides reduce to the same expression. Establish `hf' : f = Module.finrank (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R)`.

Rewrite using `[hf, Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal K.O)]`. Both sides reduce to the same expression. Use `haveI : Module.Finite (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R) := inferInstance`. Use `haveI : Finite (IsLocalRing.ResidueField R) := Module.finite_of_finite (IsLocalRing.ResidueField K.O)`. Establish `hcard : Nat.card (IsLocalRing.ResidueField R) = (K.q ^ 2) ^ f`.

Rewrite using `[hf', ← K.card_res]`. Conclude with `Module.natCard_eq_pow_finrank`. Establish `hodd : Odd f`. Use `odd_of_involution (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField.map t) ?_ K.q f hcard (IsLocalRing.residue R (algebraMap K.O R a)) ?_ ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective x`. Rewrite using `[IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, htt]`. Use `haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)`. Establish `h1` using `FiniteField.pow_card (IsLocalRing.residue K.O a)`. Rewrite `h1` using `[← Nat.card_eq_fintype_card, K.card_res]`.

Rewrite using `[← IsLocalRing.ResidueField.map_residue (algebraMap K.O R), ← map_pow, h1]`. Rewrite using `[IsLocalRing.ResidueField.map_residue]`. Introduce `h`. Apply `hδ` to reduce the goal to its premises. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]`.

Use `⟨p, fun h => hp0 (Subtype.ext h), by rw [← ht, htp], ?_⟩` and prove the remaining obligations. Unfold `UQ.eta`. Rewrite using `[hval, zpow_natCast, hodd.neg_one_pow]`.
-/
theorem exists_fixed_odd (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L]
    [IsScalarTower K.O K.E L] [Module.Finite K.E L] (τ : L →+* L) (hτ : ∀ x, τ (τ x) = x)
    (hc : ∀ e : K.E, τ (algebraMap K.E L e) = algebraMap K.E L (K.c e)) :
    ∃ y : L, y ≠ 0 ∧ τ y = y ∧ K.eta (Algebra.norm K.E y) = -1 := by
  obtain ⟨c, hcO⟩ := exists_conj_int K
  have hτO : ∀ x : K.O, τ (algebraMap K.O L x) = algebraMap K.O L (c x) := by
    intro x
    rw [IsScalarTower.algebraMap_apply K.O K.E L, hc, ← hcO, ← IsScalarTower.algebraMap_apply]
  let R := integralClosure K.O L
  haveI : Module.Finite K.O R := IsIntegralClosure.finite K.O K.E L R
  haveI : IsDedekindDomain R := IsIntegralClosure.isDedekindDomain K.O K.E L R
  haveI : IsLocalRing R := isLocalRing_of_finite K.O R
  have injL : Function.Injective (algebraMap K.O L) := by
    rw [IsScalarTower.algebraMap_eq K.O K.E L]
    exact (algebraMap K.E L).injective.comp (IsFractionRing.injective K.O K.E)
  have injR : Function.Injective (algebraMap K.O R) := by
    intro x y h
    apply injL
    rw [IsScalarTower.algebraMap_apply K.O R L, h, ← IsScalarTower.algebraMap_apply]
  haveI : FaithfulSMul K.O R := (faithfulSMul_iff_algebraMap_injective _ _).2 injR
  haveI : Module.IsTorsionFree K.O R := inferInstance
  have hnf : ¬ IsField R := fun h =>
    IsDiscreteValuationRing.not_isField K.O
      ((Algebra.IsIntegral.isField_iff_isField injR).2 h)
  haveI : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 2 0).1 ‹IsDedekindDomain R›
  have hint : ∀ x : R, τ (x : L) ∈ R := by
    intro x
    exact IsIntegral.map_of_comp_eq c τ (by ext z; simp [hτO]) x.2
  let t : R →+* R := RingHom.codRestrict (τ.comp (algebraMap R L)) R hint
  have ht : ∀ x : R, ((t x : R) : L) = τ x := fun x => rfl
  have htt : ∀ x, t (t x) = x := fun x => Subtype.ext (by rw [ht, ht, hτ])
  have htO : ∀ x : K.O, t (algebraMap K.O R x) = algebraMap K.O R (c x) :=
    fun x => Subtype.ext (hτO x)
  haveI : IsLocalHom t := ⟨fun x hx => by simpa [htt] using hx.map t⟩
  haveI : IsLocalHom (algebraMap K.O R) := inferInstance
  obtain ⟨a, b, hab, hnm⟩ := K.c_res
  have hb : c a = b := IsFractionRing.injective K.O K.E (by rw [hcO, hab])
  have hδ : algebraMap K.O R a - t (algebraMap K.O R a) ∉ IsLocalRing.maximalIdeal R := by
    rw [htO, hb, ← map_sub]
    intro h
    apply (IsLocalRing.mem_maximalIdeal _).1 h
    exact (IsLocalRing.notMem_maximalIdeal.1 hnm).map _

  have hunif : ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p} := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} := hp.maximalIdeal_eq
    have hpm : t p ∈ Ideal.span {p} := by
      rw [← hm]
      exact map_nonunit t p ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hpm
    have key : ∀ s : R, s + t s * u ∉ IsLocalRing.maximalIdeal R →
        ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p} := by
      intro s hs
      refine ⟨s * p + t (s * p), by rw [map_add, htt, add_comm], ?_⟩
      have : s * p + t (s * p) = (s + t s * u) * p := by rw [map_mul, ← hu]; ring
      rw [this, hm, Ideal.span_singleton_mul_left_unit (IsLocalRing.notMem_maximalIdeal.1 hs)]
    by_cases h1 : 1 + t 1 * u ∈ IsLocalRing.maximalIdeal R
    · refine key (algebraMap K.O R a) fun h2 => hδ ?_
      rw [map_one, one_mul] at h1
      have := Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ (t (algebraMap K.O R a)) h1)
      convert this using 1
      ring
    · exact key 1 h1
  obtain ⟨p, htp, hm⟩ := hunif
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field R (by rw [hm]; simp)
  haveI : (IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal K.O) := inferInstance
  haveI : CharZero K.O := RingHom.charZero (algebraMap K.O K.E)
  haveI : PerfectField (FractionRing K.O) := inferInstance
  set f := (IsLocalRing.maximalIdeal R).inertiaDeg K.O with hf
  have hN : Ideal.span {Algebra.intNorm K.O R p} = IsLocalRing.maximalIdeal K.O ^ f := by
    rw [← Ideal.relNorm_singleton, ← hm]
    exact Ideal.relNorm_eq_pow_of_isMaximal _ _
  have hval : val K.O (Algebra.norm K.E (p : L)) = f := by
    have := Algebra.algebraMap_intNorm (A := K.O) (K := K.E) (L := L) (B := R) p
    rw [← val_of_span_eq (E := K.E) K.O _ f hN, this]
    rfl
  have hf' : f = Module.finrank (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R) := by
    rw [hf, Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal K.O)]
    rfl
  haveI : Module.Finite (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R) :=
    inferInstance
  haveI : Finite (IsLocalRing.ResidueField R) :=
    Module.finite_of_finite (IsLocalRing.ResidueField K.O)
  have hcard : Nat.card (IsLocalRing.ResidueField R) = (K.q ^ 2) ^ f := by
    rw [hf', ← K.card_res]
    exact Module.natCard_eq_pow_finrank
  have hodd : Odd f := by
    refine odd_of_involution (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField.map t) ?_
      K.q f hcard (IsLocalRing.residue R (algebraMap K.O R a)) ?_ ?_
    · intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, htt]
    · haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)
      have h1 := FiniteField.pow_card (IsLocalRing.residue K.O a)
      rw [← Nat.card_eq_fintype_card, K.card_res] at h1
      rw [← IsLocalRing.ResidueField.map_residue (algebraMap K.O R), ← map_pow, h1]
    · rw [IsLocalRing.ResidueField.map_residue]
      intro h
      apply hδ
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  refine ⟨p, fun h => hp0 (Subtype.ext h), by rw [← ht, htp], ?_⟩
  unfold UQ.eta
  rw [hval, zpow_natCast, hodd.neg_one_pow]

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]`. Use `congr 1`.
-/
theorem norm_prod' (E A B : Type) [Field E] [CommRing A] [CommRing B] [Algebra E A] [Algebra E B]
    [Module.Finite E A] [Module.Finite E B] (a : A) (b : B) :
    Algebra.norm E ((a, b) : A × B) = Algebra.norm E a * Algebra.norm E b := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

/- English proof (translation)
Establish `hff : f * f = f` using `hf`. Set `I : Ideal B.A` to `Ideal.span {1 - f}`. Establish `hI : ∀ y, y ∈ I ↔ f * y = 0`. Introduce `y`. Rewrite using `[Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Take the linear combination `(-s) * hff`. Introduce `h`. Conclude with `⟨y, by linear_combination -h⟩`.

Use `haveI : I.IsMaximal := by`. Rewrite using `[Ideal.isMaximal_iff]`. Use `⟨by rw [hI]; simpa using hf0, fun J x hIJ hx hxJ => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hfield x (fun h => hx ((hI x).2 h))`. Establish `h1 : 1 - x * z ∈ J` using `hIJ ((hI _).2 (by linear_combination -hz))`.

Use `J.add_mem h1 (J.mul_mem_right z hxJ)` as an intermediate fact. Simplify using `using this`. Use `letI : Field (B.A ⧸ I) := Ideal.Quotient.field I`. Establish `hle : I ≤ I.comap (B.σ : B.A →+* B.A)`. Introduce `y hy`.

Rewrite using `[Ideal.mem_comap, hI]`. Use `congrArg B.σ ((hI y).1 hy)` as an intermediate fact. Rewrite `this` using `[map_mul, hσ, map_zero]`. Conclude with `this`. Set `τ : B.A ⧸ I →+* B.A ⧸ I` to `Ideal.quotientMap I (B.σ : B.A →+* B.A) hle`.

Establish `hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (B.σ x)` using `fun x => rfl`. Take `⟨y, hy0, hyτ, hyN⟩` from `exists_fixed_odd K (B.A ⧸ I) τ (by`. Introduce `x`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hτ, hτ, B.σ_σ])`.

Use the proof step `(by`. Introduce `e`. Express the relevant statement in the definitionally equal form `τ (Ideal.Quotient.mk I (algebraMap K.E B.A e)) = _`. Rewrite using `[hτ, B.σ_alg]`. Use the proof step `rfl)`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hy1 : f * y ≠ 0` using `fun h => hy0 (Ideal.Quotient.eq_zero_iff_mem.2 ((hI y).2 h))`. Take `⟨z, hz⟩` from `hfield y hy1`. Establish `hy2 : f * (B.σ y - y) = 0`. Rewrite using `[← hI, ← Ideal.Quotient.eq, ← hτ]`.

Conclude with `hyτ`. Use `⟨f * y + (1 - f), ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one (f * z + (1 - f)) ?_` and prove the remaining obligations. Take the linear combination `(y * z - y - z + 1) * hff + hz`. Rewrite using `[map_add, map_mul, map_sub, map_one, hσ]`.

Take the linear combination `hy2`. Take the linear combination `(1 - y) * hff`. Set `e` to `AlgEquiv.prodQuotientOfIsIdempotentElem K.E (e := 1 - f) (f := f) hf.one_sub hf (by ring) (by linear_combination -hff)`. Establish `he : e (f * y + (1 - f)) = (Ideal.Quotient.mk I y, 1)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I _ = Ideal.Quotient.mk I y`. Rewrite using `[Ideal.Quotient.eq, hI]`. Take the linear combination `(y - 1) * hff`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {f}) _ = Ideal.Quotient.mk (Ideal.span {f}) 1`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`.

Conclude with `⟨y - 1, by ring⟩`. Rewrite using `[← Algebra.norm_eq_of_algEquiv e, he, norm_prod', map_one, mul_one]`. Conclude with `hyN`.
-/
theorem exists_plus_eta_norm (K : UQ) (B : InvAlg K) (f : B.A) (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) (hfield : ∀ y : B.A, f * y ≠ 0 → ∃ z : B.A, f * y * z = f) (hσ : B.σ f = f) :
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  have hff : f * f = f := hf
  let I : Ideal B.A := Ideal.span {1 - f}
  have hI : ∀ y, y ∈ I ↔ f * y = 0 := by
    intro y
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨s, rfl⟩
      linear_combination (-s) * hff
    · intro h
      exact ⟨y, by linear_combination -h⟩
  haveI : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by rw [hI]; simpa using hf0, fun J x hIJ hx hxJ => ?_⟩
    obtain ⟨z, hz⟩ := hfield x (fun h => hx ((hI x).2 h))
    have h1 : 1 - x * z ∈ J := hIJ ((hI _).2 (by linear_combination -hz))
    have := J.add_mem h1 (J.mul_mem_right z hxJ)
    simpa using this
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  have hle : I ≤ I.comap (B.σ : B.A →+* B.A) := by
    intro y hy
    rw [Ideal.mem_comap, hI]
    have := congrArg B.σ ((hI y).1 hy)
    rw [map_mul, hσ, map_zero] at this
    exact this
  let τ : B.A ⧸ I →+* B.A ⧸ I := Ideal.quotientMap I (B.σ : B.A →+* B.A) hle
  have hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (B.σ x) := fun x => rfl
  obtain ⟨y, hy0, hyτ, hyN⟩ := exists_fixed_odd K (B.A ⧸ I) τ
    (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hτ, hτ, B.σ_σ])
    (by
      intro e
      change τ (Ideal.Quotient.mk I (algebraMap K.E B.A e)) = _
      rw [hτ, B.σ_alg]
      rfl)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy1 : f * y ≠ 0 := fun h => hy0 (Ideal.Quotient.eq_zero_iff_mem.2 ((hI y).2 h))
  obtain ⟨z, hz⟩ := hfield y hy1
  have hy2 : f * (B.σ y - y) = 0 := by
    rw [← hI, ← Ideal.Quotient.eq, ← hτ]
    exact hyτ
  refine ⟨f * y + (1 - f), ⟨?_, ?_⟩, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (f * z + (1 - f)) ?_
    linear_combination (y * z - y - z + 1) * hff + hz
  · rw [map_add, map_mul, map_sub, map_one, hσ]
    linear_combination hy2
  · linear_combination (1 - y) * hff
  · let e := AlgEquiv.prodQuotientOfIsIdempotentElem K.E (e := 1 - f) (f := f) hf.one_sub hf
      (by ring) (by linear_combination -hff)
    have he : e (f * y + (1 - f)) = (Ideal.Quotient.mk I y, 1) := by
      refine Prod.ext ?_ ?_
      · change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I y
        rw [Ideal.Quotient.eq, hI]
        linear_combination (y - 1) * hff
      · change Ideal.Quotient.mk (Ideal.span {f}) _ = Ideal.Quotient.mk (Ideal.span {f}) 1
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
        exact ⟨y - 1, by ring⟩
    rw [← Algebra.norm_eq_of_algEquiv e, he, norm_prod', map_one, mul_one]
    exact hyN

end GlobalTheory.LocalFiniteOddFixed
