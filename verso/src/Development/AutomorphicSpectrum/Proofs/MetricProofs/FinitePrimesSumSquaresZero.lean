import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

namespace GlobalTheory.CompanionTheory.QuadFin

/- English proof (translation)
Establish `hint : IsIntegral ℚ x` using `⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩`. Establish `hy' : y ∈ Algebra.adjoin ℚ {x}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hy`. Use `Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_) (fun u v _ _ hu hv => ?_) hy'` and prove the remaining obligations.

Conclude with `⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩`. Conclude with `⟨r, 0, by simp⟩`. Take `⟨a, b, rfl⟩` from `hu`. Take `⟨a', b', rfl⟩` from `hv`. Conclude with `⟨a + a', b + b', by simp only [map_add]; ring⟩`.

Take `⟨a, b, rfl⟩` from `hu`. Take `⟨a', b', rfl⟩` from `hv`. Use `⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Take the linear combination `(algebraMap ℚ E b * algebraMap ℚ E b') * hx`.
-/
theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add, map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

/- English proof (translation)
Use `haveI := Fact.mk hq`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : (p : ℚ) = 0` using `by rw [h]; ring`. Conclude with `hp.ne_zero (by exact_mod_cast h0)`.

Establish `h1` using `congrArg (padicValRat q) h`. Rewrite `h1` using `[padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b, padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]`. Move the coercions through the operations in `at h1`. Use linear arithmetic over natural numbers and integers. Introduce `hd`.

Conclude with `hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm`.
-/
theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

/- English proof (translation)
Establish `hφ : Function.Injective (algebraMap ℚ E)` using `(algebraMap ℚ E).injective`. Establish `key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]`. Take the linear combination `h - algebraMap ℚ E b ^ 2 * hx`. Establish `hq0 : (0 : ℚ) < q` using `by exact_mod_cast hq.pos`.

Establish `hp0 : (0 : ℚ) < p` using `by exact_mod_cast hp.pos`. Distinguish the cases in `hab : 2 * a * b = 0`. Rewrite `key` using `[hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ]`. Break down `mul_eq_zero.mp hab with h2a | hb` into its components or cases. Establish `ha : a = 0` using `by linarith`.

Substitute `ha` using the available equality. Conclude with `not_sq_eq_of_prime hp hq hpq b (by linear_combination key)`. Substitute `hb` using the available equality. Use polynomial arithmetic with `[sq_nonneg a]`. Establish `hne : algebraMap ℚ E (2 * a * b) ≠ 0` using `(map_ne_zero _).mpr hab`.

Establish `hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b)` using `eq_div_of_mul_eq hne (by linear_combination key)`. Rewrite `hx'` using `[← map_neg, ← map_div₀]`. Rewrite `hx` using `[hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]]`. Establish `h2` using `hφ hx`. Use polynomial arithmetic with `[sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]`.
-/
theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

/- English proof (translation)
Use `haveI : Finite (IntermediateField ℚ E) := (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp ⟨inferInstance, Field.exists_primitive_element ℚ E⟩`. Establish `key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) → IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q`. Introduce `p q hp hq x y hx hy he`. Assume the negation of the conclusion as `hpq`. Establish `hmem : x ∈ IntermediateField.adjoin ℚ {y}`.

Rewrite using `[← he]`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ x`. Take `⟨a, b, hab⟩` from `exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem`. Conclude with `false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)`. Establish `hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} => IntermediateField.adjoin ℚ {Classical.choose p.2.2})`.

Introduce and unpack `⟨p, hp⟩ ⟨q, hq⟩ he`. Conclude with `Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)`. Conclude with `Set.finite_coe_iff.mp (Finite.of_injective _ hinj)`.
-/
theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

/- English proof (translation)
Establish `hfd` using `GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F`. Use `(@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, x, hx⟩`. Establish `hint : IsIntegral ℚ x` using `⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩`. Establish `hmem : x ∈ algebraicClosure ℚ F` using `mem_algebraicClosure_iff'.mpr hint`.

Conclude with `⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩`.
-/
theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

/- English proof (translation)
Use `haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)`. Use `haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)`. Use `haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F`. Use `haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F`. Use `(finite_primes_field F).subset ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨hp, a, b, hb, hab⟩`. Establish `hb' : algebraMap A F b ≠ 0` using `fun h0 => hb (IsFractionRing.injective A F (by rw [h0, map_zero]))`. Use `⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap A F) hab`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, map_zero] at e`.

Rewrite using `[div_pow, div_eq_iff (pow_ne_zero 2 hb')]`. Take the linear combination `e`.
-/
theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add, map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

/- English proof (translation)
Introduce `σ _ A _ _ _ f hf`. Use `haveI : Algebra.FiniteType ℤ A := by`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin σ`. Use `Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩` and prove the remaining obligations. Establish `hcomp : ((MvPolynomial.aeval (R` using `ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by`.

Apply `MvPolynomial.ringHom_ext'` to reduce the goal to its premises. Conclude with `RingHom.ext_int _ _`. Introduce `s`. Simplify using the standard rewrite rules. Introduce `a`.

Take `⟨p, rfl⟩` from `hf a`. Conclude with `⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩`. Conclude with `finite_primes_of_isFractionRing A (FractionRing A)`.
-/
theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
