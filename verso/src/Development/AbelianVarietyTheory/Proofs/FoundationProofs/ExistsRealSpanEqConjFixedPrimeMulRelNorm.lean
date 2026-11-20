import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddOrderAtEvenElsewhere
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.FixedPrimeNorm

open IsDedekindDomain UniqueFactorizationMonoid

/- English proof (translation)
Establish `hss : ∀ J : Ideal R, (J.map s).map s = J` using `fun J => by`. Rewrite using `[← Ideal.map_coe s, ← Ideal.map_coe s, Ideal.map_map]`. Establish `: (s : R →+* R).comp (s : R →+* R) = RingHom.id R` using `RingHom.ext hs`. Rewrite using `[this, Ideal.map_id]`. Proceed by induction on `I using (wellFounded_dvdNotUnit (α := Ideal R)).induction with`.

Consider the case `h I ih`. Introduce `hI hfix hev`. Distinguish the cases in `htop : I = ⊤`. Conclude with `⟨⊤, by simp [htop, Ideal.map_top]⟩`. Take `⟨Q, hQm, hIQ⟩` from `Ideal.exists_le_maximal I htop`.

Establish `hQ0 : Q ≠ ⊥` using `fun h => hI (le_bot_iff.1 (h ▸ hIQ))`. Establish `hQ : Prime Q` using `Ideal.prime_of_isPrime hQ0 hQm.isPrime`. Establish `hQ'0 : Q.map s ≠ ⊥` using `fun h => hQ0 (by rw [← hss Q, h, Ideal.map_bot])`. Establish `hQ' : Prime (Q.map s)` using `Ideal.prime_of_isPrime hQ'0 (by haveI := hQm.isPrime`. Conclude with `Ideal.map_isPrime_of_equiv s)`.

Establish `hd : Q ∣ I` using `Ideal.dvd_iff_le.2 hIQ`. Establish `hd' : Q.map s ∣ I` using `Ideal.dvd_iff_le.2 (hfix ▸ Ideal.map_mono hIQ)`. Establish `hdd : Q * Q.map s ∣ I`. Take `⟨J, rfl⟩` from `hd`. Use `mul_dvd_mul_left _ ?_` and prove the remaining obligations.

Establish `hJ : J ≠ 0` using `right_ne_zero_of_mul hI`. Distinguish the cases in `h : Q.map s = Q`. Use `hev Q hQm.isPrime hQ0 h` as an intermediate fact. Rewrite `this` using `[normalizedFactors_mul hQ0 hJ, normalizedFactors_irreducible hQ.irreducible, normalize_eq, Multiset.count_add, Multiset.count_singleton_self]`. Rewrite using `[h]`.

Apply `dvd_of_mem_normalizedFactors` to reduce the goal to its premises. Rewrite using `[← Multiset.count_ne_zero]`. Introduce `h0`. Rewrite `this` using `[h0]`. Conclude with `absurd this (by decide)`.

Break down `hQ'.dvd_or_dvd hd' with h1 | h1` into its components or cases. Conclude with `absurd (associated_iff_eq.1 ((hQ'.dvd_prime_iff_associated hQ).1 h1)) h`. Conclude with `h1`. Take `⟨J, rfl⟩` from `hdd`. Establish `hJ : J ≠ 0` using `right_ne_zero_of_mul hI`.

Establish `hQQ : Q * Q.map s ≠ 0` using `mul_ne_zero hQ0 hQ'0`. Take `⟨B, hB⟩` from `ih J ⟨hJ, Q * Q.map s, fun h => hQ.not_unit (isUnit_of_mul_isUnit_left h), mul_comm _ _⟩ hJ (by`. Rewrite `hfix` using `[Ideal.map_mul, Ideal.map_mul, hss, mul_comm (Q.map s) Q]`. Conclude with `mul_left_cancel₀ hQQ hfix) (fun P hP hP0 hPf => by`. Use `hev P hP hP0 hPf` as an intermediate fact.

Rewrite `this` using `[normalizedFactors_mul hQQ hJ, normalizedFactors_mul hQ0 hQ'0, normalizedFactors_irreducible hQ.irreducible, normalizedFactors_irreducible hQ'.irreducible, normalize_eq, normalize_eq, Multiset.count_add, Multiset.count_add, Multiset.count_singleton, Multiset.count_singleton]`. Distinguish the cases in `h : P = Q`. Substitute `h` using the available equality. Rewrite `this` using `[if_pos rfl, if_pos hPf.symm]`. Conclude with `(Nat.even_add.1 this).1 (by decide)`.

Rewrite `this` using `[if_neg h, if_neg (fun h' => h (by rw [← hPf, h', hss]))]`. Simplify using `using this)`. Conclude with `⟨Q * B, by rw [Ideal.map_mul, hB]; ring⟩`.
-/
theorem exists_eq_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (s : R ≃+* R)
    (hs : ∀ x, s (s x) = x) (I : Ideal R) : I ≠ ⊥ → I.map s = I →
    (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q.map s = Q → Even ((normalizedFactors I).count Q)) →
    ∃ B : Ideal R, I = B * B.map s := by
  have hss : ∀ J : Ideal R, (J.map s).map s = J := fun J => by
    rw [← Ideal.map_coe s, ← Ideal.map_coe s, Ideal.map_map]
    have : (s : R →+* R).comp (s : R →+* R) = RingHom.id R := RingHom.ext hs
    rw [this, Ideal.map_id]
  induction I using (wellFounded_dvdNotUnit (α := Ideal R)).induction with
  | h I ih =>
  intro hI hfix hev
  by_cases htop : I = ⊤
  · exact ⟨⊤, by simp [htop, Ideal.map_top]⟩
  obtain ⟨Q, hQm, hIQ⟩ := Ideal.exists_le_maximal I htop
  have hQ0 : Q ≠ ⊥ := fun h => hI (le_bot_iff.1 (h ▸ hIQ))
  have hQ : Prime Q := Ideal.prime_of_isPrime hQ0 hQm.isPrime
  have hQ'0 : Q.map s ≠ ⊥ := fun h => hQ0 (by rw [← hss Q, h, Ideal.map_bot])
  have hQ' : Prime (Q.map s) := Ideal.prime_of_isPrime hQ'0 (by
    haveI := hQm.isPrime
    exact Ideal.map_isPrime_of_equiv s)
  have hd : Q ∣ I := Ideal.dvd_iff_le.2 hIQ
  have hd' : Q.map s ∣ I := Ideal.dvd_iff_le.2 (hfix ▸ Ideal.map_mono hIQ)
  have hdd : Q * Q.map s ∣ I := by
    obtain ⟨J, rfl⟩ := hd
    refine mul_dvd_mul_left _ ?_
    have hJ : J ≠ 0 := right_ne_zero_of_mul hI
    by_cases h : Q.map s = Q
    · have := hev Q hQm.isPrime hQ0 h
      rw [normalizedFactors_mul hQ0 hJ, normalizedFactors_irreducible hQ.irreducible,
        normalize_eq, Multiset.count_add, Multiset.count_singleton_self] at this
      rw [h]
      apply dvd_of_mem_normalizedFactors
      rw [← Multiset.count_ne_zero]
      intro h0
      rw [h0] at this
      exact absurd this (by decide)
    · rcases hQ'.dvd_or_dvd hd' with h1 | h1
      · exact absurd (associated_iff_eq.1 ((hQ'.dvd_prime_iff_associated hQ).1 h1)) h
      · exact h1
  obtain ⟨J, rfl⟩ := hdd
  have hJ : J ≠ 0 := right_ne_zero_of_mul hI
  have hQQ : Q * Q.map s ≠ 0 := mul_ne_zero hQ0 hQ'0
  obtain ⟨B, hB⟩ := ih J ⟨hJ, Q * Q.map s, fun h => hQ.not_unit (isUnit_of_mul_isUnit_left h),
    mul_comm _ _⟩ hJ (by
      rw [Ideal.map_mul, Ideal.map_mul, hss, mul_comm (Q.map s) Q] at hfix
      exact mul_left_cancel₀ hQQ hfix) (fun P hP hP0 hPf => by
      have := hev P hP hP0 hPf
      rw [normalizedFactors_mul hQQ hJ, normalizedFactors_mul hQ0 hQ'0,
        normalizedFactors_irreducible hQ.irreducible, normalizedFactors_irreducible hQ'.irreducible,
        normalize_eq, normalize_eq, Multiset.count_add, Multiset.count_add,
        Multiset.count_singleton, Multiset.count_singleton] at this
      by_cases h : P = Q
      · subst h
        rw [if_pos rfl, if_pos hPf.symm] at this
        exact (Nat.even_add.1 this).1 (by decide)
      · rw [if_neg h, if_neg (fun h' => h (by rw [← hPf, h', hss]))] at this
        simpa using this)
  exact ⟨Q * B, by rw [Ideal.map_mul, hB]; ring⟩

/- English proof (translation)
Establish `hp : Prime P` using `Ideal.prime_of_isPrime hP0 hP`. Establish `hd : P ∣ I`. Apply `dvd_of_mem_normalizedFactors` to reduce the goal to its premises. Rewrite using `[← Multiset.count_ne_zero]`. Introduce `h0`.

Rewrite `hodd` using `[h0]`. Conclude with `absurd hodd (by decide)`. Take `⟨J, rfl⟩` from `hd`. Establish `hJ : J ≠ 0` using `right_ne_zero_of_mul hI`. Establish `hc : ∀ Q, (normalizedFactors (P * J)).count Q = (if Q = P then 1 else 0) + (normalizedFactors J).count Q` using `fun Q => by`.

Rewrite using `[normalizedFactors_mul hP0 hJ, normalizedFactors_irreducible hp.irreducible, normalize_eq, Multiset.count_add, Multiset.count_singleton]`. Take `⟨B, hB⟩` from `exists_eq_mul_map s hs J hJ (by`. Rewrite `hfix` using `[Ideal.map_mul, hPf]`. Conclude with `mul_left_cancel₀ hP0 hfix) (fun Q hQ hQ0 hQf => by`. Distinguish the cases in `h : Q = P`.

Substitute `h` using the available equality. Rewrite `hodd` using `[hc, if_pos rfl]`. Conclude with `(Nat.odd_add.1 hodd).1 (by decide)`. Use `hev Q hQ hQ0 hQf h` as an intermediate fact. Rewrite `this` using `[hc, if_neg h]`.

Simplify using `using this)`. Conclude with `⟨B, by rw [hB, mul_assoc]⟩`.
-/
theorem exists_eq_prime_mul_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (s : R ≃+* R)
    (hs : ∀ x, s (s x) = x) (I P : Ideal R) (hI : I ≠ ⊥) (hfix : I.map s = I) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (hPf : P.map s = P) (hodd : Odd ((normalizedFactors I).count P))
    (hev : ∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q.map s = Q → Q ≠ P →
      Even ((normalizedFactors I).count Q)) :
    ∃ B : Ideal R, I = P * B * B.map s := by
  have hp : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hd : P ∣ I := by
    apply dvd_of_mem_normalizedFactors
    rw [← Multiset.count_ne_zero]
    intro h0
    rw [h0] at hodd
    exact absurd hodd (by decide)
  obtain ⟨J, rfl⟩ := hd
  have hJ : J ≠ 0 := right_ne_zero_of_mul hI
  have hc : ∀ Q, (normalizedFactors (P * J)).count Q =
      (if Q = P then 1 else 0) + (normalizedFactors J).count Q := fun Q => by
    rw [normalizedFactors_mul hP0 hJ, normalizedFactors_irreducible hp.irreducible,
        normalize_eq, Multiset.count_add, Multiset.count_singleton]
  obtain ⟨B, hB⟩ := exists_eq_mul_map s hs J hJ (by
    rw [Ideal.map_mul, hPf] at hfix
    exact mul_left_cancel₀ hP0 hfix) (fun Q hQ hQ0 hQf => by
    by_cases h : Q = P
    · subst h
      rw [hc, if_pos rfl] at hodd
      exact (Nat.odd_add.1 hodd).1 (by decide)
    · have := hev Q hQ hQ0 hQf h
      rw [hc, if_neg h] at this
      simpa using this)
  exact ⟨B, by rw [hB, mul_assoc]⟩

/- English proof (translation)
Establish `h1 : w.valuation E (t : E) = w.intValuation t` using `w.valuation_of_algebraMap t`. Rewrite `h` using `[h1, w.intValuation_if_neg ht, WithZero.exp_inj, count_associates_factors_eq (by simpa using ht) w.isPrime w.ne_bot]`. Use linear arithmetic over natural numbers and integers.
-/
theorem count_eq_of_valuation {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (t : 𝓞 E) (ht : t ≠ 0) (m : ℤ) (h : w.valuation E (t : E) = WithZero.exp m) :
    (((normalizedFactors (Ideal.span {t})).count w.asIdeal : ℕ) : ℤ) = -m := by
  have h1 : w.valuation E (t : E) = w.intValuation t := w.valuation_of_algebraMap t
  rw [h1, w.intValuation_if_neg ht, WithZero.exp_inj,
    count_associates_factors_eq (by simpa using ht) w.isPrime w.ne_bot] at h
  omega

section Quad

open GlobalTheory.QNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `hq.span x`. Establish `hθ : θ ≠ 0`. Introduce and unpack `rfl`. Use `hq.sq` as an intermediate fact. Rewrite `this` using `[zero_pow two_ne_zero, eq_comm, map_eq_zero]`.

Conclude with `hq.nonsq (this ▸ IsSquare.zero)`. Rewrite `hx` using `[map_add, map_mul, σ.commutes, σ.commutes, hq.conj]`. Establish `: algebraMap F E b * θ = 0` using `by linear_combination (-1 / 2 : E) * hx`. Conclude with `⟨a, by rw [this, add_zero]⟩`.
-/
theorem fixed_mem_range (hq : IsQuad δ θ σ) (x : E) (hx : σ x = x) : ∃ a : F, algebraMap F E a = x := by
  obtain ⟨a, b, rfl⟩ := hq.span x
  have hθ : θ ≠ 0 := by
    rintro rfl
    have := hq.sq
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at this
    exact hq.nonsq (this ▸ IsSquare.zero)
  rw [map_add, map_mul, σ.commutes, σ.commutes, hq.conj] at hx
  have : algebraMap F E b * θ = 0 := by linear_combination (-1 / 2 : E) * hx
  exact ⟨a, by rw [this, add_zero]⟩

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `hq.span x`. Simplify using `[hq.conj]`.
-/
theorem conj_conj (hq : IsQuad δ θ σ) (x : E) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := hq.span x
  simp [hq.conj]

/- English proof (translation)
Introduce `h`. Establish `hss : ∀ x, s (s x) = x` using `fun x => RingOfIntegers.ext (by show ((s (s x) : 𝓞 E) : E) = x`. Rewrite using `[hs, hs, conj_conj hq])`. Establish `key : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → w' = w`. Introduce `w' hw'`.

Break down `(conj_places_transitive F E δ θ σ hq).2 w w' hw' with h1 | h1` into its components or cases. Conclude with `h1`. Use extensionality with `x`. Rewrite using `[← w'.valuation_lt_one_iff_mem (K := E)]`. Use `erw [h1, ← hs]`.

Use `erw [w.valuation_lt_one_iff_mem (K := E)]`. Prove the components needed by the constructor for the conclusion. Introduce `h2`. Rewrite using `[← hw, ← hss x]`. Conclude with `Ideal.mem_map_of_mem _ h2`.

Introduce `h2`. Rewrite using `[← hw]`. Conclude with `Ideal.mem_map_of_mem _ h2`. Take `⟨w1, w2, hne, h1, h2⟩` from `two_places_of_isSquare F E δ θ σ hq _ h`. Conclude with `hne ((key w1 h1).trans (key w2 h2).symm)`.
-/
theorem not_isSquare_of_fixed (hq : IsQuad δ θ σ) (s : 𝓞 E ≃+* 𝓞 E)
    (hs : ∀ x, ((s x : 𝓞 E) : E) = σ x) (w : HeightOneSpectrum (𝓞 E))
    (hw : w.asIdeal.map s = w.asIdeal) :
    ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) δ) := by
  intro h
  have hss : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by
    show ((s (s x) : 𝓞 E) : E) = x
    rw [hs, hs, conj_conj hq])
  have key : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → w' = w := by
    intro w' hw'
    rcases (conj_places_transitive F E δ θ σ hq).2 w w' hw' with h1 | h1
    · exact h1
    · ext x
      rw [← w'.valuation_lt_one_iff_mem (K := E)]
      erw [h1, ← hs]
      erw [w.valuation_lt_one_iff_mem (K := E)]
      constructor
      · intro h2
        rw [← hw, ← hss x]
        exact Ideal.mem_map_of_mem _ h2
      · intro h2
        rw [← hw]
        exact Ideal.mem_map_of_mem _ h2
  obtain ⟨w1, w2, hne, h1, h2⟩ := two_places_of_isSquare F E δ θ σ hq _ h
  exact hne ((key w1 h1).trans (key w2 h2).symm)

/- English proof (translation)
Take `⟨e, -, he⟩` from `(places_over F E).2.2 w`. Use `⟨e, fun x t m ht hx hm => count_eq_of_valuation w t ht _ ?_⟩` and prove the remaining obligations. Rewrite using `[← hx, he, hm, ← WithZero.exp_nsmul, nsmul_eq_mul]`.
-/
theorem count_eq_mul (w : HeightOneSpectrum (𝓞 E)) : ∃ e : ℕ, ∀ (x : F) (t : 𝓞 E) (m : ℤ),
    t ≠ 0 → algebraMap F E x = t → (w.under (𝓞 F)).valuation F x = WithZero.exp m →
    (((normalizedFactors (Ideal.span {t})).count w.asIdeal : ℕ) : ℤ) = -(e * m) := by
  obtain ⟨e, -, he⟩ := (places_over F E).2.2 w
  refine ⟨e, fun x t m ht hx hm => count_eq_of_valuation w t ht _ ?_⟩
  rw [← hx, he, hm, ← WithZero.exp_nsmul, nsmul_eq_mul]

/- English proof (translation)
Establish `hss : ∀ x, s (s x) = x` using `fun x => RingOfIntegers.ext (by show ((s (s x) : 𝓞 E) : E) = x`. Rewrite using `[hs, hs, conj_conj hq])`. Take `⟨y, hy⟩` from `hu`. Establish `hP : ∀ x ∈ w.asIdeal, s x ∈ w.asIdeal` using `fun x hx => by`. Rewrite using `[← hw]`.

Conclude with `Ideal.mem_map_of_mem _ hx`. Establish `hchar : ∀ t : 𝓞 E, t ∈ w.asIdeal → t ∉ w.asIdeal ^ 2 → w.valuation E (t : E) = WithZero.exp (-1)`. Introduce `t h1 h2`. Establish `h0 : w.valuation E (t : E) = w.intValuation t` using `w.valuation_of_algebraMap t`. Establish `ht : t ≠ 0` using `by rintro rfl; exact h2 (zero_mem _)`.

Rewrite `h1` using `[← pow_one w.asIdeal, ← w.intValuation_le_pow_iff_mem]`. Rewrite `h2` using `[← w.intValuation_le_pow_iff_mem]`. Rewrite using `[h0]`. Rewrite `h1`, `h2`, the goal using `[w.intValuation_if_neg ht]`. Rewrite `h1`, `h2` using `[WithZero.exp_le_exp]`.

Rewrite using `[WithZero.exp_inj]`. Move the coercions through the operations in `at h1 h2`. Use linear arithmetic over natural numbers and integers. Take `⟨π, hπ⟩` from `w.intValuation_exists_uniformizer`. Establish `hπ1 : π ∈ w.asIdeal`.

Rewrite using `[← pow_one w.asIdeal, ← w.intValuation_le_pow_iff_mem, hπ]`. Simplify using the standard rewrite rules. Establish `hπ2 : π ∉ w.asIdeal ^ 2`. Rewrite using `[← w.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]`. Evaluate the numerical expressions.

Distinguish the cases in `h1 : π + s π ∈ w.asIdeal ^ 2`. Use `⟨y * π + s (y * π), by rw [map_add, hss, add_comm], hchar _ (add_mem (Ideal.mul_mem_left _ _ hπ1) (hP _ (Ideal.mul_mem_left _ _ hπ1))) fun h2 => ?_⟩` and prove the remaining obligations. Establish `h3 : (y - s y) * π ∈ w.asIdeal ^ 2`. Establish `: (y - s y) * π = (y * π + s (y * π)) - s y * (π + s π)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `sub_mem h2 (Ideal.mul_mem_left _ _ h1)`. Rewrite `h3` using `[← w.intValuation_le_pow_iff_mem, map_mul, hπ, (w.intValuation_eq_one_iff).2 hy, one_mul, WithZero.exp_le_exp]`. Evaluate the numerical expressions using `at h3`.

Conclude with `⟨π + s π, by rw [map_add, hss, add_comm], hchar _ (add_mem hπ1 (hP _ hπ1)) h1⟩`.
-/
theorem exists_fixed_uniformizer (hq : IsQuad δ θ σ) (s : 𝓞 E ≃+* 𝓞 E)
    (hs : ∀ x, ((s x : 𝓞 E) : E) = σ x) (w : HeightOneSpectrum (𝓞 E))
    (hw : w.asIdeal.map s = w.asIdeal) (hu : ∃ y, y - s y ∉ w.asIdeal) :
    ∃ t : 𝓞 E, s t = t ∧ w.valuation E (t : E) = WithZero.exp (-1) := by
  have hss : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by
    show ((s (s x) : 𝓞 E) : E) = x
    rw [hs, hs, conj_conj hq])
  obtain ⟨y, hy⟩ := hu
  have hP : ∀ x ∈ w.asIdeal, s x ∈ w.asIdeal := fun x hx => by
    rw [← hw]; exact Ideal.mem_map_of_mem _ hx
  have hchar : ∀ t : 𝓞 E, t ∈ w.asIdeal → t ∉ w.asIdeal ^ 2 →
      w.valuation E (t : E) = WithZero.exp (-1) := by
    intro t h1 h2
    have h0 : w.valuation E (t : E) = w.intValuation t := w.valuation_of_algebraMap t
    have ht : t ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
    rw [← pow_one w.asIdeal, ← w.intValuation_le_pow_iff_mem] at h1
    rw [← w.intValuation_le_pow_iff_mem] at h2
    rw [h0]
    rw [w.intValuation_if_neg ht] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    rw [WithZero.exp_inj]
    push_cast at h1 h2
    omega
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπ1 : π ∈ w.asIdeal := by
    rw [← pow_one w.asIdeal, ← w.intValuation_le_pow_iff_mem, hπ]; simp
  have hπ2 : π ∉ w.asIdeal ^ 2 := by
    rw [← w.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]; norm_num
  by_cases h1 : π + s π ∈ w.asIdeal ^ 2
  · refine ⟨y * π + s (y * π), by rw [map_add, hss, add_comm], hchar _
      (add_mem (Ideal.mul_mem_left _ _ hπ1) (hP _ (Ideal.mul_mem_left _ _ hπ1))) fun h2 => ?_⟩
    have h3 : (y - s y) * π ∈ w.asIdeal ^ 2 := by
      have : (y - s y) * π = (y * π + s (y * π)) - s y * (π + s π) := by
        rw [map_mul]; ring
      rw [this]
      exact sub_mem h2 (Ideal.mul_mem_left _ _ h1)
    rw [← w.intValuation_le_pow_iff_mem, map_mul, hπ,
      (w.intValuation_eq_one_iff).2 hy, one_mul, WithZero.exp_le_exp] at h3
    norm_num at h3
  · exact ⟨π + s π, by rw [map_add, hss, add_comm], hchar _ (add_mem hπ1 (hP _ hπ1)) h1⟩

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (𝓞 F) t`. Establish `hb0 : algebraMap (𝓞 F) F b ≠ 0`. Simplify using `using nonZeroDivisors.ne_zero hb`. Establish `e : algebraMap F E (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b ^ 2) = ((algebraMap (𝓞 F) (𝓞 E) (a * b) : 𝓞 E) : E)`. Establish `: algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b ^ 2 = algebraMap (𝓞 F) F (a * b)` using `by rw [map_mul]; field_simp`.

Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨algebraMap _ _ b, algebraMap (𝓞 F) (𝓞 E) (a * b), hb0, fun h => ?_, e, fun v m hm => ?_⟩` and prove the remaining obligations. Rewrite `e` using `[h]`. Simplify using `only [map_zero, RingOfIntegers.coe_eq_algebraMap, map_eq_zero] at e`.

Conclude with `mul_ne_zero ht (pow_ne_zero _ hb0) e`. Establish `h1 : v.valuation F (algebraMap (𝓞 F) F b) ≠ 0` using `by simpa using hb0`. Use `⟨WithZero.log (v.valuation F (algebraMap (𝓞 F) F b)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hm, map_pow, two_mul, WithZero.exp_add, WithZero.exp_add, WithZero.exp_log h1, sq]`.
-/
theorem exists_mul_sq_integral (t : F) (ht : t ≠ 0) : ∃ (b : F) (u : 𝓞 E), b ≠ 0 ∧ u ≠ 0 ∧
    algebraMap F E (t * b ^ 2) = u ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (m : ℤ),
      v.valuation F t = WithZero.exp m → ∃ k : ℤ, v.valuation F (t * b ^ 2) = WithZero.exp (m + 2 * k) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) t
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have e : algebraMap F E (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b ^ 2) =
      ((algebraMap (𝓞 F) (𝓞 E) (a * b) : 𝓞 E) : E) := by
    have : algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b ^ 2 =
      algebraMap (𝓞 F) F (a * b) := by rw [map_mul]; field_simp
    rw [this]; rfl
  refine ⟨algebraMap _ _ b, algebraMap (𝓞 F) (𝓞 E) (a * b), hb0, fun h => ?_, e, fun v m hm => ?_⟩
  · rw [h] at e
    simp only [map_zero, RingOfIntegers.coe_eq_algebraMap, map_eq_zero] at e
    exact mul_ne_zero ht (pow_ne_zero _ hb0) e
  · have h1 : v.valuation F (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
    refine ⟨WithZero.log (v.valuation F (algebraMap (𝓞 F) F b)), ?_⟩
    rw [map_mul, hm, map_pow, two_mul, WithZero.exp_add, WithZero.exp_add, WithZero.exp_log h1, sq]

/- English proof (translation)
Establish `hss : ∀ x, s (s x) = x` using `fun x => RingOfIntegers.ext (by show ((s (s x) : 𝓞 E) : E) = x`. Rewrite using `[hs, hs, conj_conj hq])`. Establish `hδ : δ ≠ 0` using `fun h => hq.nonsq (h ▸ IsSquare.zero)`. Establish `hfixI : ∀ (x : F) (u : 𝓞 E), algebraMap F E x = u → (Ideal.span {u}).map s = Ideal.span {u}` using `fun x u h => by`. Establish `: s u = u` using `RingOfIntegers.ext (by show ((s u : 𝓞 E) : E) = u`.

Rewrite using `[hs, ← h, σ.commutes])`. Rewrite using `[Ideal.map_span, Set.image_singleton, this]`. Establish `heven : ∀ (t b : F) (u : 𝓞 E), u ≠ 0 → algebraMap F E (t * b ^ 2) = u → (∀ (v : HeightOneSpectrum (𝓞 F)) (m : ℤ), v.valuation F t = WithZero.exp m → ∃ k : ℤ, v.valuation F (t * b ^ 2) = WithZero.exp (m + 2 * k)) → ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.map s = w.asIdeal → (IsSq …`. Introduce `t b u hu0 hu hv w hw h`. Take `⟨n, hn⟩` from `h.resolve_left (not_isSquare_of_fixed hq s hs w hw)`.

Take `⟨k, hk⟩` from `hv _ _ hn`. Take `⟨e, he⟩` from `count_eq_mul (F := F) w`. Rewrite using `[← Int.even_coe_nat, he _ u _ hu0 hu hk]`. Conclude with `⟨-(e * (n + k)), by ring⟩`. Set `w₀ : HeightOneSpectrum (𝓞 E)` to `⟨P, hP, hP0⟩`.

Take `⟨t, ht, ⟨n, hn⟩, hrest⟩` from `exists_odd_order_at_even_elsewhere F (Units.mk0 δ hδ) σ₀ hq.nonsq (fun t ht hv hρ => by`. Take `⟨b, u, hb, hu0, hu, hval⟩` from `exists_mul_sq_integral (E := E) t ht`. Take `⟨B, hB⟩` from `exists_eq_mul_map s hss (Ideal.span {u}) (by simpa using hu0) (hfixI _ _ hu) (fun Q hQ hQ0 hQf => heven t b u hu0 hu hval ⟨Q, hQ, hQ0⟩ hQf (hv _))`. Establish `hsq : ∀ ρ : F →+* ℝ, 0 < ρ b ^ 2` using `fun ρ => by`. Establish `: ρ b ≠ 0` using `by simpa using hb`.

Check the signs of the components of the expression. Use `hsign _ u B hu0 hu hB (fun ρ h => by` as an intermediate fact. Rewrite using `[map_mul, map_pow]`. Conclude with `mul_pos (hρ ρ h) (hsq ρ))`. Rewrite `this` using `[map_mul, map_pow]`.

Conclude with `(mul_pos_iff_of_pos_right (hsq σ₀)).1 this) (w₀.under (𝓞 F))`. Take `⟨b, u, hb, hu0, hu', hval⟩` from `exists_mul_sq_integral (E := E) t ht`. Take `⟨B, hB⟩` from `exists_eq_prime_mul_mul_map s hss (Ideal.span {u}) P (by simpa using hu0) (hfixI _ _ hu') hP hP0 hPf (by`. Take `⟨k, hk⟩` from `hval _ _ hn`. Take `⟨e, he⟩` from `count_eq_mul (F := F) w₀`.

Take `⟨π, hπ, hπv⟩` from `exists_fixed_uniformizer hq s hs w₀ hPf hu`. Take `⟨x, hx⟩` from `fixed_mem_range hq π (by rw [← hs, hπ])`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [map_zero, RingOfIntegers.coe_eq_algebraMap] at hπv`.

Conclude with `WithZero.exp_ne_zero hπv.symm`. Establish `hx0 : (w₀.under (𝓞 F)).valuation F x ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Introduce and unpack `rfl`. Rewrite `hx` using `[map_zero]`.

Conclude with `hπ0 (by simpa using hx.symm)`. Establish `h1` using `he x π _ hπ0 hx (WithZero.exp_log hx0).symm`. Rewrite `h1` using `[count_eq_of_valuation w₀ π hπ0 _ hπv]`. Establish `hodd : Odd (e : ℤ)`. Establish `h3 : Odd ((e : ℤ) * WithZero.log ((w₀.under (𝓞 F)).valuation F x))` using `⟨-1, by linarith⟩`.

Conclude with `(Int.odd_mul.1 h3).1`. Establish `h2` using `he _ u _ hu0 hu' hk`. Rewrite using `[← Int.odd_coe_nat]`. Use `erw [h2]`. Conclude with `(hodd.mul ⟨n + k, by ring⟩).neg)`.

Use the proof step `(fun Q hQ hQ0 hQf hne => heven t b u hu0 hu' hval ⟨Q, hQ, hQ0⟩ hQf (by`. Distinguish the cases in `h : (⟨Q, hQ, hQ0⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = w₀.under (𝓞 F)`. It suffices to derive a contradiction. Break down `(conj_places_transitive F E δ θ σ hq).2 w₀ _ h with h1 | h1` into its components or cases. Conclude with `hne (congrArg HeightOneSpectrum.asIdeal h1)`.

Apply `hne` to reduce the goal to its premises. Use extensionality with `x`. Establish `a1` using `(⟨Q, hQ, hQ0⟩ : HeightOneSpectrum (𝓞 E)).valuation_lt_one_iff_mem (K := E) x`. Establish `a2` using `w₀.valuation_lt_one_iff_mem (K := E) (s x)`. Use `erw [h1, ← hs, a2] at a1`.

Use `a1.symm.trans ⟨fun h2 => ?_, fun h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[← hPf, ← hss x]`. Conclude with `Ideal.mem_map_of_mem _ h2`. Use `show s x ∈ P`. Rewrite using `[← hPf]`.

Conclude with `Ideal.mem_map_of_mem _ h2`. Conclude with `hrest _ h))`. Conclude with `⟨u, B, hu0, by rw [← hu', σ.commutes], hB⟩`.
-/
theorem exists_span_eq (hq : IsQuad δ θ σ) (s : 𝓞 E ≃+* 𝓞 E)
    (hs : ∀ x, ((s x : 𝓞 E) : E) = σ x) (σ₀ : F →+* ℝ)
    (hsign : ∀ (x : F) (t : 𝓞 E) (B : Ideal (𝓞 E)), t ≠ 0 → algebraMap F E x = t →
      Ideal.span {t} = B * B.map s → (∀ ρ : F →+* ℝ, ρ ≠ σ₀ → 0 < ρ x) → 0 < σ₀ x)
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPf : P.map s = P)
    (hu : ∃ y, y - s y ∉ P) :
    ∃ (t : 𝓞 E) (B : Ideal (𝓞 E)), t ≠ 0 ∧ σ t = t ∧ Ideal.span {t} = P * B * B.map s := by
  have hss : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by
    show ((s (s x) : 𝓞 E) : E) = x
    rw [hs, hs, conj_conj hq])
  have hδ : δ ≠ 0 := fun h => hq.nonsq (h ▸ IsSquare.zero)
  have hfixI : ∀ (x : F) (u : 𝓞 E), algebraMap F E x = u →
      (Ideal.span {u}).map s = Ideal.span {u} := fun x u h => by
    have : s u = u := RingOfIntegers.ext (by
      show ((s u : 𝓞 E) : E) = u
      rw [hs, ← h, σ.commutes])
    rw [Ideal.map_span, Set.image_singleton, this]
  have heven : ∀ (t b : F) (u : 𝓞 E), u ≠ 0 → algebraMap F E (t * b ^ 2) = u →
      (∀ (v : HeightOneSpectrum (𝓞 F)) (m : ℤ), v.valuation F t = WithZero.exp m →
        ∃ k : ℤ, v.valuation F (t * b ^ 2) = WithZero.exp (m + 2 * k)) →
      ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.map s = w.asIdeal →
      (IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) δ) ∨
        ∃ n : ℤ, (w.under (𝓞 F)).valuation F t = WithZero.exp (2 * n)) →
      Even ((normalizedFactors (Ideal.span {u})).count w.asIdeal) := by
    intro t b u hu0 hu hv w hw h
    obtain ⟨n, hn⟩ := h.resolve_left (not_isSquare_of_fixed hq s hs w hw)
    obtain ⟨k, hk⟩ := hv _ _ hn
    obtain ⟨e, he⟩ := count_eq_mul (F := F) w
    rw [← Int.even_coe_nat, he _ u _ hu0 hu hk]
    exact ⟨-(e * (n + k)), by ring⟩
  let w₀ : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hP0⟩
  obtain ⟨t, ht, ⟨n, hn⟩, hrest⟩ := exists_odd_order_at_even_elsewhere F (Units.mk0 δ hδ) σ₀
    hq.nonsq (fun t ht hv hρ => by
      obtain ⟨b, u, hb, hu0, hu, hval⟩ := exists_mul_sq_integral (E := E) t ht
      obtain ⟨B, hB⟩ := exists_eq_mul_map s hss (Ideal.span {u}) (by simpa using hu0)
        (hfixI _ _ hu) (fun Q hQ hQ0 hQf => heven t b u hu0 hu hval ⟨Q, hQ, hQ0⟩ hQf (hv _))
      have hsq : ∀ ρ : F →+* ℝ, 0 < ρ b ^ 2 := fun ρ => by
        have : ρ b ≠ 0 := by simpa using hb
        positivity
      have := hsign _ u B hu0 hu hB (fun ρ h => by
        rw [map_mul, map_pow]; exact mul_pos (hρ ρ h) (hsq ρ))
      rw [map_mul, map_pow] at this
      exact (mul_pos_iff_of_pos_right (hsq σ₀)).1 this) (w₀.under (𝓞 F))
  obtain ⟨b, u, hb, hu0, hu', hval⟩ := exists_mul_sq_integral (E := E) t ht
  obtain ⟨B, hB⟩ := exists_eq_prime_mul_mul_map s hss (Ideal.span {u}) P (by simpa using hu0)
    (hfixI _ _ hu') hP hP0 hPf (by
      obtain ⟨k, hk⟩ := hval _ _ hn
      obtain ⟨e, he⟩ := count_eq_mul (F := F) w₀
      obtain ⟨π, hπ, hπv⟩ := exists_fixed_uniformizer hq s hs w₀ hPf hu
      obtain ⟨x, hx⟩ := fixed_mem_range hq π (by rw [← hs, hπ])
      have hπ0 : π ≠ 0 := by
        rintro rfl
        simp only [map_zero, RingOfIntegers.coe_eq_algebraMap] at hπv
        exact WithZero.exp_ne_zero hπv.symm
      have hx0 : (w₀.under (𝓞 F)).valuation F x ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        rintro rfl
        rw [map_zero] at hx
        exact hπ0 (by simpa using hx.symm)
      have h1 := he x π _ hπ0 hx (WithZero.exp_log hx0).symm
      rw [count_eq_of_valuation w₀ π hπ0 _ hπv] at h1
      have hodd : Odd (e : ℤ) := by
        have h3 : Odd ((e : ℤ) * WithZero.log ((w₀.under (𝓞 F)).valuation F x)) := ⟨-1, by linarith⟩
        exact (Int.odd_mul.1 h3).1
      have h2 := he _ u _ hu0 hu' hk
      rw [← Int.odd_coe_nat]
      erw [h2]
      exact (hodd.mul ⟨n + k, by ring⟩).neg)
    (fun Q hQ hQ0 hQf hne => heven t b u hu0 hu' hval ⟨Q, hQ, hQ0⟩ hQf (by
      by_cases h : (⟨Q, hQ, hQ0⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = w₀.under (𝓞 F)
      · exfalso
        rcases (conj_places_transitive F E δ θ σ hq).2 w₀ _ h with h1 | h1
        · exact hne (congrArg HeightOneSpectrum.asIdeal h1)
        · apply hne
          ext x
          have a1 := (⟨Q, hQ, hQ0⟩ : HeightOneSpectrum (𝓞 E)).valuation_lt_one_iff_mem (K := E) x
          have a2 := w₀.valuation_lt_one_iff_mem (K := E) (s x)
          erw [h1, ← hs, a2] at a1
          refine a1.symm.trans ⟨fun h2 => ?_, fun h2 => ?_⟩
          · rw [← hPf, ← hss x]
            exact Ideal.mem_map_of_mem _ h2
          · show s x ∈ P
            rw [← hPf]
            exact Ideal.mem_map_of_mem _ h2
      · exact hrest _ h))
  exact ⟨u, B, hu0, by rw [← hu', σ.commutes], hB⟩

end Quad

/- English proof (translation)
Introduce `D P hP hP0 hPf`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x` using `fun x => by`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`.

Conclude with `(D.host.toHostAx.conjE_apply _ _).symm`. Set `s` to `Formalism.L2.Pj.barE D`. Establish `hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E x` using `fun _ => rfl`. Establish `hsm : ∀ I : Ideal (𝓞 D.host.E), D.host.conj • I = I.map s` using `fun I => by`. Rewrite using `[Ideal.pointwise_smul_def, ← Ideal.map_coe s]`.

Use `congr 1`. Conclude with `RingHom.ext fun x => RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D x).symm`. Establish `hd : (0 : ℝ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`. Establish `hθsq` using `D.host.sqrtMinusD_sq`. Establish `hθc` using `Formalism.L2.Pj.cc_sqrtMinusD D`.

Establish `hθ0 : D.host.sqrtMinusD ≠ 0`. Introduce `h`. Rewrite `hθsq` using `[h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero]`. Conclude with `D.host.hyp.2.1.ne_zero hθsq`. Establish `hq : GlobalTheory.QNorm.IsQuad (-(D.host.d : maximalRealSubfield D.host.E)) D.host.sqrtMinusD (IsCMField.complexConj D.host.E)`.

Use `⟨?_, by rw [hθsq]; simp, hθc, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨r, hr⟩`. Establish `h1 : D.host.sqrtMinusD ^ 2 = (r : D.host.E) ^ 2`. Use `congrArg (fun y : maximalRealSubfield D.host.E => (y : D.host.E)) hr` as an intermediate fact. Rewrite using `[hθsq, sq]`.

Simplify using `using this`. Establish `h2` using `(IsCMField.complexConj_eq_self_iff D.host.E r).2 r.2`. Apply `hθ0` to reduce the goal to its premises. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. Rewrite `hθc` using `[h, h2]`.

Rewrite using `[h]`. Take the linear combination `(1 / 2 : D.host.E) * hθc`. Rewrite `hθc` using `[h, map_neg, h2]`. Rewrite using `[h]`. Take the linear combination `(1 / 2 : D.host.E) * hθc`.

Use `⟨⟨(x + IsCMField.complexConj D.host.E x) / 2, (IsCMField.complexConj_eq_self_iff D.host.E _).1 ?_⟩, ⟨(x - IsCMField.complexConj D.host.E x) / (2 * D.host.sqrtMinusD), (IsCMField.complexConj_eq_self_iff D.host.E _).1 ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]`. Rewrite using `[map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hθc]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `show x = (x + IsCMField.complexConj D.host.E x) / 2 + (x - IsCMField.complexConj D.host.E x) / (2 * D.host.sqrtMinusD) * D.host.sqrtMinusD`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hreal : ∀ τ : D.what₂.Tau, ComplexEmbedding.IsReal ((embT D τ).comp (algebraMap (maximalRealSubfield D.host.E) D.host.E))` using `fun τ => by`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `x.2 (embT D τ)`. Set `r : D.what₂.Tau → (maximalRealSubfield D.host.E →+* ℝ)` to `fun τ => (hreal τ).embedding`. Establish `hr : ∀ τ x, ((r τ x : ℝ) : ℂ) = embT D τ (algebraMap _ D.host.E x)` using `fun τ x => (hreal τ).coe_embedding_apply x`.

Establish `hinj : Function.Injective r` using `fun τ τ' h => by`. Establish `hE` using `factEmb D.R D.host`. Establish `h1 : embT D τ D.host.sqrtMinusD = _` using `(hE.2 _).2 (D.eTau τ).2`. Establish `h2 : embT D τ' D.host.sqrtMinusD = _` using `(hE.2 _).2 (D.eTau τ').2`. Establish `h3 : embT D τ = embT D τ'`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `hq.span x`. Rewrite using `[map_add, map_add, map_mul, map_mul, ← hr, ← hr, ← hr, ← hr, h, h1, h2]`. Conclude with `D.eTau.injective (Subtype.ext (hE.1.1 h3))`. Take `⟨τ₀⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm ⟨1, by simp [Formalism.HC.Frame.Psi]⟩⟩`.

Take `⟨t, B, ht, htf, hB⟩` from `exists_span_eq hq s hs (r τ₀) (fun x t B ht hx hB hρ => by`. Establish `h1` using `GlobalTheory.NormSign.norm_pos D t B ht (by rw [← hcc, ← hx, AlgEquiv.commutes]) (by rw [hsm, hB])`. Rewrite `h1` using `[← hx]`. Simplify using `only [← hr] at h1`. Rewrite `h1` using `[← Complex.ofReal_prod, Complex.ofReal_re, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)]`.

Conclude with `(mul_pos_iff_of_pos_right (Finset.prod_pos fun τ hτ => hρ _ fun h => Finset.ne_of_mem_erase hτ (hinj h))).1 h1)`. Use `P hP hP0 (by rw [← hsm, hPf]) (Formalism.L2.Pj.cmUnram_conj D P (hP.isMaximal hP0))`. Conclude with `⟨t, B, ht, by rw [← hcc, htf], by rw [hsm, hB]⟩`.
-/
theorem exists_span_eq_prime_mul_norm : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsPrime → P ≠ ⊥ → D.host.conj • P = P → ∃ (t : 𝓞 D.host.E) (B : Ideal (𝓞 D.host.E)), t ≠ 0 ∧ D.host.conj (t : D.host.E) = t ∧ Ideal.span {t} = P * B * (D.host.conj • B) := by
  intro D P hP hP0 hPf
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply _ _).symm
  let s := Formalism.L2.Pj.barE D
  have hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hsm : ∀ I : Ideal (𝓞 D.host.E), D.host.conj • I = I.map s := fun I => by
    rw [Ideal.pointwise_smul_def, ← Ideal.map_coe s]
    congr 1
    exact RingHom.ext fun x => RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D x).symm
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hθsq := D.host.sqrtMinusD_sq
  have hθc := Formalism.L2.Pj.cc_sqrtMinusD D
  have hθ0 : D.host.sqrtMinusD ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at hθsq
    exact D.host.hyp.2.1.ne_zero hθsq
  have hq : GlobalTheory.QNorm.IsQuad (-(D.host.d : maximalRealSubfield D.host.E)) D.host.sqrtMinusD
      (IsCMField.complexConj D.host.E) := by
    refine ⟨?_, by rw [hθsq]; simp, hθc, fun x => ?_⟩
    · rintro ⟨r, hr⟩
      have h1 : D.host.sqrtMinusD ^ 2 = (r : D.host.E) ^ 2 := by
        have := congrArg (fun y : maximalRealSubfield D.host.E => (y : D.host.E)) hr
        rw [hθsq, sq]
        simpa using this
      have h2 := (IsCMField.complexConj_eq_self_iff D.host.E r).2 r.2
      apply hθ0
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
      · rw [h, h2] at hθc
        rw [h]; linear_combination (1 / 2 : D.host.E) * hθc
      · rw [h, map_neg, h2] at hθc
        rw [h]; linear_combination (1 / 2 : D.host.E) * hθc
    · refine ⟨⟨(x + IsCMField.complexConj D.host.E x) / 2,
        (IsCMField.complexConj_eq_self_iff D.host.E _).1 ?_⟩,
        ⟨(x - IsCMField.complexConj D.host.E x) / (2 * D.host.sqrtMinusD),
        (IsCMField.complexConj_eq_self_iff D.host.E _).1 ?_⟩, ?_⟩
      · rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hθc]
        field_simp
        ring
      · show x = (x + IsCMField.complexConj D.host.E x) / 2 +
          (x - IsCMField.complexConj D.host.E x) / (2 * D.host.sqrtMinusD) * D.host.sqrtMinusD
        field_simp
        ring
  have hreal : ∀ τ : D.what₂.Tau, ComplexEmbedding.IsReal
      ((embT D τ).comp (algebraMap (maximalRealSubfield D.host.E) D.host.E)) := fun τ => by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact x.2 (embT D τ)
  let r : D.what₂.Tau → (maximalRealSubfield D.host.E →+* ℝ) := fun τ => (hreal τ).embedding
  have hr : ∀ τ x, ((r τ x : ℝ) : ℂ) = embT D τ (algebraMap _ D.host.E x) := fun τ x =>
    (hreal τ).coe_embedding_apply x
  have hinj : Function.Injective r := fun τ τ' h => by
    have hE := factEmb D.R D.host
    have h1 : embT D τ D.host.sqrtMinusD = _ := (hE.2 _).2 (D.eTau τ).2
    have h2 : embT D τ' D.host.sqrtMinusD = _ := (hE.2 _).2 (D.eTau τ').2
    have h3 : embT D τ = embT D τ' := by
      refine RingHom.ext fun x => ?_
      obtain ⟨a, b, rfl⟩ := hq.span x
      rw [map_add, map_add, map_mul, map_mul, ← hr, ← hr, ← hr, ← hr, h, h1, h2]
    exact D.eTau.injective (Subtype.ext (hE.1.1 h3))
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.HC.Frame.Psi]⟩⟩
  obtain ⟨t, B, ht, htf, hB⟩ := exists_span_eq hq s hs (r τ₀) (fun x t B ht hx hB hρ => by
      have h1 := GlobalTheory.NormSign.norm_pos D t B ht (by rw [← hcc, ← hx, AlgEquiv.commutes]) (by rw [hsm, hB])
      rw [← hx] at h1
      simp only [← hr] at h1
      rw [← Complex.ofReal_prod, Complex.ofReal_re,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)] at h1
      exact (mul_pos_iff_of_pos_right (Finset.prod_pos fun τ hτ =>
        hρ _ fun h => Finset.ne_of_mem_erase hτ (hinj h))).1 h1)
    P hP hP0 (by rw [← hsm, hPf]) (Formalism.L2.Pj.cmUnram_conj D P (hP.isMaximal hP0))
  exact ⟨t, B, ht, by rw [← hcc, htf], by rw [hsm, hB]⟩

end GlobalTheory.FixedPrimeNorm
