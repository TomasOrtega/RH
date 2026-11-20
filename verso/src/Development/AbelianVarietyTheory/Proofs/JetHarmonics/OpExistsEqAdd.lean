import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LieMatrixCoordinates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscriminantGramUnit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open NumberField

namespace GlobalTheory.AvChartCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def IsPrimeUnder (w : Place p R) (P : Ideal R) : Prop :=
  P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
    ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤

def liftOw (w : Place p R) {S : Type} [CommRing S] (ψ : Op p R →+* S) (h : ψ w.e = 1) :
    w.Ow →+* S :=
  Ideal.Quotient.lift _ ψ (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [h])

namespace IsPrimeUnder

variable {w : Place p R} {P : Ideal R}

/- English proof (translation)
Rewrite using `[← map_natCast w.toOw]`. Conclude with `Ideal.mem_map_of_mem _ h.2.1`.
-/
theorem p_mem (h : IsPrimeUnder w P) : (p : w.Ow) ∈ P.map w.toOw := by
  rw [← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ h.2.1

/- English proof (translation)
Use `h.1` as an intermediate fact. Take `⟨Q, hPQ, hQe⟩` from `Ideal.eq_prime_pow_mul_coprime hJ P`. Generalize the expression as in `Multiset.count P _ = e at hQe`. Establish `hQ0 : Q ≠ ⊥` using `by rintro rfl; exact hJ (by simpa using hQe)`. Rewrite using `[hQe, Ideal.map_mul, Ideal.map_pow, GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P h.1 h.2.2.2 Q hQ0 hPQ, Ideal.mul_top]`.
-/
theorem map_eq_pow [IsDedekindDomain R] (h : IsPrimeUnder w P) {J : Ideal R} (hJ : J ≠ ⊥) :
    J.map w.toOw =
      P.map w.toOw ^ (UniqueFactorizationMonoid.normalizedFactors J).count P := by
  have := h.1
  obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime hJ P
  generalize Multiset.count P _ = e at hQe
  have hQ0 : Q ≠ ⊥ := by rintro rfl; exact hJ (by simpa using hQe)
  rw [hQe, Ideal.map_mul, Ideal.map_pow,
    GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P h.1 h.2.2.2 Q hQ0 hPQ, Ideal.mul_top]

variable [IsDedekindDomain R] [CharZero R]

/- English proof (translation)
Rewrite using `[← h.map_eq_pow (by simpa using (Fact.out : p.Prime).ne_zero), Ideal.map_span, Set.image_singleton, map_natCast]`.
-/
theorem span_p_eq (h : IsPrimeUnder w P) :
    Ideal.span {(p : w.Ow)} = P.map w.toOw ^
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P := by
  rw [← h.map_eq_pow (by simpa using (Fact.out : p.Prime).ne_zero), Ideal.map_span,
    Set.image_singleton, map_natCast]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `h.span_p_eq`. Rewrite `h1` using `[h0, pow_zero, Ideal.one_eq_top]`. Conclude with `h.2.2.1.ne_top (eq_top_iff.2 (h1 ▸ (Ideal.span_singleton_le_iff_mem _).2 h.p_mem))`.
-/
theorem count_ne_zero (h : IsPrimeUnder w P) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P ≠ 0 := by
  intro h0
  have h1 := h.span_p_eq
  rw [h0, pow_zero, Ideal.one_eq_top] at h1
  exact h.2.2.1.ne_top (eq_top_iff.2 (h1 ▸ (Ideal.span_singleton_le_iff_mem _).2 h.p_mem))

variable [Module.Finite ℤ R]

/- English proof (translation)
Establish `key : ∀ i j : ℕ, P.map w.toOw ^ i = P.map w.toOw ^ j → ¬ i < j`. Introduce `i j hij hlt`. Establish `h1 : Ideal.span {(p : w.Ow) ^ i} = Ideal.span {(p : w.Ow) ^ j}`. Rewrite using `[← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, h.span_p_eq, ← pow_mul, ← pow_mul, mul_comm _ i, mul_comm _ j, pow_mul, pow_mul, hij]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_lt hlt`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (h1 ▸ Ideal.mem_span_singleton_self _)`. Establish `h2 : ∀ (n : ℕ) (x : w.Ow), (p : w.Ow) ^ n * x = 0 → x = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`.

Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`. Conclude with `GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w x (ih _ (by linear_combination hx))`. Establish `h3` using `h2 i (1 - c * p ^ k * p) (by linear_combination -hc)`.

Apply `h.2.2.1.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, sub_eq_zero.1 h3]`. Conclude with `Ideal.mul_mem_left _ _ h.p_mem`. Conclude with `le_antisymm (not_lt.1 (key j i hij.symm)) (not_lt.1 (key i j hij))`.
-/
theorem pow_inj (h : IsPrimeUnder w P) {i j : ℕ}
    (hij : P.map w.toOw ^ i = P.map w.toOw ^ j) : i = j := by
  have key : ∀ i j : ℕ, P.map w.toOw ^ i = P.map w.toOw ^ j → ¬ i < j := by
    intro i j hij hlt
    have h1 : Ideal.span {(p : w.Ow) ^ i} = Ideal.span {(p : w.Ow) ^ j} := by
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, h.span_p_eq, ← pow_mul,
        ← pow_mul, mul_comm _ i, mul_comm _ j, pow_mul, pow_mul, hij]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h2 : ∀ (n : ℕ) (x : w.Ow), (p : w.Ow) ^ n * x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        exact GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w x (ih _ (by linear_combination hx))
    have h3 := h2 i (1 - c * p ^ k * p) (by linear_combination -hc)
    apply h.2.2.1.ne_top
    rw [Ideal.eq_top_iff_one, sub_eq_zero.1 h3]
    exact Ideal.mul_mem_left _ _ h.p_mem
  exact le_antisymm (not_lt.1 (key j i hij.symm)) (not_lt.1 (key i j hij))

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

/- English proof (translation)
Establish `: CharZero (FractionRing R)` using `inferInstance`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)) (FractionRing R)` using `IsIntegralClosure.isLocalization _ (FractionRing ℤ) _ _`. Establish `: FiniteDimensional (FractionRing ℤ) (FractionRing R)` using `.of_isLocalization ℤ R (nonZeroDivisors ℤ)`. Establish `hsep : Algebra.IsSeparable (FractionRing ℤ) (FractionRing R)` using `inferInstance`. Establish `hD : differentIdeal ℤ R ≠ ⊥` using `differentIdeal_ne_bot`.

Establish `h1` using `h.span_p_eq`. Establish `h2` using `h.map_eq_pow hD`. Establish `he` using `h.count_ne_zero`. Generalize the expression as in `Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})) = e at h1 he ⊢`. Generalize the expression as in `Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R)) = k at h2 ⊢`.

Establish `he' : (e : ℝ) ≠ 0` using `by exact_mod_cast he`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, hb, hvd, hab⟩`. Rewrite `hab` using `[← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul]`. Establish `h3 : (k : ℝ) * b = e * a` using `by exact_mod_cast h.pow_inj hab`.

Establish `hb' : (b : ℝ) ≠ 0` using `by exact_mod_cast hb.ne'`. Rewrite using `[eq_div_iff he']`. Apply `mul_right_cancel₀ hb'` to reduce the goal to its premises. Rewrite using `[h3, ← hvd]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `rfl`. Use `⟨k, e, Nat.pos_of_ne_zero he, div_mul_cancel₀ _ he', ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem isDiffVal_iff (h : IsPrimeUnder w P) (vd : ℝ) :
    w.IsDiffVal_vp vd ↔ vd =
      ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R)).count P : ℝ) /
        ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P : ℝ) := by
  have : CharZero (FractionRing R) := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)) (FractionRing R) :=
    IsIntegralClosure.isLocalization _ (FractionRing ℤ) _ _
  have : FiniteDimensional (FractionRing ℤ) (FractionRing R) :=
    .of_isLocalization ℤ R (nonZeroDivisors ℤ)
  have hsep : Algebra.IsSeparable (FractionRing ℤ) (FractionRing R) := inferInstance
  have hD : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have h1 := h.span_p_eq
  have h2 := h.map_eq_pow hD
  have he := h.count_ne_zero
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span {(p : R)})) = e at h1 he ⊢
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (differentIdeal ℤ R)) = k at h2 ⊢
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  constructor
  · rintro ⟨a, b, hb, hvd, hab⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul] at hab
    have h3 : (k : ℝ) * b = e * a := by exact_mod_cast h.pow_inj hab
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [eq_div_iff he']
    apply mul_right_cancel₀ hb'
    rw [h3, ← hvd]; ring
  · rintro rfl
    refine ⟨k, e, Nat.pos_of_ne_zero he, div_mul_cancel₀ _ he', ?_⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul, mul_comm]

end IsPrimeUnder

end GlobalTheory.AvChartCompare
