import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.LaurSplit

variable {K : Type} [CommRing K]

/- English proof (translation)
Rewrite using `[LaurentPolynomial.coeff_toLaurent]`. Conclude with `Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k`.
-/
theorem coeff_nat (p : Polynomial K) (k : ℕ) :
    (Polynomial.toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k

/- English proof (translation)
Rewrite using `[LaurentPolynomial.coeff_toLaurent]`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨m, hm⟩`. Establish `: (m : ℤ) = k` using `hm`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_neg (p : Polynomial K) (k : ℤ) (hk : k < 0) :
    (Polynomial.toLaurent p).coeff k = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = k := hm
  omega

/- English proof (translation)
Establish `hc : ∀ n : ℤ, (Polynomial.toLaurent a).coeff n = (Polynomial.toLaurent b).coeff (-n)` using `fun n => by rw [h, LaurentPolynomial.invert_apply]`. Prove the components needed by the constructor for the conclusion. Use extensionality with `n`. Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[Polynomial.coeff_C_succ, ← coeff_nat, hc]`. Conclude with `coeff_neg b _ (by omega)`. Use extensionality with `n`. Break down `n with _ | n` into its components or cases. Establish `h0` using `hc ((0 : ℕ) : ℤ)`.

Rewrite `h0` using `[coeff_nat]`. Establish `h1 : (-(((0 : ℕ) : ℤ))) = ((0 : ℕ) : ℤ)` using `by simp`. Rewrite `h0` using `[h1, coeff_nat]`. Simplify using `[h0]`. Establish `h0` using `hc (((n + 1 : ℕ) : ℤ) * (-1))`.

Establish `h1 : (-(((n + 1 : ℕ) : ℤ) * (-1))) = ((n + 1 : ℕ) : ℤ)` using `by ring`. Rewrite `h0` using `[h1, coeff_nat, coeff_neg a _ (by omega)]`. Rewrite using `[Polynomial.coeff_C_succ, ← h0]`.
-/
theorem eq_C_of_toLaurent_eq_invert (a b : Polynomial K)
    (h : Polynomial.toLaurent a = LaurentPolynomial.invert (Polynomial.toLaurent b)) :
    a = Polynomial.C (a.coeff 0) ∧ b = Polynomial.C (a.coeff 0) := by
  have hc : ∀ n : ℤ, (Polynomial.toLaurent a).coeff n = (Polynomial.toLaurent b).coeff (-n) :=
    fun n => by rw [h, LaurentPolynomial.invert_apply]
  constructor
  · ext n
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_C_succ, ← coeff_nat, hc]
      exact coeff_neg b _ (by omega)
  · ext n
    rcases n with _ | n
    · have h0 := hc ((0 : ℕ) : ℤ)
      rw [coeff_nat] at h0
      have h1 : (-(((0 : ℕ) : ℤ))) = ((0 : ℕ) : ℤ) := by simp
      rw [h1, coeff_nat] at h0
      simp [h0]
    · have h0 := hc (((n + 1 : ℕ) : ℤ) * (-1))
      have h1 : (-(((n + 1 : ℕ) : ℤ) * (-1))) = ((n + 1 : ℕ) : ℤ) := by ring
      rw [h1, coeff_nat, coeff_neg a _ (by omega)] at h0
      rw [Polynomial.coeff_C_succ, ← h0]

/- English proof (translation)
Proceed by induction on `h using LaurentPolynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨p₁, p₂, rfl⟩` from `hp`. Take `⟨q₁, q₂, rfl⟩` from `hq`. Use `⟨p₁ + q₁, p₂ + q₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `C_mul_T n a`. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = -1 + -(m : ℤ)` from `⟨(-n - 1).toNat, by omega⟩`.

Use `⟨0, Polynomial.C a * Polynomial.X ^ m, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.toLaurent_C_mul_X_pow, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, map_zero, zero_add, LaurentPolynomial.T_add]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ)` from `⟨n.toNat, by omega⟩`. Use `⟨Polynomial.C a * Polynomial.X ^ m, 0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.toLaurent_C_mul_X_pow]`. Simplify using the standard rewrite rules.
-/
theorem exists_split (h : K[T;T⁻¹]) :
    ∃ h₁ h₂ : Polynomial K, h = Polynomial.toLaurent h₁ +
      LaurentPolynomial.T (-1) * LaurentPolynomial.invert (Polynomial.toLaurent h₂) := by
  induction h using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, p₂, rfl⟩ := hp
    obtain ⟨q₁, q₂, rfl⟩ := hq
    refine ⟨p₁ + q₁, p₂ + q₂, ?_⟩
    simp only [map_add]
    ring
  | C_mul_T n a =>
    rcases lt_or_ge n 0 with hn | hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -1 + -(m : ℤ) := ⟨(-n - 1).toNat, by omega⟩
      refine ⟨0, Polynomial.C a * Polynomial.X ^ m, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow, map_mul, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, map_zero, zero_add, LaurentPolynomial.T_add]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
      refine ⟨Polynomial.C a * Polynomial.X ^ m, 0, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow]
      simp

/- English proof (translation)
Introduce `K _ f g α β hmem`. Take `⟨h, hh⟩` from `Ideal.mem_span_singleton'.1 hmem`. Take `⟨h₁, h₂, rfl⟩` from `exists_split h`. Establish `hT : (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : K[T;T⁻¹]) = 1`. Rewrite using `[← LaurentPolynomial.T_add]`.

Simplify using the standard rewrite rules. Establish `key : Polynomial.toLaurent (α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁) = LaurentPolynomial.invert (Polynomial.toLaurent (β - (Polynomial.C g - Polynomial.X * Polynomial.C f) * h₂))`. Simplify using `only [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]`. Take the linear combination `(-1 : K[T;T⁻¹]) * hh - LaurentPolynomial.invert (Polynomial.toLaurent h₂) * LaurentPolynomial.C g * hT`. Take `⟨ha, hb⟩` from `eq_C_of_toLaurent_eq_invert _ _ key`.

Use `⟨(α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁).coeff 0, Ideal.mem_span_singleton'.2 ⟨h₁, ?_⟩, Ideal.mem_span_singleton'.2 ⟨h₂, ?_⟩⟩` and prove the remaining obligations. Take the linear combination `(-1 : Polynomial K) * ha`. Take the linear combination `(-1 : Polynomial K) * hb`.
-/
theorem exists_const_of_mem_span : ∀ (K : Type) [CommRing K] (f g : K) (α β : Polynomial K),
    Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β) ∈
      Ideal.span {(LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g : K[T;T⁻¹])} →
    ∃ c : K, α - Polynomial.C c ∈ Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g} ∧
      β - Polynomial.C c ∈ Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f} := by
  intro K _ f g α β hmem
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨h₁, h₂, rfl⟩ := exists_split h
  have hT : (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  have key : Polynomial.toLaurent (α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁) =
      LaurentPolynomial.invert (Polynomial.toLaurent
        (β - (Polynomial.C g - Polynomial.X * Polynomial.C f) * h₂)) := by
    simp only [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    linear_combination (-1 : K[T;T⁻¹]) * hh -
      LaurentPolynomial.invert (Polynomial.toLaurent h₂) * LaurentPolynomial.C g * hT
  obtain ⟨ha, hb⟩ := eq_C_of_toLaurent_eq_invert _ _ key
  refine ⟨(α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁).coeff 0,
    Ideal.mem_span_singleton'.2 ⟨h₁, ?_⟩, Ideal.mem_span_singleton'.2 ⟨h₂, ?_⟩⟩
  · linear_combination (-1 : Polynomial K) * ha
  · linear_combination (-1 : Polynomial K) * hb

end GlobalTheory.CompanionTheory.LaurSplit
