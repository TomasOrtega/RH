import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.LaurSplit

variable {K : Type} [CommRing K]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_nat (p : Polynomial K) (k : ℕ) :
    (Polynomial.toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_neg (p : Polynomial K) (k : ℤ) (hk : k < 0) :
    (Polynomial.toLaurent p).coeff k = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = k := hm
  omega

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.
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
