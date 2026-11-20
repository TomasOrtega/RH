import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Proceed by induction on `h using LaurentPolynomial.induction_on' with`. Consider the case `add f g hf hg`. Take `⟨α₁, β₁, rfl⟩` from `hf`. Take `⟨α₂, β₂, rfl⟩` from `hg`. Use `⟨α₁ + α₂, β₁ + β₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `C_mul_T n a`. Break down `le_total 0 n with hn | hn` into its components or cases. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`.

Use `⟨Polynomial.monomial m a, 0, ?_⟩` and prove the remaining obligations. Simplify using `[Polynomial.toLaurent_C_mul_T]`. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)`. Use `⟨0, -Polynomial.monomial m a, ?_⟩` and prove the remaining obligations. Establish `hn' : n = -(m : ℤ)` using `by omega`.

Substitute `hn'` using the available equality. Simplify using `[Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T, LaurentPolynomial.invert_C]`.
-/
theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

/- English proof (translation)
Introduce `p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y`. Take `⟨k, h, hy⟩` from `h₃.pow y`. Take `⟨α, β, rfl⟩` from `laurent_eq_toLaurent_sub_invert h`. Take `⟨-, -, root₁, -, -⟩` from `pf_facts p K₁ h₁.pf`. Take `⟨-, -, root₂, -, -⟩` from `pf_facts p K₂ h₂.pf`.

Take `⟨-, -, -, inj₃, -⟩` from `pf_facts p K₃ h₃.pf`. Take `⟨b₁, hb₁⟩` from `root₁ k (i₁ α)`. Take `⟨b₂, hb₂⟩` from `root₂ k (i₂ β)`. Take `⟨F, hF⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k`. Use `⟨b₁, b₂, inj₃ k _ _ ?_⟩` and prove the remaining obligations.

Establish `key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k)`. Rewrite using `[← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]`. Rewrite using `[hy, key, hb₁, hb₂, e₁, e₂, map_sub]`.
-/
theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
