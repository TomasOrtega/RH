import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (σ (x : K))` using `(RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom`. Establish `h2 : IsIntegral A (σ (x : K))` using `h1.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h2`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem ringOfIntegers_map_mem_valuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) (x : 𝓞 K) : σ (x : K) ∈ A := by
  have h1 : IsIntegral ℤ (σ (x : K)) := (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (x : K)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

noncomputable def ringOfIntegersToValuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) : 𝓞 K →+* A :=
  ((σ.comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
    (fun x => ringOfIntegers_map_mem_valuationSubring A σ x))

/- English proof (translation)
Introduce `K _ _ A p _ hpA P hpP α h hα σ`. Use `set f := ringOfIntegersToValuationSubring A σ with hf`. Establish `hfx : ∀ x : 𝓞 K, ((f x : A) : ℂ) = σ (x : K)` using `fun x => rfl`. Use `set Q : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f with hQ`. Establish `hQp : Q.IsPrime` using `Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)`.

Establish `hQne : Q ≠ ⊤` using `hQp.ne_top`. Establish `hmem : ∀ x : 𝓞 K, x ∈ Q ↔ A.valuation (σ (x : K)) < 1`. Introduce `x`. Rewrite using `[hQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hfx]`. Establish `hpQ : (p : 𝓞 K) ∈ Q`.

Rewrite using `[hmem]`. Establish `: σ (((p : 𝓞 K) : K)) = (p : ℂ)` using `by simp`. Rewrite using `[this]`. Conclude with `(ValuationSubring.mem_nonunits_iff A).mp hpA`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Conclude with `(ValuationSubring.valuation_le_one_iff A _).mpr (ringOfIntegers_map_mem_valuationSubring A σ α)`. Assume the negation of the conclusion as `hlt push_neg at hlt`. Establish `hαQ : α ∈ Q` using `(hmem α).mpr hlt`. Establish `hspan : P.asIdeal ^ h ≤ Q`. Rewrite using `[← hα, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hαQ`. Establish `hPQ : P.asIdeal ≤ Q` using `Ideal.IsPrime.le_of_pow_le hspan`. Establish `hPeq : P.asIdeal = Q` using `P.isMaximal.eq_of_le hQne hPQ`. Conclude with `hpP (hPeq ▸ hpQ)`.
-/
theorem valuation_embedding_generator_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
      ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h →
      ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  intro K _ _ A p _ hpA P hpP α h hα σ
  set f := ringOfIntegersToValuationSubring A σ with hf
  have hfx : ∀ x : 𝓞 K, ((f x : A) : ℂ) = σ (x : K) := fun x => rfl
  set Q : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)
  have hQne : Q ≠ ⊤ := hQp.ne_top
  have hmem : ∀ x : 𝓞 K, x ∈ Q ↔ A.valuation (σ (x : K)) < 1 := by
    intro x
    rw [hQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hfx]
  have hpQ : (p : 𝓞 K) ∈ Q := by
    rw [hmem]
    have : σ (((p : 𝓞 K) : K)) = (p : ℂ) := by simp
    rw [this]
    exact (ValuationSubring.mem_nonunits_iff A).mp hpA
  refine le_antisymm ?_ ?_
  · exact (ValuationSubring.valuation_le_one_iff A _).mpr (ringOfIntegers_map_mem_valuationSubring A σ α)
  · by_contra hlt
    push_neg at hlt
    have hαQ : α ∈ Q := (hmem α).mpr hlt
    have hspan : P.asIdeal ^ h ≤ Q := by
      rw [← hα, Ideal.span_singleton_le_iff_mem]
      exact hαQ
    have hPQ : P.asIdeal ≤ Q := Ideal.IsPrime.le_of_pow_le hspan
    have hPeq : P.asIdeal = Q := P.isMaximal.eq_of_le hQne hPQ
    exact hpP (hPeq ▸ hpQ)

end GlobalTheory
