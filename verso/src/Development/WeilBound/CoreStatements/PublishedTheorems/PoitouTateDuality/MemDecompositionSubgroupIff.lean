import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise

namespace PositivityTheory.PTNLoc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x`. Introduce `h show σ • A = A`. Use extensionality with `y`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Use `h ((σ⁻¹ : G F Ω) y)` as an intermediate fact. Rewrite `this` using `[ReciprocityTheory.Gal.mul_inv_apply]`. Conclude with `this.symm`.
-/
theorem mem_decompositionSubgroup_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    exact ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : G F Ω) y)
    rw [ReciprocityTheory.Gal.mul_inv_apply] at this
    exact this.symm

/- English proof (translation)
Rewrite using `[A'.valuation_le_one_iff, A.valuation_le_one_iff]`. Conclude with `hA x`.
-/
theorem valuation_le_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff]
  exact hA x

/- English proof (translation)
Rewrite using `[ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x, hA, hA, map_eq_zero_iff E E.injective]`.
-/
theorem valuation_lt_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) < 1 ↔ A.valuation x < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x,
    hA, hA, map_eq_zero_iff E E.injective]

/- English proof (translation)
Introduce `F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ`. Establish `hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F'`. Rewrite using `[mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`.

Take `⟨x, rfl⟩` from `E.surjective y`. Rewrite using `[hΦ, hA, hA]`. Conclude with `h x`. Introduce `h x`. Use `h (E x)` as an intermediate fact.

Rewrite `this` using `[hΦ, hA, hA]`. Then use the resulting hypothesis. Use `⟨hdec, ?_, fun q => ?_⟩` and prove the remaining obligations. Use `show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)`. Use `and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `E.surjective y`.

Rewrite using `[hΦ, ← map_sub E, valuation_lt_one_transport E hA]`. Conclude with `h x ((valuation_le_one_transport E hA x).1 hy)`. Use `h (E x) ((valuation_le_one_transport E hA x).2 hx)` as an intermediate fact. Rewrite `this` using `[hΦ, ← map_sub E, valuation_lt_one_transport E hA]`. Then use the resulting hypothesis. Use `show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)`.

Use `and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `E.surjective y`. Rewrite using `[hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]`. Conclude with `h x ((valuation_le_one_transport E hA x).1 hy)`. Use `h (E x) ((valuation_le_one_transport E hA x).2 hx)` as an intermediate fact.

Rewrite `this` using `[hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]`. Then use the resulting hypothesis.
-/
theorem locHyp : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ
  have hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F' := by
    rw [mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, hA, hA]
      exact h x
    · intro h x
      have := h (E x)
      rwa [hΦ, hA, hA] at this
  refine ⟨hdec, ?_, fun q => ?_⟩
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_sub E, valuation_lt_one_transport E hA] at this
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA] at this

end PositivityTheory.PTNLoc
