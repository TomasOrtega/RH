import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    IsPlaceOver A w → ∀ M : ℕ, (M : 𝓞 F) ∉ w.asIdeal → ∀ s ∈ Ine (F := F) A, ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ w A hA M hM s hs ζ hζ
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simpa using w.asIdeal.zero_mem)
  have hvM : A.valuation (M : Ω) = 1 := by
    have h1 := (hA (M : 𝓞 F)).not.mpr hM
    have h2 : (algebraMap F Ω) ((M : 𝓞 F) : F) = (M : Ω) := by simp
    rw [h2] at h1
    refine le_antisymm ?_ (not_lt.mp h1)
    simpa using A.valuation_le_one (M : A)
  have hvz : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ M = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with h | h | h
    · exact absurd hp (pow_lt_one₀ zero_le' h hM0).ne
    · exact h
    · exact absurd hp (one_lt_pow₀ h hM0).ne'
  have hI : s ∈ Inertia A := hs
  unfold Inertia at hI
  obtain ⟨-, hI⟩ := hI
  have hd : A.valuation (s ζ - ζ) < 1 := hI ζ hvz.le
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hvz
  set η := s ζ / ζ with hηdef
  have hsz : s ζ = η * ζ := (div_mul_cancel₀ _ hζ0).symm
  have hη : η ^ M = 1 := by
    rw [hηdef, div_pow, ← map_pow, hζ, map_one, div_one]
  have hη1 : A.valuation (η - 1) < 1 := by
    have e : s ζ - ζ = (η - 1) * ζ := by rw [hsz]; ring
    rw [e, map_mul, hvz, mul_one] at hd
    exact hd
  have hvη : A.valuation η = 1 := by
    have e : η = 1 + (η - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hη1
  by_contra hne
  have hne' : η ≠ 1 := by
    intro h1
    apply hne
    rw [hsz, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, η ^ i = 0 := by
    have e := mul_geom_sum η M
    rw [hη, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne')
  have hMsum : (M : Ω) = ∑ i ∈ Finset.range M, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  have hlt : A.valuation (M : Ω) < 1 := by
    rw [hMsum]
    refine Valuation.map_sum_lt _ one_ne_zero ?_
    intro i _
    have e := mul_geom_sum η i
    have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
      refine Valuation.map_sum_le _ ?_
      intro j _
      rw [map_pow, hvη, one_pow]
    rw [Valuation.map_sub_swap, ← e, map_mul]
    calc A.valuation (η - 1) * A.valuation (∑ j ∈ Finset.range i, η ^ j)
        ≤ A.valuation (η - 1) * 1 := by gcongr
      _ = A.valuation (η - 1) := mul_one _
      _ < 1 := hη1
  rw [hvM] at hlt
  exact lt_irrefl _ hlt
