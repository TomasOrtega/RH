import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ w A hA M hM s hs ζ hζ`. Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Conclude with `hM (by simpa using w.asIdeal.zero_mem)`. Establish `hvM : A.valuation (M : Ω) = 1`.

Establish `h1` using `(hA (M : 𝓞 F)).not.mpr hM`. Establish `h2 : (algebraMap F Ω) ((M : 𝓞 F) : F) = (M : Ω)` using `by simp`. Rewrite `h1` using `[h2]`. Use `le_antisymm ?_ (not_lt.mp h1)` and prove the remaining obligations. Simplify using `using A.valuation_le_one (M : A)`.

Establish `hvz : A.valuation ζ = 1`. Establish `hp : A.valuation ζ ^ M = 1` using `by rw [← map_pow, hζ, map_one]`. Break down `lt_trichotomy (A.valuation ζ) 1 with h | h | h` into its components or cases. Conclude with `absurd hp (pow_lt_one₀ zero_le' h hM0).ne`. Conclude with `h`.

Conclude with `absurd hp (one_lt_pow₀ h hM0).ne'`. Establish `hI : s ∈ Inertia A` using `hs`. Unfold `Inertia at hI`. Take `⟨-, hI⟩` from `hI`. Establish `hd : A.valuation (s ζ - ζ) < 1` using `hI ζ hvz.le`.

Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hvz`. Use `set η := s ζ / ζ with hηdef`. Establish `hsz : s ζ = η * ζ` using `(div_mul_cancel₀ _ hζ0).symm`.

Establish `hη : η ^ M = 1`. Rewrite using `[hηdef, div_pow, ← map_pow, hζ, map_one, div_one]`. Establish `hη1 : A.valuation (η - 1) < 1`. Establish `e : s ζ - ζ = (η - 1) * ζ` using `by rw [hsz]; ring`. Rewrite `hd` using `[e, map_mul, hvz, mul_one]`.

Conclude with `hd`. Establish `hvη : A.valuation η = 1`. Establish `e : η = 1 + (η - 1)` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_one_add_of_lt _ hη1`.

Assume the negation of the conclusion as `hne`. Establish `hne' : η ≠ 1`. Introduce `h1`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hsz, h1, one_mul]`.

Establish `hsum : ∑ i ∈ Finset.range M, η ^ i = 0`. Establish `e` using `mul_geom_sum η M`. Rewrite `e` using `[hη, sub_self]`. Conclude with `(mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne')`. Establish `hMsum : (M : Ω) = ∑ i ∈ Finset.range M, (1 - η ^ i)`.

Rewrite using `[Finset.sum_sub_distrib, hsum, sub_zero]`. Simplify using the standard rewrite rules. Establish `hlt : A.valuation (M : Ω) < 1`. Rewrite using `[hMsum]`. Use `Valuation.map_sum_lt _ one_ne_zero ?_` and prove the remaining obligations.

Introduce `i _`. Establish `e` using `mul_geom_sum η i`. Establish `hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1`. Use `Valuation.map_sum_le _ ?_` and prove the remaining obligations. Introduce `j _`.

Rewrite using `[map_pow, hvη, one_pow]`. Rewrite using `[Valuation.map_sub_swap, ← e, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[hvM]`. Conclude with `lt_irrefl _ hlt`.
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
