import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)`.
-/
theorem valuation_algebraMap_int_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) : A.valuation (algebraMap E Ω (x : E)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)

/- English proof (translation)
Establish `hdvd : P.asIdeal ∣ Ideal.span {ϖ}` using `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal`. Introduce `hle`. Apply `h2` to reduce the goal to its premises.

Establish `: Ideal.span {ϖ} ≤ P.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `(Ideal.span_singleton_le_iff_mem _).1 this`. Take `⟨s, hsJ, hsP⟩` from `Set.not_subset.1 hJP`.

Establish `hmem : ϖ' * s ∈ Ideal.span {ϖ}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul h1' hsJ`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hmem`. Establish `hs1 : A.valuation (algebraMap E Ω (s : E)) = 1` using `le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))`.

Establish `e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Conclude with `ha` after adjusting the coercions. Establish `hv` using `congrArg A.valuation e`.

Rewrite `hv` using `[map_mul, map_mul, hs1, mul_one]`. Rewrite using `[← hv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_uniformiser_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hP : IsPlaceOver A P) {ϖ ϖ' : 𝓞 E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal) :
    A.valuation (algebraMap E Ω (ϖ' : E)) ≤ A.valuation (algebraMap E Ω (ϖ : E)) := by
  have hdvd : P.asIdeal ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal := by
    intro hle
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  have hmem : ϖ' * s ∈ Ideal.span {ϖ} := by
    rw [hJ]; exact Ideal.mul_mem_mul h1' hsJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hs1 : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))
  have e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact_mod_cast ha
  have hv := congrArg A.valuation e
  rw [map_mul, map_mul, hs1, mul_one] at hv
  rw [← hv]
  calc A.valuation (algebraMap E Ω (a : E)) * A.valuation (algebraMap E Ω (ϖ : E))
      ≤ 1 * A.valuation (algebraMap E Ω (ϖ : E)) := by
        gcongr; exact valuation_algebraMap_int_le_one A a
    _ = A.valuation (algebraMap E Ω (ϖ : E)) := one_mul _

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ`. Establish `hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0`. Introduce `x hx h0`. Apply `hx` to reduce the goal to its premises. Establish `hx0 : (x : E) = 0` using `(map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0`.

Establish `: x = 0` using `by exact_mod_cast hx0`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])`.

Establish `hπ0' : π' ≠ 0`. Introduce and unpack `rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])`. Establish `hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E))` using `le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')`. Use `set ρ := π' / π with hρ`. Establish `hρ0 : ρ ≠ 0` using `div_ne_zero hπ0' hπ0`.

Establish `hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E))`. Rewrite using `[hρ, div_pow, hπ, hπ', map_div₀]`. Establish `hvρm : A.valuation ρ ^ m = 1`. Rewrite using `[← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]`. Simplify using `using hne ϖ' h2'`.

Establish `hvρ : A.valuation ρ = 1`. Break down `lt_trichotomy (A.valuation ρ) 1 with h | h | h` into its components or cases. Conclude with `absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne`. Conclude with `h`. Conclude with `absurd hvρm (one_lt_pow₀ h hm0.ne').ne'`.

Establish `hmv : ¬ A.valuation (m : Ω) < 1`. Introduce `h`. Apply `hmP` to reduce the goal to its premises. Apply `(hP _).1` to reduce the goal to its premises. Simplify using `using h`.

Establish `hσρm : (σ ρ / ρ) ^ m = 1`. Rewrite using `[div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]`. Conclude with `div_self (pow_ne_zero _ hρ0)`. Establish `hclose : A.valuation (σ ρ / ρ - 1) < 1`. Establish `e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ` using `by field_simp`.

Rewrite using `[e, map_div₀, hvρ, div_one]`. Conclude with `hσ.2 ρ hvρ.le`. Establish `hfix : σ ρ / ρ = 1` using `root_eq_of_close A m hσρm (one_pow m) hmv hclose`. Establish `hfix' : σ ρ = ρ` using `(div_eq_one_iff_eq hρ0).1 hfix`. Establish `eπ' : π' = ρ * π` using `by rw [hρ]; field_simp`.

Rewrite using `[eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]`.
-/
theorem tame_quot_indep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ ϖ' : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ (π π' : Ω), π ^ m = algebraMap E Ω (ϖ : E) → π' ^ m = algebraMap E Ω (ϖ' : E) → ∀ σ ∈ Ine (F := E) A, σ π / π = σ π' / π' := by
  intro E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ
  have hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0 := by
    intro x hx h0
    apply hx
    have hx0 : (x : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0
    have : x = 0 := by exact_mod_cast hx0
    rw [this]; exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])
  have hπ0' : π' ≠ 0 := by
    rintro rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])
  have hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E)) :=
    le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')
  set ρ := π' / π with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hπ0' hπ0
  have hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E)) := by
    rw [hρ, div_pow, hπ, hπ', map_div₀]
  have hvρm : A.valuation ρ ^ m = 1 := by
    rw [← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]
    simpa using hne ϖ' h2'
  have hvρ : A.valuation ρ = 1 := by
    rcases lt_trichotomy (A.valuation ρ) 1 with h | h | h
    · exact absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne
    · exact h
    · exact absurd hvρm (one_lt_pow₀ h hm0.ne').ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    apply (hP _).1
    simpa using h
  have hσρm : (σ ρ / ρ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]
    exact div_self (pow_ne_zero _ hρ0)
  have hclose : A.valuation (σ ρ / ρ - 1) < 1 := by
    have e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ := by field_simp
    rw [e, map_div₀, hvρ, div_one]
    exact hσ.2 ρ hvρ.le
  have hfix : σ ρ / ρ = 1 := root_eq_of_close A m hσρm (one_pow m) hmv hclose
  have hfix' : σ ρ = ρ := (div_eq_one_iff_eq hρ0).1 hfix
  have eπ' : π' = ρ * π := by rw [hρ]; field_simp
  rw [eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]

end GlobalTheory.TameTau
