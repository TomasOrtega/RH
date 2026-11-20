import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyAndNormOfPowEqUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlacStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRecip

/- English proof (translation)
Introduce `hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ`. Establish `hint : IsIntegral E π` using `Algebra.IsIntegral.isIntegral π`. Establish `: FiniteDimensional E (IntermediateField.adjoin E {π})` using `IntermediateField.adjoin.finiteDimensional hint`. Establish `: NumberField (IntermediateField.adjoin E {π})` using `NumberField.of_module_finite E _`. Establish `: IsAlgClosure (IntermediateField.adjoin E {π}) Ω` using `⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩`.

Use `set K := IntermediateField.adjoin E {π} with hKdef`. Take `⟨artK, hartK⟩` from `hG K Ω`. Take `⟨W, hWv, hWuniq, hAW, hnW, hunif⟩` from `GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ`. Take `⟨-, hnorm⟩` from `GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ`. Establish `hπ0 : π ≠ 0`.

Introduce and unpack `rfl`. Establish `hv1 : (1 : 𝓞 E) ∉ v.asIdeal` using `fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Break down `Nat.eq_zero_or_pos (normV v - 1) with h0 | h0` into its components or cases. Rewrite `hπ` using `[h0, pow_zero]`. Establish `: (ϖ : E) = ((1 : 𝓞 E) : E)`.

Apply `(algebraMap E Ω).injective` to reduce the goal to its premises. Rewrite using `[← hπ]`. Simplify using the standard rewrite rules. Conclude with `hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)`. Rewrite `hπ` using `[zero_pow h0.ne']`.

Establish `: (ϖ : E) = 0` using `(map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm`. Conclude with `hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)`. Establish `hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0`. Introduce `h`. Apply `hπ0` to reduce the goal to its premises.

Use `congrArg (algebraMap K Ω) h` as an intermediate fact. Simplify using `using this`. Use `set yK : Kˣ := Units.mk0 _ hgen0 with hyK`. Use `set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ`. Establish `hcu : IsUnifAt W cπ` using `hunif cπ rfl`.

Take `⟨σ, hσF, hσA⟩` from `(hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩`. Establish `hN` using `GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA`. Use `⟨σ.restrictScalars E, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hnW]`. Conclude with `hσF`.

Use `σ.commutes (IntermediateField.AdjoinSimple.gen E π)` as an intermediate fact. Simplify using `using this`. Introduce `c hc`. Establish `hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E` using `rfl`. Rewrite using `[hinv, hN]`.

Use `congr 2`. Use `ext`. Rewrite using `[hc]`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]`. Rewrite using `[hnorm]`.

Simplify using the standard rewrite rules.
-/
theorem exists_frob_fix_of_eisenstein : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField (IntermediateField.adjoin E {π}) := NumberField.of_module_finite E _
  have : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  set K := IntermediateField.adjoin E {π} with hKdef
  obtain ⟨artK, hartK⟩ := hG K Ω
  obtain ⟨W, hWv, hWuniq, hAW, hnW, hunif⟩ := GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨-, hnorm⟩ := GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hv1 : (1 : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rcases Nat.eq_zero_or_pos (normV v - 1) with h0 | h0
    · rw [h0, pow_zero] at hπ
      have : (ϖ : E) = ((1 : 𝓞 E) : E) := by
        apply (algebraMap E Ω).injective; rw [← hπ]; simp
      exact hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)
    · rw [zero_pow h0.ne'] at hπ
      have : (ϖ : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm
      exact hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)
  have hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h; apply hπ0
    have := congrArg (algebraMap K Ω) h
    simpa using this
  set yK : Kˣ := Units.mk0 _ hgen0 with hyK
  set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ
  have hcu : IsUnifAt W cπ := hunif cπ rfl
  obtain ⟨σ, hσF, hσA⟩ := (hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩
  have hN := GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA
  refine ⟨σ.restrictScalars E, ?_, ?_, ?_⟩
  · rw [← hnW]; exact hσF
  · have := σ.commutes (IntermediateField.AdjoinSimple.gen E π)
    simpa using this
  · intro c hc
    have hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E := rfl
    rw [hinv, hN]
    congr 2
    ext
    rw [hc]
    simp only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]
    rw [hnorm]
    simp

end GlobalTheory.TameRecip
