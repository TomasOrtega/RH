import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ ι χ μ hχ`. Take `⟨_, art, a, hart, _, hL⟩` from `hχ`. Establish `hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (l : 𝓞 F) ∉ v.asIdeal`. Establish `hne : Ideal.span {(l : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `(Fact.out : Nat.Prime l).ne_zero` after adjusting the coercions. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset ?_)` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_setOf_eq, not_not] at hv ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hv`. Use `filter_upwards [GlobalTheory.GalChar.unr_ae χ, hl] with v hu hv`. Use `⟨hu, fun A hA => ⟨(GlobalTheory.HeckeGal.IsLAdicOf.unr_iff hart hL (Or.inl hv) hA).2 hu, fun σ hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.HeckeGal.IsLAdicOf.frob_unr hart hL (Or.inl hv) hu hA hσ`. Rewrite using `[map_inv, Units.val_inv_eq_inv_val, h, inv_inv, RingEquiv.apply_symm_apply]`.
-/
theorem UpperTheory.galois_character_frobenius_compatibility :
    UpperTheory.V.Af.Sol.CharFrob := by
  intro F Ω _ _ _ _ _ l _ ι χ μ hχ
  obtain ⟨_, art, a, hart, _, hL⟩ := hχ
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (l : 𝓞 F) ∉ v.asIdeal := by
    have hne : Ideal.span {(l : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset ?_)
    intro v hv
    simp only [Set.mem_setOf_eq, not_not] at hv ⊢
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  filter_upwards [GlobalTheory.GalChar.unr_ae χ, hl] with v hu hv
  refine ⟨hu, fun A hA => ⟨(GlobalTheory.HeckeGal.IsLAdicOf.unr_iff hart hL (Or.inl hv) hA).2 hu, fun σ hσ => ?_⟩⟩
  have h := GlobalTheory.HeckeGal.IsLAdicOf.frob_unr hart hL (Or.inl hv) hu hA hσ
  rw [map_inv, Units.val_inv_eq_inv_val, h, inv_inv, RingEquiv.apply_symm_apply]
