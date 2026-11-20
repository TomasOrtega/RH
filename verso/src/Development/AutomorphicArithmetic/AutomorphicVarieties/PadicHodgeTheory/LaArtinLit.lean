import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

/- English proof (translation)
Take `⟨rc, a, ha, -⟩` from `H.loc.llc F Ω A w h`. Conclude with `⟨a, ha⟩`.
-/
theorem UpperTheory.V.Loc.localArtinReciprocity (H : GlobalTheory.Mem.LiteralAutomorphy.LitN) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) :
    ∃ a, IsLocalArtin h a := by
  obtain ⟨rc, a, ha, -⟩ := H.loc.llc F Ω A w h
  exact ⟨a, ha⟩
