import Development.EtaleCohomology.EtaleTrace.GenEtalePfCut

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Introduce `k _ _ X P _ _ p r π hπ hr hfin hsurj`. Take `⟨x⟩ : Nonempty P` from `inferInstance`. Take `⟨U, hU, hxU, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show x ∈ (⊤ : P.Opens) from trivial)`. Establish `hU' : IsAffineOpen (π ⁻¹ᵁ U)` using `hU.preimage π`. Use `⟨U, hU, ⟨x, hxU⟩, hU', ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hft : (r.appLE ⊤ U le_top).hom.FiniteType` using `HasRingHomProperty.appLE (P := @LocallyOfFiniteType) r hr ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Use `letI := (r.appLE ⊤ U le_top).hom.toAlgebra`. Use `haveI : IsNoetherianRing Γ(S k, ⊤) := isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm`. Use `haveI : Algebra.FiniteType Γ(S k, ⊤) Γ(P, U) := hft`. Conclude with `Algebra.FiniteType.isNoetherianRing Γ(S k, ⊤) Γ(P, U)`.

Use `haveI : IsAffine U := hU`. Establish `h0 : (π ∣_ U).appTop.hom.Finite` using `(π ∣_ U).finite_appTop`. Rewrite `h0` using `[morphismRestrict_appTop]`. Establish `gen : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = U → RingHom.Finite (π.app W ≫ X.presheaf.map (eqToHom h).op).hom → RingHom.Finite (π.app U).hom`. Introduce and unpack `W T h rfl`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `gen _ _ _ (by simp) h0`. Use `haveI : IsDominant π := inferInstance haveI : IsSchemeTheoreticallyDominant π := .of_isDominant π`. Conclude with `π.app_injective U`.
-/
theorem genAffineData : GenAffineData := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show x ∈ (⊤ : P.Opens) from trivial)
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  refine ⟨U, hU, ⟨x, hxU⟩, hU', ?_, ?_, ?_⟩
  · have hft : (r.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) r hr ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    letI := (r.appLE ⊤ U le_top).hom.toAlgebra
    haveI : IsNoetherianRing Γ(S k, ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
    haveI : Algebra.FiniteType Γ(S k, ⊤) Γ(P, U) := hft
    exact Algebra.FiniteType.isNoetherianRing Γ(S k, ⊤) Γ(P, U)
  · haveI : IsAffine U := hU
    have h0 : (π ∣_ U).appTop.hom.Finite := (π ∣_ U).finite_appTop
    rw [morphismRestrict_appTop] at h0
    have gen : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = U →
        RingHom.Finite (π.app W ≫ X.presheaf.map (eqToHom h).op).hom → RingHom.Finite (π.app U).hom := by
      rintro W T h rfl
      subst h
      simp
    exact gen _ _ _ (by simp) h0
  · haveI : IsDominant π := inferInstance
    haveI : IsSchemeTheoreticallyDominant π := .of_isDominant π
    exact π.app_injective U

/- English proof (translation)
The claim follows from `GenEtale_of' genAffineData h`.
-/
theorem GenEtale_of_atBot (h : GenEtaleAtBot) : GenEtale := GenEtale_of' genAffineData h

end LateralTheory.EtaleTrace.Cov
