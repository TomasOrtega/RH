import Development.EtaleCohomology.EtaleTrace.GenEtalePfCut

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Substitute using the available equality. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem GenEtale_of_atBot (h : GenEtaleAtBot) : GenEtale := GenEtale_of' genAffineData h

end LateralTheory.EtaleTrace.Cov
