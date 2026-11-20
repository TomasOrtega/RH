import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFType

/- English proof (translation)
Establish `hC : (algebraMap ℤ C).FiniteType` using `RingHom.finiteType_algebraMap.2 inferInstance`. Establish `hE : (E.symm.toRingHom).FiniteType` using `RingHom.FiniteType.of_surjective _ E.symm.surjective`. Establish `h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType` using `hE.comp hC`. Establish `h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C)` using `RingHom.ext_int _ _`. Rewrite `h1` using `[← h2]`.

Conclude with `RingHom.FiniteType.of_comp_finiteType h1`.
-/
theorem finiteType_of_equiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℤ C]
    [Algebra.FiniteType ℤ C] (E : B ≃+* C) (g : ℤ →+* A) (f : A →+* B) : f.FiniteType := by
  have hC : (algebraMap ℤ C).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have hE : (E.symm.toRingHom).FiniteType := RingHom.FiniteType.of_surjective _ E.symm.surjective
  have h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType := hE.comp hC
  have h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C) := RingHom.ext_int _ _
  rw [← h2] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

/- English proof (translation)
Introduce `X Ω _ ξ κ _ x hall T`. Use `⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩` and prove the remaining obligations. Establish `hQ` using `(RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway RingHom.finiteType_holdsForLocalizationAway).1`. Rewrite using `[HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]`. Introduce `q`.

Take `⟨c, hcq⟩` from `T.cover ⟨q, hall q⟩`. Take `⟨U, hUa, hU⟩` from `T.affine c hcq.1`. Establish `hqU : q ∈ U` using `(hU q).2 ⟨hall q, hcq⟩`. Establish `hg : genPt ξ ∈ U` using `(hall q).mem_open U.isOpen hqU`. Take `⟨E, -⟩` from `GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg`.

Use `haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)`. Conclude with `⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩`. Rewrite using `[quasiCompact_iff_compactSpace] choose U hUa hU using T.affine`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X)`.

Use extensionality with `q`. Simplify using `only [Set.mem_univ, Set.mem_iUnion, true_iff]`. Take `⟨c, hcq⟩` from `T.cover ⟨q, hall q⟩`. Conclude with `⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩`. Rewrite using `[hcov]`.

Conclude with `isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact`.
-/
theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  intro X Ω _ ξ κ _ x hall T
  refine ⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩
  · have hQ := (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).1
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]
    intro q
    obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
    obtain ⟨U, hUa, hU⟩ := T.affine c hcq.1
    have hqU : q ∈ U := (hU q).2 ⟨hall q, hcq⟩
    have hg : genPt ξ ∈ U := (hall q).mem_open U.isOpen hqU
    obtain ⟨E, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg
    haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩
  · rw [quasiCompact_iff_compactSpace]
    choose U hUa hU using T.affine
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X) := by
      ext q
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
      exact ⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩
    rw [hcov]
    exact isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact

end GlobalTheory.CompanionTheory.Ar.ChartFType
