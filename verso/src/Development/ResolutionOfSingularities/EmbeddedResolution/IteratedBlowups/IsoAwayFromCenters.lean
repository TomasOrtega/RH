import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The restriction of the composite to the target open factors as the restriction of the first morphism to the inverse image open followed by the restriction of the second morphism. Both factors are isomorphisms, so their composite is an isomorphism.
-/
private theorem isIso_restrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have := h1
  have := h2
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := inferInstance
  rw [morphismRestrict_comp]
  exact h

/- English proof (authored)
Induct on the stage. Initially projection to the base is the given isomorphism, whose restriction remains an isomorphism. At a successor, the center misses the inverse image of the chosen open because all center points project into the prescribed disjoint set. Hence the restricted center ideal is the unit ideal and the restricted blowup is an isomorphism. Compose this with the preceding restricted projection, which is an isomorphism by induction.
-/
private theorem isIso_restrict_projectionToBase_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S)
    (i : ℕ) (hi : i ≤ s.length) :
    IsIso (s.projectionToBase i ∣_ U) := by
  revert hi
  induction i with
  | zero =>
    intro _
    show IsIso (s.projectionToBase 0 ∣_ U)
    have h0 : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0).op = 𝟙 (op (0 : ℕ)) := rfl
    have : IsIso (s.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h0, CategoryTheory.Functor.map_id,
        Category.id_comp]
      infer_instance
    infer_instance
  | succ i ih =>
    intro hi
    have hi' : i < s.length := hi
    have h2 : IsIso (s.projectionToBase i ∣_ U) := ih (Nat.le_of_succ_le hi)
    have hcomp : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) :=
      s.transitionMap_comp_projectionToBase (Nat.le_succ i)
    have hb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi'
    have hres := hb.restrict (s.projectionToBase i ⁻¹ᵁ U)
    have htop : (s.center i).comap (s.projectionToBase i ⁻¹ᵁ U).ι = ⊤ := by
      apply Blowup.comap_eq_top_of_notMem_support
      intro x hx
      have h1 := hs i hi' ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) hx
      have hxV : (s.projectionToBase i ⁻¹ᵁ U).ι.base x
          ∈ ((s.projectionToBase i ⁻¹ᵁ U : (s.schemeAt i).Opens) : Set (s.schemeAt i)) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self x
      have h2' : (s.projectionToBase i).base ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) ∈ (U : Set X) := hxV
      exact Set.disjoint_left.mp hU h2' h1
    rw [htop] at hres
    have h1 : IsIso (s.transitionMapSucc i ∣_ (s.projectionToBase i ⁻¹ᵁ U)) := hres.isIso_of_top
    have key : IsIso ((s.transitionMapSucc i ≫ s.projectionToBase i) ∣_ U) :=
      isIso_restrict_comp (s.transitionMapSucc i) (s.projectionToBase i) U h1 h2
    rw [hcomp] at key
    exact key

/- English proof (authored)
The last structural map is the projection at the final stage. Apply the stagewise isomorphism result there to the given disjoint open.
-/
theorem isIso_restrict_lastStructMap_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S) :
    IsIso (s.lastStructMap ∣_ U) := by
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase]
  exact isIso_restrict_projectionToBase_of_centersLieOver s S U hU hs s.length le_rfl

/- English proof (authored)
The smooth locus is disjoint from its complement. All centers lie over that complement by hypothesis, so the last structural map restricts to an isomorphism over the smooth locus.
-/
theorem isIso_restrict_lastStructMap_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  refine isIso_restrict_lastStructMap_of_centersLieOver s _ f.smoothLocus ?_ hs
  show Disjoint (f.smoothLocus : Set X) ((f.smoothLocus : Set X)ᶜ)
  exact disjoint_compl_right

end FunctorialResolution.EmbeddedResolution
