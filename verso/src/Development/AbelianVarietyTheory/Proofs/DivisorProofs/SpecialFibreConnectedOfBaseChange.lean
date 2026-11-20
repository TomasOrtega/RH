import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibSurj

open IsLocalRing

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`.
-/
theorem spec_square :
    Spec.map (CommRingCat.ofHom (residue O)) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ResidueField.map φ)) ≫ Spec.map (CommRingCat.ofHom (residue V)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

noncomputable def fibMap :
    pullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (residue O))) ⟶
      pullback s (Spec.map (CommRingCat.ofHom (residue V))) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (ResidueField.map φ))) (by
      simp only [Category.assoc]
      rw [← spec_square, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem fibMap_fst : fibMap φ s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem fibMap_snd : fibMap φ s ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (ResidueField.map φ)) :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Establish `hL` using `IsPullback.of_hasPullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (residue O)))`. Establish `hR` using `IsPullback.of_hasPullback s (Spec.map (CommRingCat.ofHom φ))`. Establish `hOut` using `hL.paste_horiz hR`. Rewrite `hOut` using `[← fibMap_fst, spec_square]`. Conclude with `IsPullback.of_right hOut (fibMap_snd φ s) (IsPullback.of_hasPullback _ _)`.
-/
theorem fibMap_isPullback :
    IsPullback (fibMap φ s) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
  have hL := IsPullback.of_hasPullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))
    (Spec.map (CommRingCat.ofHom (residue O)))
  have hR := IsPullback.of_hasPullback s (Spec.map (CommRingCat.ofHom φ))
  have hOut := hL.paste_horiz hR
  rw [← fibMap_fst, spec_square] at hOut
  exact IsPullback.of_right hOut (fibMap_snd φ s) (IsPullback.of_hasPullback _ _)

/- English proof (translation)
Establish `hψ : Surjective (Spec.map (CommRingCat.ofHom (ResidueField.map φ)))`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨y⟩` from `(inferInstance : Nonempty (Spec (CommRingCat.of (ResidueField O))))`. Conclude with `⟨y, Subsingleton.elim _ _⟩`.

Conclude with `MorphismProperty.of_isPullback (fibMap_isPullback φ s).flip hψ`.
-/
theorem fibMap_surjective : Surjective (fibMap φ s) := by
  have hψ : Surjective (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (ResidueField O))))
    exact ⟨y, Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback (fibMap_isPullback φ s).flip hψ

end

/- English proof (translation)
Introduce `V _ _ _ O _ _ _ φ hφ X s hc`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre at hc ⊢`. Conclude with `(fibMap_surjective φ s).surj.connectedSpace (fibMap φ s).continuous`.
-/
theorem fibre_connected_of_base_change :
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by
  intro V _ _ _ O _ _ _ φ hφ X s hc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre at hc ⊢
  exact (fibMap_surjective φ s).surj.connectedSpace (fibMap φ s).continuous

end GlobalTheory.FibSurj
