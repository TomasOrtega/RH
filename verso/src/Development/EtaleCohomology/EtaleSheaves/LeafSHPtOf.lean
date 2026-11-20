import Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `B U x J _ _ D c V a e t ht hcof`. Take `⟨j0⟩` from `(inferInstance : Nonempty J)`. Prove the components needed by the constructor for the conclusion. Introduce `O hxO`. Establish `hU : Etale U.hom` using `U.prop`.

Set `U' : B.Etale` to `MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by`. Express the relevant statement in the definitionally equal form `Etale (O.ι ≫ U.hom)`. Use the proof step `infer_instance)`. Set `b : U' ⟶ U` to `MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl`. Take `⟨j, g, hg⟩` from `hcof U' b ⟨x, hxO⟩ rfl`.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[← ht j, ← hg]`. Establish `: Set.range (O.ι) ⊆ (O : Set U.left)` using `by rw [Scheme.Opens.range_ι]`. Apply `this` to reduce the goal to its premises. Conclude with `⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by rfl⟩`.

Introduce `S hS`. Take `⟨𝒰, _, h, hU⟩` from `(Scheme.mem_smallGrothendieckTopology _ _).1 hS`. Take `⟨i, ⟨u, hu⟩⟩` from `((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x`. Set `fi : (𝒰.X i).asOverProp B (h i) ⟶ U` to `(𝒰.f i).asOverProp B`. Use `⟨_, fi, hU _ _ ⟨i⟩, ?_⟩` and prove the remaining obligations.

Take `⟨j, g, hg⟩` from `hcof _ fi u hu`. Conclude with `⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by`. Rewrite using `[Category.assoc, Category.assoc, hg, ht j]⟩`.
-/
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop`.
-/
theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
