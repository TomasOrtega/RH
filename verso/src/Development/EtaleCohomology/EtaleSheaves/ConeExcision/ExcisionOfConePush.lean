import Development.EtaleCohomology.EtaleSheaves.ConeExcision

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExcPf

variable (R : Type) [CommRing R]

/- English proof (translation)
Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `T`. Establish `hg : Function.Injective (g.app T)` using `(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app g).1 ‹_› T)`. Rewrite using `[ModuleCat.mono_iff_injective]`. Express the relevant statement in the definitionally equal form `Function.Injective (Finsupp.mapDomain (ULift.map (g.app T)))`.

Conclude with `Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))`.
-/
theorem mono_freePresheaf_map {X Y : PSh} (g : X ⟶ Y) [Mono g] : Mono ((freeP R).map g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  have hg : Function.Injective (g.app T) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app g).1 ‹_› T)
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (Finsupp.mapDomain (ULift.map (g.app T)))
  exact Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))

/- English proof (translation)
Use `mono_freePresheaf_map R g` as an intermediate fact. Express the relevant statement in the definitionally equal form `Mono ((presheafToSheaf _ _).map ((freeP R).map g))`. Use `infer_instance`.
-/
theorem free_mono {X Y : PSh} (g : X ⟶ Y) [Mono g] : Mono ((free R).map g) := by
  have := mono_freePresheaf_map R g
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

/- English proof (translation)
Introduce `R _ E E' f _ n`. Establish `hlev : ∀ p : ℕ, Mono (f.app (op (SimplexCategory.mk p)))` using `fun p => (NatTrans.mono_iff_mono_app f).1 ‹_› _`. Express the relevant statement in the definitionally equal form `Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f n)`. Distinguish the cases in `h : ∃ p : ℕ, ComplexShape.embeddingDownNat.f p = n`. Take `⟨p, hp⟩` from `h`.

Rewrite using `[HomologicalComplex.extendMap_f _ _ hp]`. Establish `: Mono (((chainsN R).map f).f p)`. Express the relevant statement in the definitionally equal form `Mono ((free R).map (f.app (op (SimplexCategory.mk p))))`. Conclude with `free_mono R _`. Use `infer_instance`.

Simplify using `only [not_exists] at h`. Establish `hz` using `HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat n h`. Conclude with `⟨fun g k _ => hz.eq_of_tgt g k⟩`.
-/
theorem LeafMono_pf : LeafMono := by
  intro R _ E E' f _ n
  have hlev : ∀ p : ℕ, Mono (f.app (op (SimplexCategory.mk p))) := fun p =>
    (NatTrans.mono_iff_mono_app f).1 ‹_› _
  change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f n)
  by_cases h : ∃ p : ℕ, ComplexShape.embeddingDownNat.f p = n
  · obtain ⟨p, hp⟩ := h
    rw [HomologicalComplex.extendMap_f _ _ hp]
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((free R).map (f.app (op (SimplexCategory.mk p))))
      exact free_mono R _
    infer_instance
  · simp only [not_exists] at h
    have hz := HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat n h
    exact ⟨fun g k _ => hz.eq_of_tgt g k⟩

/- English proof (translation)
The claim follows from `LeafExc_of hRel LeafMono_pf hSq hCone`.
-/
theorem excision_of_conePush (hRel : LateralTheory.E.t_E6Cut.LeafRel) (hSq : LeafSq) (hCone : LeafConePush) :
    LateralTheory.E.t_E6Cut.LeafExc :=
  LeafExc_of hRel LeafMono_pf hSq hCone

end LateralTheory.E.LeafExcPf
