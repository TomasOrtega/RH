import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

/- English proof (translation)
Set `x : Presieve.FamilyOfElements (F.obj ⋙ forget _) T.arrows` to `fun V v hv => Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))`. Establish `hres : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), Sec.res g (Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g)`. Introduce `V W v hv g`. Rewrite using `[map_res, freeGen_res]`. Use `congr 2`.

Establish `hcomp : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), Sec.map (σ (g ≫ v) (T.downward_closed hv g)) (freeGen R (yoneda.obj W) W (𝟙 W)) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g)`. Introduce `V W v hv g`. Rewrite using `[← hσ v hv g]`. Express the relevant statement in the definitionally equal form `Sec.map (σ v hv) (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map g)) (freeGen R (yoneda.obj W) W (𝟙 W))) = _`. Rewrite using `[freeGen_map]`.

Use `congr 2`. Establish `hx : x.SieveCompatible`. Introduce `V W v g hv`. Conclude with `(hcomp v hv g).trans (hres v hv g).symm`. Establish `hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _)` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond)`.

Take `⟨s, hs, -⟩` from `hF T hT x ((Presieve.compatible_iff_sieveCompatible x).2 hx)`. Take `⟨t, ht⟩` from `free_exists (R := R) (yoneda.obj S) F (fun U g => Sec.res g (show Sec F S from s)) (fun V U g h => by`. Express the relevant statement in the definitionally equal form `Sec.res g (Sec.res h _) = Sec.res (g ≫ h) _`. Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply])`. Use `⟨t, fun V v hv => ?_⟩` and prove the remaining obligations.

Apply `free_ext` to reduce the goal to its premises. Introduce `U w`. Express the relevant statement in the definitionally equal form `Sec.map t (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map v)) (freeGen R (yoneda.obj V) U w)) = _`. Rewrite using `[freeGen_map, ht, ← hres v hv w]`. Establish `hsv : Sec.res v (show Sec F S from s) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))` using `hs v hv`.

Rewrite using `[← hsv]`. Express the relevant statement in the definitionally equal form `Sec.res (w ≫ v) _ = Sec.res w (Sec.res v _)`. Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem free_hom_glue_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S)
    (hT : T ∈ Scheme.etaleTopology S)
    (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F))
    (hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) :
    ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v),
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by

  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) T.arrows := fun V v hv =>
    Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))

  have hres : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.res g (Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [map_res, freeGen_res]
    congr 2
  have hcomp : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.map (σ (g ≫ v) (T.downward_closed hv g)) (freeGen R (yoneda.obj W) W (𝟙 W)) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [← hσ v hv g]
    change Sec.map (σ v hv) (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map g)) (freeGen R (yoneda.obj W) W (𝟙 W))) = _
    rw [freeGen_map]
    congr 2
  have hx : x.SieveCompatible := by
    intro V W v g hv
    exact (hcomp v hv g).trans (hres v hv g).symm
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond)
  obtain ⟨s, hs, -⟩ := hF T hT x ((Presieve.compatible_iff_sieveCompatible x).2 hx)
  obtain ⟨t, ht⟩ := free_exists (R := R) (yoneda.obj S) F (fun U g => Sec.res g (show Sec F S from s))
    (fun V U g h => by
      change Sec.res g (Sec.res h _) = Sec.res (g ≫ h) _
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply])
  refine ⟨t, fun V v hv => ?_⟩
  apply free_ext
  intro U w
  change Sec.map t (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map v)) (freeGen R (yoneda.obj V) U w)) = _
  rw [freeGen_map, ht, ← hres v hv w]
  have hsv : Sec.res v (show Sec F S from s) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V)) := hs v hv
  rw [← hsv]
  change Sec.res (w ≫ v) _ = Sec.res w (Sec.res v _)
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end GlobalTheory.EtC.Tr

/- English proof (translation)
The claim follows from `@GlobalTheory.EtC.Tr.free_hom_glue_of_covering`.
-/
example : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv :=
  @GlobalTheory.EtC.Tr.free_hom_glue_of_covering
