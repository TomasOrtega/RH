import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEtStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `S O _ s hs`. Take `⟨_, A, _, _, j, hj, hind, rfl⟩` from `hs`. Take `⟨J, _, _, D, ι, ⟨hc⟩, het⟩` from `GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hind`. Set `G : Jᵒᵖ ⥤ Over S` to `{ obj := fun k => Over.mk (Spec.map (D.obj k.unop).hom ≫ j) map := fun {k l} f => Over.homMk (Spec.map (D.map f.unop).right) (by dsimp`. Rewrite using `[← Category.assoc, ← Spec.map_comp, Under.w])`.

Use `map_id := fun k => by ext1; simp`. Use `map_comp := fun f g => by ext1; simp [Spec.map_comp] }`. Set `π : (Functor.const Jᵒᵖ).obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j)) ⟶ G` to `{ app := fun k => Over.homMk (Spec.map (ι.app k.unop).right) (by dsimp [G]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, Under.w (ι.app k.unop)]`. Use the proof step `rfl)`.

Use `naturality := fun k l f => by ext1`. Express the relevant statement in the definitionally equal form `(𝟙 _ ≫ Spec.map (ι.app l.unop).right) = Spec.map (ι.app k.unop).right ≫ Spec.map (D.map f.unop).right`. Rewrite using `[Category.id_comp, ← Spec.map_comp]`. Use `congr 1`. Use `congrArg (fun m => Under.Hom.right m) (ι.naturality f.unop)` as an intermediate fact.

Simplify using `only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Under.comp_right] at this`. Conclude with `this.symm }`. Use `haveI : IsConnected J := IsFiltered.isConnected J`. Use `haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ`. Use `⟨Jᵒᵖ, inferInstance, inferInstance, G, π, ⟨?_⟩, fun k => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Apply `isLimitOfReflects (Over.forget S)` to reduce the goal to its premises. Establish `h1` using `isColimitOfPreserves (Under.forget (CommRingCat.of A)) hc`. Establish `h2` using `isLimitOfPreserves Scheme.Spec h1.op`. Conclude with `h2`. Simplify using `[G]`.

Use `infer_instance`. Simplify using `[G]`. Establish `: Etale (Spec.map (D.obj k.unop).hom)` using `(HasRingHomProperty.Spec_iff (P := @Etale)).2 (het k.unop)`. Use `infer_instance`.
-/
theorem exists_cofiltered_limit_affine_etale_of_isStalk : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  intro S O _ s hs
  obtain ⟨_, A, _, _, j, hj, hind, rfl⟩ := hs
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hind
  let G : Jᵒᵖ ⥤ Over S :=
    { obj := fun k => Over.mk (Spec.map (D.obj k.unop).hom ≫ j)
      map := fun {k l} f => Over.homMk (Spec.map (D.map f.unop).right) (by
        dsimp
        rw [← Category.assoc, ← Spec.map_comp, Under.w])
      map_id := fun k => by ext1; simp
      map_comp := fun f g => by ext1; simp [Spec.map_comp] }
  let π : (Functor.const Jᵒᵖ).obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j)) ⟶ G :=
    { app := fun k => Over.homMk (Spec.map (ι.app k.unop).right) (by
        dsimp [G]
        rw [← Category.assoc, ← Spec.map_comp, Under.w (ι.app k.unop)]
        rfl)
      naturality := fun k l f => by
        ext1
        change (𝟙 _ ≫ Spec.map (ι.app l.unop).right) = Spec.map (ι.app k.unop).right ≫ Spec.map (D.map f.unop).right
        rw [Category.id_comp, ← Spec.map_comp]
        congr 1
        have := congrArg (fun m => Under.Hom.right m) (ι.naturality f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Under.comp_right] at this
        exact this.symm }
  haveI : IsConnected J := IsFiltered.isConnected J
  haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G, π, ⟨?_⟩, fun k => ⟨?_, ?_⟩⟩
  · apply isLimitOfReflects (Over.forget S)
    have h1 := isColimitOfPreserves (Under.forget (CommRingCat.of A)) hc
    have h2 := isLimitOfPreserves Scheme.Spec h1.op
    exact h2
  · dsimp [G]; infer_instance
  · dsimp [G]
    have : Etale (Spec.map (D.obj k.unop).hom) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (het k.unop)
    infer_instance

end GlobalTheory.EtC
