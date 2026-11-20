import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPfB

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

section gen
variable {C : Type*} [Category C] {S : Type*} [Ring S] {F G : Cᵒᵖ ⥤ ModuleCat.{1} S} (φ : F ⟶ G) {X : C}

/- English proof (translation)
Introduce and unpack `Y i ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩`. Conclude with `⟨t + t', by rw [map_add, map_add, ht, ht']⟩`.
-/
theorem pl_imageSieve_add (s s' : G.obj (op X)) :
    Presheaf.imageSieve φ s ⊓ Presheaf.imageSieve φ s' ≤ Presheaf.imageSieve φ (s + s') := by
  rintro Y i ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
  exact ⟨t + t', by rw [map_add, map_add, ht, ht']⟩

/- English proof (translation)
Introduce and unpack `Y i ⟨t, ht⟩`. Conclude with `⟨r • t, by rw [map_smul, map_smul, ht]⟩`.
-/
theorem pl_imageSieve_smul (r : S) (s : G.obj (op X)) :
    Presheaf.imageSieve φ s ≤ Presheaf.imageSieve φ (r • s) := by
  rintro Y i ⟨t, ht⟩
  exact ⟨r • t, by rw [map_smul, map_smul, ht]⟩

/- English proof (translation)
Use extensionality with `Y i`. Simplify using `only [Sieve.top_apply, iff_true]`. Conclude with `⟨0, by rw [map_zero, map_zero]⟩`.
-/
theorem pl_imageSieve_zero : Presheaf.imageSieve φ (0 : G.obj (op X)) = ⊤ := by
  ext Y i
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩
end gen

/- English proof (translation)
Break down `H with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases. Use `⟨NatTrans.app (biprod.inl : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _ (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩` and prove the remaining obligations. Establish `key` using `congrArg (fun (k : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z)) (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y))) (biprod.inl_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))`. Use `Eq.trans key ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)`.

Use `(ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)` and prove the remaining obligations. Conclude with `congrArg ModuleCat.freeMk (congrArg ULift.up hy)`. Use `⟨NatTrans.app (biprod.inr : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _ (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩` and prove the remaining obligations. Establish `key` using `congrArg (fun (k : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z)) (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y))) (biprod.inr_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))`. Use `Eq.trans key ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)`. Use `(ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)` and prove the remaining obligations. Conclude with `congrArg ModuleCat.freeMk (congrArg ULift.up hy)`.
-/
theorem pl_hit (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : SimplexCategoryᵒᵖ)
    {X Z : Scheme.{0}} (x : (E.obj n).obj (op X)) (h : Z ⟶ X)
    (H : (∃ y, (f.app n).app (op Z) y = (E.obj n).map h.op x) ∨ (∃ y, (g.app n).app (op Z) y = (E.obj n).map h.op x)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) h := by
  rcases H with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine ⟨NatTrans.app (biprod.inl : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inl_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)
  · refine ⟨NatTrans.app (biprod.inr : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inr_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)

/- English proof (translation)
Take `⟨ι, O, hO, hi⟩` from `hL n X x`. Establish `hO' : TopologicalSpace.IsOpenCover O` using `hO`. Apply `Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises. Use `GrothendieckTopology.superset_covering _ ?_ (X.openCoverOfIsOpenCover O hO').mem_grothendieckTopology` and prove the remaining obligations. Use `(Sieve.generate_le_iff _ _).2 ?_` and prove the remaining obligations.

Introduce and unpack `Y _ ⟨i⟩`. Conclude with `pl_hit R f g n x (O i).ι (hi i)`.
-/
theorem pl_gen (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hL : LocCov f g) (n : SimplexCategoryᵒᵖ)
    (X : Scheme.{0}) (x : (E.obj n).obj (op X)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) ∈ Scheme.etaleTopology.{0} X := by
  obtain ⟨ι, O, hO, hi⟩ := hL n X x
  have hO' : TopologicalSpace.IsOpenCover O := hO
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (X.openCoverOfIsOpenCover O hO').mem_grothendieckTopology
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro Y _ ⟨i⟩
  exact pl_hit R f g n x (O i).ι (hi i)

/- English proof (translation)
Introduce `R _ U V E f g hL n`. Prove the components needed by the constructor for the conclusion. Introduce `X s`. Express the relevant statement in the definitionally equal form `(ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) at s`. Proceed by induction on `s using Finsupp.induction_linear with`.

Consider the case `zero`. Conclude with `GrothendieckTopology.superset_covering _ (pl_imageSieve_zero _).ge (GrothendieckTopology.top_mem _ _)`. Consider the case `add a b ha hb`. Conclude with `GrothendieckTopology.superset_covering _ (pl_imageSieve_add _ _ _) (GrothendieckTopology.intersection_covering _ ha hb)`. Consider the case `single a r`.

Establish `e : (Finsupp.single a r : ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) = r • ModuleCat.freeMk (R` using `ULift.{1} R) a := by`. Conclude with `(Finsupp.smul_single_one a r).symm`. Establish `h` using `GrothendieckTopology.superset_covering _ (pl_imageSieve_smul _ r _) (pl_gen R f g hL n X a.down)`. Use `h using 2` and compare the differences between its conclusion and the goal. Conclude with `congrArg (Presheaf.imageSieve _) e`.
-/
theorem LeafPLoc_of : LeafPLoc := by
  intro R _ U V E f g hL n
  constructor
  intro X s
  change (ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) at s
  induction s using Finsupp.induction_linear with
  | zero =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_zero _).ge (GrothendieckTopology.top_mem _ _)
  | add a b ha hb =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_add _ _ _)
      (GrothendieckTopology.intersection_covering _ ha hb)
  | single a r =>
    have e : (Finsupp.single a r : ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) =
        r • ModuleCat.freeMk (R := ULift.{1} R) a := by
      exact (Finsupp.smul_single_one a r).symm
    have h := GrothendieckTopology.superset_covering _ (pl_imageSieve_smul _ r _) (pl_gen R f g hL n X a.down)
    convert h using 2
    exact congrArg (Presheaf.imageSieve _) e

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
