import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

namespace GenPf

variable (R : Type) [CommRing R]

abbrev mk {P : PSh} {U : Scheme.{0}} (x : P.obj (op U)) : ((freeP R).obj P).obj (op U) :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj (op U))) (ULift.up x)

/- English proof (translation)
Simplify using `only [freeP]`. Conclude with `Finsupp.mapDomain_single`.
-/
theorem freePresheaf_obj_map_mk (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (mk R x) = mk R (P.map g.op x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

/- English proof (translation)
Simplify using `only [freeP]`. Conclude with `Finsupp.mapDomain_single`.
-/
theorem freePresheaf_map_app_mk {P P' : PSh} (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (mk R x) = mk R (f.app (op U) x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

/- English proof (translation)
Establish `h` using `congrArg (fun k => ModuleCat.Hom.hom k (mk R x)) ((toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P)).naturality g.op)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at h`. Rewrite `h` using `[freePresheaf_obj_map_mk]`. Conclude with `h.symm`.
-/
theorem part1 (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom k (mk R x))
    ((toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_obj_map_mk] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `congrArg (fun k => ModuleCat.Hom.hom (NatTrans.app k (op U)) (mk R x)) (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))`. Simplify using `only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h`. Rewrite `h` using `[freePresheaf_map_app_mk]`. Conclude with `h.symm`.
-/
theorem part2 (P P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom (NatTrans.app k (op U)) (mk R x))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_map_app_mk] at h
  exact h.symm

def adjE (P : PSh) (G : Shv R) : ((free R).obj P ⟶ G) ≃ ((freeP R).obj P ⟶ G.obj) :=
  (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv ((freeP R).obj P) G

/- English proof (translation)
The claim follows from `Adjunction.homEquiv_unit _ _ _ _`.
-/
theorem adjE_apply (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) :
    adjE R P G φ = toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P) ≫ φ.hom :=
  Adjunction.homEquiv_unit _ _ _ _

/- English proof (translation)
Rewrite using `[adjE_apply]`. Both sides reduce to the same expression.
-/
theorem adjE_gen (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    ((adjE R P G φ).app (op U)).hom (mk R x) = Sec.map φ (freeGen R P U x) := by
  rw [adjE_apply]; rfl

/- English proof (translation)
Apply `(adjE R P G).injective` to reduce the goal to its premises. Use `NatTrans.ext (funext fun U => ?_)` and prove the remaining obligations. Take `⟨U⟩` from `U`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨y⟩`.

Conclude with `(adjE_gen R P G φ U y).trans ((h U y).trans (adjE_gen R P G ψ U y).symm)`.
-/
theorem part3 (P : PSh) (G : Shv R) (φ ψ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) :
    φ = ψ := by
  apply (adjE R P G).injective
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  apply ModuleCat.free_hom_ext
  rintro ⟨y⟩
  exact (adjE_gen R P G φ U y).trans ((h U y).trans (adjE_gen R P G ψ U y).symm)

def descP (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun y => t U.unop (ULift.down y))
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    rintro ⟨y⟩
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    erw [freePresheaf_obj_map_mk R P g.unop y, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ht g.unop y).symm

/- English proof (translation)
Simplify using `only [descP]`. Conclude with `ModuleCat.freeDesc_apply _ _`.
-/
theorem freePresheafDesc_app_mk (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((descP R P G t ht).app (op U)).hom (mk R x) = t U x := by
  simp only [descP]
  exact ModuleCat.freeDesc_apply _ _

/- English proof (translation)
Use `⟨(adjE R P G).symm (descP R P G t ht), fun U x => ?_⟩` and prove the remaining obligations. Rewrite using `[← adjE_gen, Equiv.apply_symm_apply, freePresheafDesc_app_mk]`.
-/
theorem part4 (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x := by
  refine ⟨(adjE R P G).symm (descP R P G t ht), fun U x => ?_⟩
  rw [← adjE_gen, Equiv.apply_symm_apply, freePresheafDesc_app_mk]

end GenPf

/- English proof (translation)
Introduce `R _ P`. Conclude with `⟨fun g x => GenPf.part1 R P g x, fun P' f U x => GenPf.part2 R P P' f U x, fun G φ ψ h => GenPf.part3 R P G φ ψ h, fun G t ht => GenPf.part4 R P G t ht⟩`.
-/
theorem LeafGen_of : LeafGen := by
  intro R _ P
  exact ⟨fun g x => GenPf.part1 R P g x, fun P' f U x => GenPf.part2 R P P' f U x,
    fun G φ ψ h => GenPf.part3 R P G φ ψ h, fun G t ht => GenPf.part4 R P G t ht⟩

end LateralTheory.CohomologicalPurity.Bd
