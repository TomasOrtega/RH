import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.H0Lifting
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

/- English proof (translation)
Set `K` to `DerivedCategory.Q.objPreimage M`. Set `e` to `DerivedCategory.Q.objObjPreimageIso M`. Set `φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K` to `HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)`. Establish `h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫ HomologicalComplex.cyclesMap φ0 0 = 𝟙 _`. Rewrite using `[← cancel_mono (K.iCycles 0)]`.

Simplify using `[φ0]`. Establish `h2 : Epi (HomologicalComplex.cyclesMap φ0 0)` using `epi_of_epi_fac h1`. Establish `h3 : Epi (HomologicalComplex.homologyMap φ0 0)` using `epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)`. Establish `h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0))`. Establish `h` using `(DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0`.

Establish `h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0)` using `h3`. Conclude with `epi_of_epi_fac h.symm`. Use `⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, Functor.map_comp]`. Conclude with `@epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)`.
-/
theorem exists_epi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (M : DerivedCategory A) :
    ∃ (Z : A) (φ : (DerivedCategory.singleFunctor A 0).obj Z ⟶ M),
      Epi ((DerivedCategory.homologyFunctor A 0).map φ) := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  let φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)
  have h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫
      HomologicalComplex.cyclesMap φ0 0 = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp [φ0]
  have h2 : Epi (HomologicalComplex.cyclesMap φ0 0) := epi_of_epi_fac h1
  have h3 : Epi (HomologicalComplex.homologyMap φ0 0) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)
  have h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0)) := by
    have h := (DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0
    have h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0) := h3
    exact epi_of_epi_fac h.symm
  refine ⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)

/- English proof (translation)
Establish `h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a)` using `η.inv.naturality a`. Establish `h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s)` using `η.inv.naturality s`. Establish `h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))`. Rewrite using `[Functor.map_comp]`. Conclude with `(cancel_epi _).1 h3`.
-/
theorem transport {A D : Type*} [Category A] [Category D] (S : A ⥤ D) (H : D ⥤ A) (η : S ⋙ H ≅ 𝟭 A)
    {X Y Z : A} {M : D} (a : X ⟶ Y) (s : X ⟶ Z) (t : H.obj (S.obj Y) ⟶ H.obj M) (φ : S.obj Z ⟶ M)
    (h : a ≫ η.inv.app Y ≫ t = s ≫ η.inv.app Z ≫ H.map φ) : H.map (S.map a) ≫ t = H.map (S.map s ≫ φ) := by
  have h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a) := η.inv.naturality a
  have h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s) := η.inv.naturality s
  have h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))
  rw [Functor.map_comp]
  exact (cancel_epi _).1 h3

abbrev PF (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

def gen {B : Scheme.{0}} (q : ℕ) {U V : B.Etale} (a : V ⟶ U) : ((PF B q).obj U).obj (op V) :=
  ModuleCat.freeMk (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

/- English proof (translation)
The claim follows from `ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _`.
-/
theorem gen_res {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).obj U).map b.op (gen q a) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

/- English proof (translation)
The claim follows from `ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _`.
-/
theorem gen_map {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).map a).app (op W) (gen q b) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

/- English proof (translation)
Use extensionality with `⟨V⟩ : 2`. Use `ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_` and prove the remaining obligations. Introduce and unpack `⟨a⟩`. Express the relevant statement in the definitionally equal form `f.app (op V) (gen q a) = g.app (op V) (gen q a)`. Establish `e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U))` using `by rw [gen_res, Category.comp_id]`.

Rewrite using `[e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]`.
-/
theorem pf_ext {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (f g : (PF B q).obj U ⟶ F) (h : f.app (op U) (gen q (𝟙 U)) = g.app (op U) (gen q (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
  rintro ⟨a⟩
  change f.app (op V) (gen q a) = g.app (op V) (gen q a)
  have e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U)) := by rw [gen_res, Category.comp_id]
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/- English proof (translation)
Set `c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V` to `fun V => ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U)) (TypeCat.ofHom (fun a => F.map a.down.op s))`. Establish `hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s` using `fun V a => ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _`. Use `⟨⟨c, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨V⟩ ⟨W⟩ ⟨b⟩`. Use `ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_` and prove the remaining obligations.

Introduce and unpack `⟨a⟩`. Express the relevant statement in the definitionally equal form `c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))`. Rewrite using `[gen_res, hc, hc, op_comp, Functor.map_comp]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `c (op U) _ = _`.

Rewrite using `[hc]`. Simplify using the standard rewrite rules.
-/
theorem pf_exists {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (s : F.obj (op U)) : ∃ f : (PF B q).obj U ⟶ F, f.app (op U) (gen q (𝟙 U)) = s := by
  let c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U))
      (TypeCat.ofHom (fun a => F.map a.down.op s))
  have hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s := fun V a =>
    ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
    refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
    rintro ⟨a⟩
    change c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))
    rw [gen_res, hc, hc, op_comp, Functor.map_comp]
    rfl
  · change c (op U) _ = _
    rw [hc]
    simp

/- English proof (translation)
Establish `: EssentiallySmall.{1} B.Etale` using `inferInstance`. Establish `hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))` using `hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)`. Establish `hπ : Sheaf.IsLocallySurjective π` using `(Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance`. Set `adj` to `sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))`. Set `t' : (PF B q).obj U ⟶ G.obj` to `adj.homEquiv _ _ t`.

Use `⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩` and prove the remaining obligations. Introduce and unpack `U' a ⟨z, hz⟩`. Take `⟨f, hf⟩` from `pf_exists (F := F.obj) z`. Use `⟨(adj.homEquiv _ F).symm f, ?_⟩` and prove the remaining obligations. Apply `(adj.homEquiv _ _).injective` to reduce the goal to its premises.

Rewrite using `[Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]`. Apply `pf_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))`. Rewrite using `[hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]`.
-/
theorem loc_lift {B : Scheme.{0}} {q : ℕ} {F G : SShv B q} (π : F ⟶ G) [Epi π] (U : B.Etale)
    (t : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U) ⟶ G) :
    Cov U (fun U' a => ∃ s : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U') ⟶ F,
      (presheafToSheaf (EtTop B) _).map ((PF B q).map a) ≫ t = s ≫ π) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  have hπ : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  let adj := sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let t' : (PF B q).obj U ⟶ G.obj := adj.homEquiv _ _ t
  refine ⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩
  rintro U' a ⟨z, hz⟩
  obtain ⟨f, hf⟩ := pf_exists (F := F.obj) z
  refine ⟨(adj.homEquiv _ F).symm f, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply pf_ext
  change t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))
  rw [hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]

/- English proof (translation)
Introduce `B q M U t`. Take `⟨Z, φ, hφ⟩` from `exists_epi M`. Set `η` to `DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0`. Set `X : B.Etale ⥤ SShv B q` to `PF B q ⋙ presheafToSheaf (EtTop B) _`. Set `π : Z ⟶ (H0 B q).obj M` to `η.inv.app Z ≫ (H0 B q).map φ`.

Establish `hπ : Epi π` using `epi_comp _ _`. Set `t0 : X.obj U ⟶ (H0 B q).obj M` to `η.inv.app (X.obj U) ≫ t`. Use `(loc_lift π U t0).mono ?_` and prove the remaining obligations. Introduce and unpack `U' a ⟨s, hs⟩`. Use `⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩` and prove the remaining obligations.

Conclude with `transport _ _ η (X.map a) s t φ hs`.
-/
theorem etale_sheaf_epi_lifts_degree_zero_derived_maps_locally : EtaleDerivedDegreeZeroHomologyLocallyLifts := by
  intro B q M U t
  obtain ⟨Z, φ, hφ⟩ := exists_epi M
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0
  let X : B.Etale ⥤ SShv B q := PF B q ⋙ presheafToSheaf (EtTop B) _
  let π : Z ⟶ (H0 B q).obj M := η.inv.app Z ≫ (H0 B q).map φ
  have hπ : Epi π := epi_comp _ _
  let t0 : X.obj U ⟶ (H0 B q).obj M := η.inv.app (X.obj U) ≫ t
  refine (loc_lift π U t0).mono ?_
  rintro U' a ⟨s, hs⟩
  refine ⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩
  exact transport _ _ η (X.map a) s t φ hs

end LateralTheory.E.H0Lifting
