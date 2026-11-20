import Development.EtaleCohomology.EtaleSheaves.LocalSlices.LocSliceOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PullMonoPf

universe u
variable {X : Scheme.{0}} (V : Scheme.{0})

abbrev KK := CostructuredArrow (Over.forget X).op (op V)

def pt (c : KK (X := X) V) : ULift.{1} (V ⟶ X) := ⟨c.hom.unop ≫ c.left.unop.hom⟩

/- English proof (translation)
Establish `h2 : (c.hom.unop : V ⟶ c.left.unop.left) = (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ g.left.unop.left` using `(congrArg Quiver.Hom.unop (CostructuredArrow.w g)).symm`. Establish `h3` using `congrArg (fun k => (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ k) (Over.w g.left.unop)`. Simplify using `only at h3`. Unfold `pt`. Use `congr 1`.

Conclude with `(congrArg (· ≫ c.left.unop.hom) h2).trans ((Category.assoc _ _ _).trans h3)`.
-/
lemma pt_eq {c c' : KK (X := X) V} (g : c ⟶ c') : pt V c = pt V c' := by
  have h2 : (c.hom.unop : V ⟶ c.left.unop.left) = (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ g.left.unop.left :=
    (congrArg Quiver.Hom.unop (CostructuredArrow.w g)).symm
  have h3 := congrArg (fun k => (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ k) (Over.w g.left.unop)
  simp only at h3
  unfold pt; congr 1
  exact (congrArg (· ≫ c.left.unop.hom) h2).trans ((Category.assoc _ _ _).trans h3)

def P : KK (X := X) V ⥤ Discrete (ULift.{1} (V ⟶ X)) where
  obj c := ⟨pt V c⟩
  map g := Discrete.eqToHom (pt_eq V g)

def Iota : Discrete (ULift.{1} (V ⟶ X)) ⥤ KK (X := X) V :=
  Discrete.functor fun x => CostructuredArrow.mk (Y := op (Over.mk x.down)) (𝟙 (op V))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b`. Apply `CostructuredArrow.hom_ext` to reduce the goal to its premises. Apply `Quiver.Hom.unop_inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `ha` using `congrArg Quiver.Hom.unop (CostructuredArrow.w a)`. Establish `hb` using `congrArg Quiver.Hom.unop (CostructuredArrow.w b)`. Conclude with `((Category.id_comp _).symm.trans ha).trans ((Category.id_comp _).symm.trans hb).symm`.
-/
lemma sub (c : KK (X := X) V) (x) : Subsingleton (c ⟶ (Iota V).obj x) := by
  constructor
  intro a b
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  have ha := congrArg Quiver.Hom.unop (CostructuredArrow.w a)
  have hb := congrArg Quiver.Hom.unop (CostructuredArrow.w b)
  exact ((Category.id_comp _).symm.trans ha).trans ((Category.id_comp _).symm.trans hb).symm

/- English proof (translation)
Take `⟨⟨x⟩⟩` from `x`. Apply `ULift.ext` to reduce the goal to its premises. Conclude with `Category.id_comp x`.
-/
lemma pt_iota (x : Discrete (ULift.{1} (V ⟶ X))) : pt V ((Iota V).obj x) = x.as := by
  obtain ⟨⟨x⟩⟩ := x
  apply ULift.ext
  exact Category.id_comp x

def uH (c : KK (X := X) V) : c ⟶ (Iota V).obj ⟨pt V c⟩ :=
  CostructuredArrow.homMk
    (Over.homMk (U := Over.mk (pt V c).down) (V := c.left.unop) (c.hom.unop : V ⟶ c.left.unop.left) rfl).op
    (by apply Quiver.Hom.unop_inj; exact Category.id_comp _)

def adj : P V ⊣ Iota (X := X) V := Adjunction.mkOfHomEquiv
  { homEquiv := fun c x =>
      { toFun := fun e => uH V c ≫ (Iota V).map e
        invFun := fun g => Discrete.eqToHom ((pt_eq V g).trans (pt_iota V x))
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => (sub V c x).elim _ _ }
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun {c} {_} {x'} _ _ => (sub V c x').elim _ _ }

instance : (Iota (X := X) V).Final := Functor.final_of_adjunction (adj V)

/- English proof (translation)
Establish `h : colimit.pre F (Iota V) ≫ colimMap φ = colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V)`. Apply `colimit.hom_ext` to reduce the goal to its premises. Introduce `j`. Simplify using the standard rewrite rules. Establish `hm : Mono (colimMap (Functor.whiskerLeft (Iota V) φ))`.

Establish `: Mono (Functor.whiskerLeft (Iota V) φ)`. Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `k`. Use `dsimp`. Use `infer_instance`.

Use `haveI : PreservesFiniteLimits (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _) := inferInstance`. Use `haveI : (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).PreservesMonomorphisms := inferInstance`. Conclude with `(colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).map_mono (Functor.whiskerLeft (Iota V) φ)`. Establish `: colimMap φ = inv (colimit.pre F (Iota V)) ≫ colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V)`. Rewrite using `[← h, IsIso.inv_hom_id_assoc]`.

Rewrite using `[this]`. Use `infer_instance`.
-/
lemma colimMono {S : Type 1} [Ring S] {F F' : KK (X := X) V ⥤ ModuleCat.{1} S} [HasColimit F] [HasColimit F']
    (φ : F ⟶ F') [Mono φ] : Mono (colimMap φ) := by
  have h : colimit.pre F (Iota V) ≫ colimMap φ = colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V) := by
    apply colimit.hom_ext; intro j; simp
  have hm : Mono (colimMap (Functor.whiskerLeft (Iota V) φ)) := by
    have : Mono (Functor.whiskerLeft (Iota V) φ) := by
      rw [NatTrans.mono_iff_mono_app]; intro k; dsimp; infer_instance
    haveI : PreservesFiniteLimits (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _) := inferInstance
    haveI : (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).PreservesMonomorphisms :=
      inferInstance
    exact (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).map_mono (Functor.whiskerLeft (Iota V) φ)
  have : colimMap φ = inv (colimit.pre F (Iota V)) ≫ colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V) := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [this]; infer_instance

/- English proof (translation)
Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `V`. Establish `key : ((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom = ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom ≫ colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f)`. Use `(Iso.inv_comp_eq _).mp ?_` and prove the remaining obligations. Apply `colimit.hom_ext` to reduce the goal to its premises.

Introduce `j`. Use `erw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, ι_colimMap]`. Establish `hn` using `((Over.forget X).op.lan.map f).naturality j.hom`. Establish `hu` using `congrArg (fun t => t.app j.left) ((Over.forget X).op.lanUnit.naturality f)`. Simplify using `[Functor.lanUnit] at hu hn`.

Establish `hu' : ((Over.forget X).op.leftKanExtensionUnit F).app j.left ≫ ((Over.forget X).op.lan.map f).app ((Over.forget X).op.obj j.left) = f.app j.left ≫ ((Over.forget X).op.leftKanExtensionUnit F').app j.left` using `hu.symm`. Use `erw [reassoc_of% hn]`. Conclude with `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu')).trans ((Category.assoc _ _ _).trans (congrArg (f.app j.left ≫ ·) (Functor.ι_leftKanExtensionObjIsoColimit_hom (Over.forget X).op F' V j)))`. Establish `hm : Mono (colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f))`. Establish `: Mono (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f)`.

Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `k`. Use `dsimp`. Use `infer_instance`. Conclude with `colimMono (X := X) V.unop _`.

Establish `: Mono (((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom)`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `Z a b h`. Establish `h2 : a ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom = b ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom` using `hm.right_cancellation _ _ ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))`.

Establish `h3` using `congrArg (· ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv) h2`. Establish `hc : ∀ c : Z ⟶ _, (c ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom) ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv = c` using `fun c => (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id c))`. Conclude with `(hc a).symm.trans (h3.trans (hc b))`. Conclude with `mono_of_mono _ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom`.
-/
lemma lanMono (R : Type) [CommRing R] (X : Scheme.{0}) :
    ((Over.forget X).op.lan : ((Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).PreservesMonomorphisms where
  preserves {F F'} f _ := by
    rw [NatTrans.mono_iff_mono_app]; intro V
    have key : ((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom =
        ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom ≫
          colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f) := by
      refine (Iso.inv_comp_eq _).mp ?_
      apply colimit.hom_ext; intro j
      erw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, ι_colimMap]
      have hn := ((Over.forget X).op.lan.map f).naturality j.hom
      have hu := congrArg (fun t => t.app j.left) ((Over.forget X).op.lanUnit.naturality f)
      dsimp [Functor.lanUnit] at hu hn
      have hu' : ((Over.forget X).op.leftKanExtensionUnit F).app j.left ≫
          ((Over.forget X).op.lan.map f).app ((Over.forget X).op.obj j.left) =
          f.app j.left ≫ ((Over.forget X).op.leftKanExtensionUnit F').app j.left := hu.symm
      erw [reassoc_of% hn]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu')).trans ((Category.assoc _ _ _).trans
        (congrArg (f.app j.left ≫ ·) (Functor.ι_leftKanExtensionObjIsoColimit_hom (Over.forget X).op F' V j)))
    have hm : Mono (colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f)) := by
      have : Mono (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f) := by
        rw [NatTrans.mono_iff_mono_app]; intro k; dsimp; infer_instance
      exact colimMono (X := X) V.unop _
    have : Mono (((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom) := by
      rw [key]
      constructor; intro Z a b h
      have h2 : a ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom =
          b ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom :=
        hm.right_cancellation _ _ ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))
      have h3 := congrArg (· ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv) h2
      have hc : ∀ c : Z ⟶ _, (c ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom) ≫
          ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv = c := fun c =>
        (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id c))
      exact (hc a).symm.trans (h3.trans (hc b))
    exact mono_of_mono _ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom

/- English proof (translation)
Introduce `R _ X`. Use `haveI := lanMono R X`. Establish `h1 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms` using `inferInstance`. Establish `h3 : (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms` using `inferInstance`. Establish `h4 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙ (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms` using `inferInstance`.

Conclude with `Functor.PreservesMonomorphisms.of_iso (F := sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙ (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) (Functor.sheafPullbackConstruction.sheafPullbackIso (Over …`.
-/
theorem PullMono_of : LateralTheory.E.LocSlicePf.PullMono := by
  intro R _ X
  haveI := lanMono R X
  have h1 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  have h3 : (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  have h4 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙
      (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  exact Functor.PreservesMonomorphisms.of_iso (F := sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙
      (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.forget X) (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.{0}.over X) Scheme.etaleTopology.{0}).symm

end LateralTheory.E.PullMonoPf
