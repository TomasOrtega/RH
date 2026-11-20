import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.TPairAssocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

abbrev Jt := Scheme.etaleTopology.{0}
abbrev MC (R : Type) [CommRing R] := ModuleCat.{1} (ULift.{1} R)
abbrev Ix (w : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = w}

/- English proof (translation)
The claim follows from `congrArg (fun f => ModuleCat.Hom.hom f a) (φ.hom.naturality g.op)`.
-/
theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) :=
  congrArg (fun f => ModuleCat.Hom.hom f a) (φ.hom.naturality g.op)

/- English proof (translation)
Simplify using `[Tens.res, DirectSum.lmap_lof]`.
-/
theorem tres_lof (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : Ix w)
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res, DirectSum.lmap_lof]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ MC R where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_id, tres_lof, ModuleCat.hom_id, LinearMap.id_apply]
    simp [Sec.res]
  map_comp f g := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_comp, tres_lof, ModuleCat.hom_comp]
    simp [Sec.res]

def dc (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ (dc I J U w)

/- English proof (translation)
Simplify using `[dT, dc, DirectSum.toModule_lof]`.
-/
theorem dT_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    dT I J U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ (Sec.map (I.d p.1.1 (p.1.1 + 1)) a ⊗ₜ b) +
      (p.1.1.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ (a ⊗ₜ Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
  simp [dT, dc, DirectSum.toModule_lof]

/- English proof (translation)
Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[tres_lof, dT_lof, dT_lof, map_add, map_zsmul, tres_lof, tres_lof, sec_nat, sec_nat]`.
-/
theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [tres_lof, dT_lof, dT_lof, map_add, map_zsmul, tres_lof, tres_lof, sec_nat, sec_nat]

def dP (I J : Cx R) (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := ModuleCat.hom_ext (dT_res I J g.unop w)

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Sec.map (K.d h i ≫ K.d i j) a = 0`. Rewrite using `[K.d_comp_d]`. Both sides reduce to the same expression.
-/
theorem sec_dd (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (a : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) a) = 0 := by
  change Sec.map (K.d h i ≫ K.d i j) a = 0
  rw [K.d_comp_d]
  rfl

/- English proof (translation)
Rewrite using `[← LinearMap.comp_apply (f := dT I J U (w + 1))]`. It suffices to establish `h : dT I J U (w + 1) ∘ₗ dT I J U w = 0 by rw [h]; rfl`. Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises.

Introduce `a b`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply]`. Rewrite using `[dT_lof, map_add, map_zsmul, dT_lof, dT_lof]`. Simplify using `only [sec_dd, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, add_zero, smul_add, smul_zero, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]`. Conclude with `neg_add_cancel _`.
-/
theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    dT I J U (w + 1) (dT I J U w x) = 0 := by
  rw [← LinearMap.comp_apply (f := dT I J U (w + 1))]
  suffices h : dT I J U (w + 1) ∘ₗ dT I J U w = 0 by rw [h]; rfl
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_lof, map_add, map_zsmul, dT_lof, dT_lof]
  simp only [sec_dd, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, add_zero, smul_add,
    smul_zero, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]
  exact neg_add_cancel _

/- English proof (translation)
Use extensionality with `U : 2`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Conclude with `dT_dT I J U.unop w x`.
-/
theorem tensorDifferential_comp_eq_zero (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  exact dT_dT I J U.unop w x

def T (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Jt (MC R)).obj (TP I J w))
    (fun w => (presheafToSheaf Jt (MC R)).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_eq_zero, Functor.map_zero])

/- English proof (translation)
Unfold `T`. Simplify using `[CochainComplex.of]`.
-/
theorem T_d (I J : Cx R) (w : ℤ) : (T I J).d w (w + 1) = (presheafToSheaf Jt (MC R)).map (dP I J w) :=
  by unfold T; simp [CochainComplex.of]

/- English proof (translation)
The claim follows from `(congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Jt P).naturality g.op)).symm`.
-/
theorem toS_res (P : Scheme.{0}ᵒᵖ ⥤ MC R) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    ((sheafify Jt P).map g.op).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt P).app (op V)).hom ((P.map g.op).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Jt P).naturality g.op)).symm

/- English proof (translation)
The claim follows from `(congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) x) (toSheafify_naturality Jt η)).symm`.
-/
theorem toS_map {P Q : Scheme.{0}ᵒᵖ ⥤ MC R} (η : P ⟶ Q) {U : Scheme.{0}} (x : P.obj (op U)) :
    ((sheafifyMap Jt η).app (op U)).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt Q).app (op U)).hom ((η.app (op U)).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) x) (toSheafify_naturality Jt η)).symm

def tS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  ((toSheafify Jt (TP I J w)).app (op U)).hom

def mulT (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  (TensorProduct.mk (ULift.{1} R) _ _).compr₂
    (tS I J U w ∘ₗ
      DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulT_apply (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) a b :
    mulT I J U s t w h a b = tS I J U w
      (DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)) :=
  rfl

def tau (I J : Cx R) : Pair I J (T I J) where
  mul := mulT I J
  nat g s t w h a b := by
    rw [mulT_apply, mulT_apply]
    exact (toS_res (TP I J w) g _).trans (congrArg _ (tres_lof I J g w ⟨(s, t), h⟩ a b))
  leibniz U s t w h a b := by
    rw [mulT_apply, mulT_apply, mulT_apply, T_d]
    refine Eq.trans (toS_map (dP I J w) _) ?_
    show tS I J U (w + 1) (dT I J U w _) = tS I J U (w + 1) _ + s.negOnePow • tS I J U (w + 1) _
    rw [dT_lof, map_add, map_zsmul, Units.smul_def]

/- English proof (translation)
Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]`.

Both sides reduce to the same expression.
-/
theorem tau_lift (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    (tau I J).lift U w = tS I J U w := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U w y`. Use `⟨_, Presheaf.imageSieve_mem Jt (toSheafify Jt (TP I J w)) (U := op U) y, ?_⟩` and prove the remaining obligations. Introduce `V g hg`. Take `⟨x, hx⟩` from `hg`.

Conclude with `⟨x, by rw [tau_lift]; exact hx⟩`. Introduce `U w x hx`. Rewrite `hx` using `[tau_lift]`. Use `⟨_, Presheaf.equalizerSieve_mem Jt (toSheafify Jt (TP I J w)) (X := op U) x 0 (by rw [map_zero]; exact hx), ?_⟩` and prove the remaining obligations. Introduce `V g hg`.

Establish `: (TP I J w).map g.op x = (TP I J w).map g.op 0` using `hg`. Rewrite `this` using `[map_zero]`. Conclude with `this`.
-/
theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Jt (toSheafify Jt (TP I J w)) (U := op U) y, ?_⟩
    intro V g hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, by rw [tau_lift]; exact hx⟩
  · intro U w x hx
    rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Jt (toSheafify Jt (TP I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx), ?_⟩
    intro V g hg
    have : (TP I J w).map g.op x = (TP I J w).map g.op 0 := hg
    rw [map_zero] at this
    exact this

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Introduce `R _ I J`. Conclude with `⟨TensEx.T I J, TensEx.tau I J, TensEx.tau_isTensor I J⟩`.
-/
theorem t_pa_tens_ex_of : t_pa_tens_ex := by
  intro R _ I J
  exact ⟨TensEx.T I J, TensEx.tau I J, TensEx.tau_isTensor I J⟩

end LateralTheory.EtaleFoundations
