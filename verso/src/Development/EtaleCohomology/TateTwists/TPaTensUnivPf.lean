import Development.EtaleCohomology.TateTwists.TPairAssocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

abbrev tl {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)

/- English proof (translation)
The claim follows from `DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => h p a b`.
-/
theorem tu_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (h : ∀ p a b, f (tl p a b) = g (tl p a b)) : f = g :=
  DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => h p a b

/- English proof (translation)
Simplify using `[tl, Tens.res, DirectSum.lmap_lof]`.
-/
theorem tu_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (tl p a b) = tl p (Sec.res g a) (Sec.res g b) := by
  simp [tl, Tens.res, DirectSum.lmap_lof]

/- English proof (translation)
Simplify using `[tl, Pair.lift, DirectSum.toModule_lof]`.
-/
theorem tu_lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (tl p a b) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [tl, Pair.lift, DirectSum.toModule_lof]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem tu_sec_res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem tu_sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  simp [Sec.res]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [tu_res_lof, tu_sec_res_id, tu_sec_res_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tu_res_lof, tu_res_lof, tu_res_lof, tu_sec_res_comp, tu_sec_res_comp]

/- English proof (translation)
Establish `: (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w)`. Use `tu_ext fun p a b => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[tu_res_lof, tu_lift_lof, tu_lift_lof, ← μ.nat]`. Conclude with `LinearMap.congr_fun this x`.
-/
theorem tu_lift_nat {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    refine tu_ext fun p a b => ?_
    simp only [LinearMap.comp_apply]
    rw [tu_res_lof, tu_lift_lof, tu_lift_lof, ← μ.nat]
  exact LinearMap.congr_fun this x

def Lf {I J K : Cx R} (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality V U g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact tu_lift_nat μ g.unop w x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U x' y' hxy`. Set `x : Tens I J U.unop w` to `x'`. Set `y : Tens I J U.unop w` to `y'`. Establish `hxy' : τ.lift U.unop w x = τ.lift U.unop w y` using `hxy`.

Establish `h0 : τ.lift U.unop w (x - y) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.mpr hxy'`. Take `⟨S, hS, hP⟩` from `hτ.2 U.unop w (x - y) h0`. Use `Scheme.etaleTopology.superset_covering ?_ hS` and prove the remaining obligations.

Introduce `V g hg`. Establish `h1 : Tens.res g w (x - y) = 0` using `hP V g hg`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Conclude with `h1`.
-/
theorem tu_locInj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U x' y' hxy
  let x : Tens I J U.unop w := x'
  let y : Tens I J U.unop w := y'
  have hxy' : τ.lift U.unop w x = τ.lift U.unop w y := hxy
  have h0 : τ.lift U.unop w (x - y) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hxy'
  obtain ⟨S, hS, hP⟩ := hτ.2 U.unop w (x - y) h0
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  have h1 : Tens.res g w (x - y) = 0 := hP V g hg
  rw [map_sub, sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U y`. Take `⟨S, hS, hP⟩` from `hτ.1 U w y`. Use `Scheme.etaleTopology.superset_covering ?_ hS` and prove the remaining obligations. Introduce `V g hg`.

Take `⟨x, hx⟩` from `hP V g hg`. Conclude with `⟨x, hx⟩`.
-/
theorem tu_locSurj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U y
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  obtain ⟨x, hx⟩ := hP V g hg
  exact ⟨x, hx⟩

/- English proof (translation)
Use `tu_locInj τ hτ w` as an intermediate fact. Use `tu_locSurj τ hτ w` as an intermediate fact. Conclude with `GrothendieckTopology.W_of_isLocallyBijective _ _`.
-/
theorem etaleTensorPairingLift_isSheafifyLocalIso {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (Lf τ w) := by
  have := tu_locInj τ hτ w
  have := tu_locSurj τ hτ w
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

def uf {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) : (T.X w).obj ⟶ (K.X w).obj :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose

/- English proof (translation)
The claim follows from `((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose_spec`.
-/
theorem uf_spec {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) :
    Lf τ w ≫ uf τ hτ μ w = Lf μ w :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose_spec

/- English proof (translation)
Use `congrArg (fun φ => (φ.app (op U)).hom x) (uf_spec τ hτ μ w)` as an intermediate fact. Conclude with `this`.
-/
theorem uf_lift {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) (U : Scheme.{0})
    (x : Tens I J U w) : ((uf τ hτ μ w).app (op U)).hom (τ.lift U w x) = μ.lift U w x := by
  have := congrArg (fun φ => (φ.app (op U)).hom x) (uf_spec τ hτ μ w)
  exact this

/- English proof (translation)
Use `uf_lift τ hτ μ w U (tl (w := w) ⟨(s, t), h⟩ a b)` as an intermediate fact. Rewrite `this` using `[tu_lift_lof, tu_lift_lof]`. Then use the resulting hypothesis.
-/
theorem uf_mul {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    ((uf τ hτ μ w).app (op U)).hom (τ.mul U s t w h a b) = μ.mul U s t w h a b := by
  have := uf_lift τ hτ μ w U (tl (w := w) ⟨(s, t), h⟩ a b)
  rwa [tu_lift_lof, tu_lift_lof] at this

/- English proof (translation)
Apply `((etaleTensorPairingLift_isSheafifyLocalIso τ hτ i) _ (K.X (i + 1)).property).1` to reduce the goal to its premises. Use `NatTrans.ext (funext fun U => ModuleCat.hom_ext (tu_ext fun p a b => ?_))` and prove the remaining obligations. Take `⟨⟨s, t⟩, h⟩` from `p`. Simplify using `only [NatTrans.comp_app, ModuleCat.hom_comp]`. Express the relevant statement in the definitionally equal form `((K.d i (i + 1)).hom.app U).hom (((uf τ hτ μ i).app (op U.unop)).hom (τ.lift U.unop i (tl _ a b))) = ((uf τ hτ μ (i + 1)).app (op U.unop)).hom (((T.d i (i + 1)).hom.app U).hom (τ.lift U.unop i (tl _ a b)))`.

Rewrite using `[tu_lift_lof, uf_mul]`. Establish `l1` using `μ.leibniz U.unop s t i h a b`. Establish `l2` using `τ.leibniz U.unop s t i h a b`. Simplify using `only [Sec.map] at l1 l2`. Rewrite using `[l1, l2, map_add, Units.smul_def, Units.smul_def, map_zsmul, uf_mul, uf_mul]`.
-/
theorem uf_comm {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (i : ℤ) :
    uf τ hτ μ i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ uf τ hτ μ (i + 1) := by
  apply ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ i) _ (K.X (i + 1)).property).1
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (tu_ext fun p a b => ?_))
  obtain ⟨⟨s, t⟩, h⟩ := p
  simp only [NatTrans.comp_app, ModuleCat.hom_comp]
  change ((K.d i (i + 1)).hom.app U).hom (((uf τ hτ μ i).app (op U.unop)).hom (τ.lift U.unop i (tl _ a b))) =
    ((uf τ hτ μ (i + 1)).app (op U.unop)).hom (((T.d i (i + 1)).hom.app U).hom (τ.lift U.unop i (tl _ a b)))
  rw [tu_lift_lof, uf_mul]
  have l1 := μ.leibniz U.unop s t i h a b
  have l2 := τ.leibniz U.unop s t i h a b
  simp only [Sec.map] at l1 l2
  rw [l1, l2, map_add, Units.smul_def, Units.smul_def, map_zsmul, uf_mul, uf_mul]

def uc {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) : T ⟶ K where
  f w := ⟨uf τ hτ μ w⟩
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    ext1
    exact uf_comm τ hτ μ i

/- English proof (translation)
Introduce `R _ I J T K τ hτ μ`. Use `⟨uc τ hτ μ, fun U s t w h a b => ?_⟩` and prove the remaining obligations. Simplify using `only [HomologicalComplex.id_f, pa_sec_map_id]`. Conclude with `uf_mul τ hτ μ U s t w h a b`.
-/
theorem t_pa_tens_univ_of : t_pa_tens_univ := by
  intro R _ I J T K τ hτ μ
  refine ⟨uc τ hτ μ, fun U s t w h a b => ?_⟩
  simp only [HomologicalComplex.id_f, pa_sec_map_id]
  exact uf_mul τ hτ μ U s t w h a b

end LateralTheory.EtaleFoundations
