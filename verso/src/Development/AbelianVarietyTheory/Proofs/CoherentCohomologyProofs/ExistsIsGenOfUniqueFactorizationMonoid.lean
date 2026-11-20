import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `: Module.FinitePresentation A M` using `Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := B) j fun r => Module.finitePresentation_of_projective _ _`. Set `d (r : s) : Module.Dual A M →ₗ[A] Module.Dual (B r) (N r)` to `IsLocalizedModule.mapExtendScalars (.powers r.1) (j r) (Algebra.linearMap A (B r)) (B r)`. Establish `hd (r : s) : IsLocalizedModule (.powers r.1) (d r)` using `inferInstance`. Establish `hd' (r : s) (ξ : Module.Dual A M) (m : M) : d r ξ (j r m) = algebraMap A (B r) (ξ m)` using `IsLocalizedModule.map_apply (.powers r.1) (j r) (Algebra.linearMap A (B r)) ξ m`. Set `e (r : s) : Module.Dual (B r) (N r) ⊗[A] N r ≃ₗ[A] B r` to `((IsLocalization.moduleTensorEquiv (.powers r.1) (B r) _ _).symm ≪≫ₗ Module.Invertible.linearEquiv (B r) (N r)).restrictScalars A`.

Establish `he (r : s) (ξ : Module.Dual (B r) (N r)) (n : N r) : e r (ξ ⊗ₜ n) = ξ n`. Simplify using `[e, IsLocalization.moduleTensorEquiv, Module.Invertible.linearEquiv, TensorProduct.equivOfCompatibleSMul]`. Use `⟨bijective_of_isLocalized_span s hs _ (fun r => TensorProduct.map (d r) (j r)) B (fun r => Algebra.linearMap A (B r)) _ fun r => ?_⟩` and prove the remaining obligations. Establish `: IsLocalizedModule.map (.powers r.1) (TensorProduct.map (d r) (j r)) (Algebra.linearMap A (B r)) (contractLeft A M) = (e r).toLinearMap`. Use `IsLocalizedModule.linearMap_ext (.powers r.1) (TensorProduct.map (d r) (j r)) (Algebra.linearMap A (B r)) ?_` and prove the remaining obligations.

Rewrite using `[IsLocalizedModule.map_comp]`. Use extensionality with `ξ m`. Simplify using `[he, hd']`. Rewrite using `[this]`. Conclude with `(e r).bijective`.
-/
theorem invertible_of_isLocalizedModule_span {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*) [∀ r, CommRing (B r)]
    [∀ r, Algebra A (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)] (N : s → Type*)
    [∀ r, AddCommGroup (N r)] [∀ r, Module A (N r)] [∀ r, Module (B r) (N r)]
    [∀ r, IsScalarTower A (B r) (N r)] (j : ∀ r, M →ₗ[A] N r)
    [∀ r : s, IsLocalizedModule.Away r.1 (j r)] (h : ∀ r, Module.Invertible (B r) (N r)) :
    Module.Invertible A M := by
  have : Module.FinitePresentation A M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := B) j fun r =>
      Module.finitePresentation_of_projective _ _
  let d (r : s) : Module.Dual A M →ₗ[A] Module.Dual (B r) (N r) :=
    IsLocalizedModule.mapExtendScalars (.powers r.1) (j r) (Algebra.linearMap A (B r)) (B r)
  have hd (r : s) : IsLocalizedModule (.powers r.1) (d r) := inferInstance
  have hd' (r : s) (ξ : Module.Dual A M) (m : M) : d r ξ (j r m) = algebraMap A (B r) (ξ m) :=
    IsLocalizedModule.map_apply (.powers r.1) (j r) (Algebra.linearMap A (B r)) ξ m
  let e (r : s) : Module.Dual (B r) (N r) ⊗[A] N r ≃ₗ[A] B r :=
    ((IsLocalization.moduleTensorEquiv (.powers r.1) (B r) _ _).symm ≪≫ₗ
      Module.Invertible.linearEquiv (B r) (N r)).restrictScalars A
  have he (r : s) (ξ : Module.Dual (B r) (N r)) (n : N r) : e r (ξ ⊗ₜ n) = ξ n := by
    simp [e, IsLocalization.moduleTensorEquiv, Module.Invertible.linearEquiv,
      TensorProduct.equivOfCompatibleSMul]
  refine ⟨bijective_of_isLocalized_span s hs _ (fun r => TensorProduct.map (d r) (j r)) B
    (fun r => Algebra.linearMap A (B r)) _ fun r => ?_⟩
  have : IsLocalizedModule.map (.powers r.1) (TensorProduct.map (d r) (j r))
      (Algebra.linearMap A (B r)) (contractLeft A M) = (e r).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (.powers r.1) (TensorProduct.map (d r) (j r))
      (Algebra.linearMap A (B r)) ?_
    rw [IsLocalizedModule.map_comp]
    ext ξ m
    simp [he, hd']
  rw [this]
  exact (e r).bijective

/- English proof (translation)
Set `` to `e.toRingHom.toAlgebra`. Establish `: IsScalarTower A B M` using `.of_algebraMap_smul fun a m => (h a m).symm`. Establish `: IsLocalization (IsUnit.submonoid A) B` using `IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit e.bijective`. Establish `: IsLocalizedModule (IsUnit.submonoid A) (LinearMap.id : M →ₗ[A] M)` using `⟨fun r => r.2.map _, fun m => ⟨(m, 1), by simp⟩, fun h => ⟨1, by simpa using h⟩⟩`. Conclude with `Module.Invertible.of_isLocalization (IsUnit.submonoid A) (LinearMap.id : M →ₗ[A] M)`.
-/
theorem invertible_of_ringEquiv {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Module A M] [Module B M] (e : A ≃+* B) (h : ∀ (a : A) (m : M), a • m = e a • m)
    [Module.Invertible A M] : Module.Invertible B M := by
  let := e.toRingHom.toAlgebra
  have : IsScalarTower A B M := .of_algebraMap_smul fun a m => (h a m).symm
  have : IsLocalization (IsUnit.submonoid A) B :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit
      e.bijective
  have : IsLocalizedModule (IsUnit.submonoid A) (LinearMap.id : M →ₗ[A] M) :=
    ⟨fun r => r.2.map _, fun m => ⟨(m, 1), by simp⟩, fun h => ⟨1, by simpa using h⟩⟩
  exact Module.Invertible.of_isLocalization (IsUnit.submonoid A) (LinearMap.id : M →ₗ[A] M)

/- English proof (translation)
Set `φ : A ≃ₗ[A] M` to `LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M e) he`. Establish `: Module.Invertible A M` using `.congr φ`. Use `bijective_toSpanSingleton_of_isBaseChange φ.symm.toLinearMap e j hj ?_` and prove the remaining obligations. Establish `: φ.symm e = 1` using `φ.symm_apply_eq.2 (one_smul A e).symm`. Rewrite using `[LinearEquiv.coe_coe, this, map_one]`.

Conclude with `isUnit_one`.
-/
theorem bijective_smul_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    {j : M →ₗ[A] N} (hj : IsBaseChange B j) {e : M} (he : Function.Bijective fun a : A => a • e) :
    Function.Bijective fun b : B => b • j e := by
  let φ : A ≃ₗ[A] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M e) he
  have : Module.Invertible A M := .congr φ
  refine bijective_toSpanSingleton_of_isBaseChange φ.symm.toLinearMap e j hj ?_
  have : φ.symm e = 1 := φ.symm_apply_eq.2 (one_smul A e).symm
  rw [LinearEquiv.coe_coe, this, map_one]
  exact isUnit_one

/- English proof (translation)
Rewrite using `[Module.Invertible.free_iff_linearEquiv]`. Use `⟨fun ⟨φ⟩ => ⟨φ.symm 1, ?_⟩, fun ⟨e, he⟩ => ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M e) he).symm⟩⟩` and prove the remaining obligations. Establish `: (fun a : A => a • φ.symm 1) = φ.symm` using `funext fun a => by`. Rewrite using `[← map_smul, smul_eq_mul, mul_one]`. Rewrite using `[this]`.

Conclude with `φ.symm.bijective`.
-/
theorem free_iff_exists_bijective_smul {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] :
    Module.Free A M ↔ ∃ e : M, Function.Bijective fun a : A => a • e := by
  rw [Module.Invertible.free_iff_linearEquiv]
  refine ⟨fun ⟨φ⟩ => ⟨φ.symm 1, ?_⟩, fun ⟨e, he⟩ =>
    ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M e) he).symm⟩⟩
  have : (fun a : A => a • φ.symm 1) = φ.symm := funext fun a => by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [this]
  exact φ.symm.bijective

namespace LB

variable {X : Scheme.{0}}

section Frames

variable {F G : X.Modules} {U U' V W : X.Opens}

def IsFrame (e : Γ(F, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun a : Γ(X, V) => a • F.presheaf.map (homOfLE h).op e

/- English proof (translation)
The claim follows from `bijective_smul_chartSec hL i`.
-/
theorem isFrame_chartSec {L : LB X} (hL : L.IsLB) (i : L.ι) : IsFrame (chartSec hL i) :=
  bijective_smul_chartSec hL i

/- English proof (translation)
Introduce `V h` and use `by rw [map_ofSec] exact bijective_smul_genSec hL.cover ht V`.
-/
theorem isFrame_genSec {L : LB X} (hL : L.IsLB) {t : LB.Gen L} (ht : t.IsGen) (U : X.Opens) :
    IsFrame (ofSec (DVR.genSec t ht) U) := fun V h => by
  rw [map_ofSec]
  exact bijective_smul_genSec hL.cover ht V

/- English proof (translation)
The claim follows from `F.map_smul (homOfLE h) a s`.
-/
theorem map_smul_resG (h : V ≤ U) (a : Γ(X, U)) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op (a • s) = resG X h a • F.presheaf.map (homOfLE h).op s :=
  F.map_smul (homOfLE h) a s

/- English proof (translation)
The claim follows from `ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s`.
-/
theorem app_map (φ : F ⟶ G) (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ.app U s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s

def appLinear (φ : F ⟶ G) (V : X.Opens) : Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V) where
  toFun := φ.app V
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem appLinear_apply (φ : F ⟶ G) (V : X.Opens) (s : Γ(F, V)) :
    appLinear φ V s = φ.app V s := rfl

def appLinearEquiv (φ : F ≅ G) (V : X.Opens) : Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V) :=
  LinearEquiv.ofBijective (appLinear φ.hom V)
    (ConcreteCategory.bijective_of_isIso (φ.hom.app V))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem appLinearEquiv_apply (φ : F ≅ G) (V : X.Opens) (s : Γ(F, V)) :
    appLinearEquiv φ V s = φ.hom.app V s := rfl

/- English proof (translation)
The claim follows from `TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V (fun k => homOfLE (hW k)) hc s t h`.
-/
theorem mod_ext_of_cover {ι : Type*} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {s t : Γ(F, V)}
    (h : ∀ k, F.presheaf.map (homOfLE (hW k)).op s = F.presheaf.map (homOfLE (hW k)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun k => homOfLE (hW k)) hc s t h

/- English proof (translation)
The claim follows from `(TopCat.Sheaf.existsUnique_gluing' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V (fun k => homOfLE (hW k)) hc s h).exists`.
-/
theorem exists_mod_of_cover {ι : Type*} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) (s : ∀ k, Γ(F, W k))
    (h : ∀ k l, F.presheaf.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (s k) =
      F.presheaf.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (s l)) :
    ∃ t : Γ(F, V), ∀ k, F.presheaf.map (homOfLE (hW k)).op t = s k :=
  (TopCat.Sheaf.existsUnique_gluing' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun k => homOfLE (hW k)) hc s h).exists

namespace IsFrame

variable {e : Γ(F, U)} {e' : Γ(F, U')}

/- English proof (translation)
Introduce `W h'` and use `by rw [QCoh.res_res] exact he W _`.
-/
theorem map (he : IsFrame e) (h : V ≤ U) : IsFrame (F.presheaf.map (homOfLE h).op e) :=
  fun W h' => by
    rw [QCoh.res_res]
    exact he W _

/- English proof (translation)
Introduce `V h` and use `by have : (fun a : Γ(X, V) => a • G.presheaf.map (homOfLE h).op (φ.hom.app U e)) = appLinearEquiv φ V ∘ fun a : Γ(X, V) => a • F.presheaf.map (homOfLE h).op e := by ext a rw [Function.comp_apply, map_smul, appLinearEquiv_apply, app_map] rw [this] exact (appLinearEquiv φ V).biject …`.
-/
theorem app (he : IsFrame e) (φ : F ≅ G) : IsFrame (φ.hom.app U e) := fun V h => by
  have : (fun a : Γ(X, V) => a • G.presheaf.map (homOfLE h).op (φ.hom.app U e)) =
      appLinearEquiv φ V ∘ fun a : Γ(X, V) => a • F.presheaf.map (homOfLE h).op e := by
    ext a
    rw [Function.comp_apply, map_smul, appLinearEquiv_apply, app_map]
  rw [this]
  exact (appLinearEquiv φ V).bijective.comp (he V h)

def repr (he : IsFrame e) (h : V ≤ U) : Γ(F, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, V) Γ(F, V)
    (F.presheaf.map (homOfLE h).op e)) (he V h)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repr_symm_apply (he : IsFrame e) (h : V ≤ U) (a : Γ(X, V)) :
    (he.repr h).symm a = a • F.presheaf.map (homOfLE h).op e := rfl

/- English proof (translation)
The claim follows from `(he.repr h).symm_apply_apply s`.
-/
theorem repr_smul (he : IsFrame e) (h : V ≤ U) (s : Γ(F, V)) :
    he.repr h s • F.presheaf.map (homOfLE h).op e = s :=
  (he.repr h).symm_apply_apply s

/- English proof (translation)
Rewrite using `[← ha]`. Conclude with `(he.repr h).apply_symm_apply a`.
-/
theorem repr_eq (he : IsFrame e) (h : V ≤ U) {s : Γ(F, V)} {a : Γ(X, V)}
    (ha : a • F.presheaf.map (homOfLE h).op e = s) : he.repr h s = a := by
  rw [← ha]
  exact (he.repr h).apply_symm_apply a

/- English proof (translation)
Use `(he.repr_eq _ ?_).symm` and prove the remaining obligations. Rewrite using `[← QCoh.res_res F h h', ← map_smul_resG, repr_smul]`.
-/
theorem resG_repr (he : IsFrame e) (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, V)) :
    resG X h' (he.repr h s) = he.repr (h'.trans h) (F.presheaf.map (homOfLE h').op s) := by
  refine (he.repr_eq _ ?_).symm
  rw [← QCoh.res_res F h h', ← map_smul_resG, repr_smul]

/- English proof (translation)
Use `conv_lhs => rw [← he'.repr_smul h' s]`. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.
-/
theorem repr_change (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') (s : Γ(F, V)) :
    he.repr h s = he.repr h (F.presheaf.map (homOfLE h').op e') * he'.repr h' s := by
  conv_lhs => rw [← he'.repr_smul h' s]
  rw [map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
The claim follows from `he.repr_eq h (one_smul _ _)`.
-/
theorem repr_self (he : IsFrame e) (h : V ≤ U) :
    he.repr h (F.presheaf.map (homOfLE h).op e) = 1 :=
  he.repr_eq h (one_smul _ _)

def unit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') : Γ(X, V)ˣ :=
  Units.mkOfMulEqOne (he.repr h (F.presheaf.map (homOfLE h').op e'))
    (he'.repr h' (F.presheaf.map (homOfLE h).op e))
    (by rw [← he.repr_change he' h h', repr_self])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_unit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') :
    (he.unit he' h h' : Γ(X, V)) = he.repr h (F.presheaf.map (homOfLE h').op e') := rfl

/- English proof (translation)
Rewrite using `[val_unit, resG_repr, QCoh.res_res]`.
-/
theorem resG_unit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') (h'' : W ≤ V) :
    resG X h'' (he.unit he' h h' : Γ(X, V)) =
      he.repr (h''.trans h) (F.presheaf.map (homOfLE (h''.trans h')).op e') := by
  rw [val_unit, resG_repr, QCoh.res_res]

end IsFrame

/- English proof (translation)
Set `e₀ : Γ(F, U.ι ''ᵁ ⊤)` to `φ.hom.app ⊤ (1 : Γ(U.toScheme, ⊤))`. Establish `hU : U ≤ U.ι ''ᵁ ⊤` using `by simp`. Set `e : Γ(F, U)` to `F.presheaf.map (homOfLE hU).op e₀`. Establish `hφ : φ.hom = Descent.sectionHom e`. Apply `(SheafOfModules.unitHomEquiv (F.restrict U.ι)).injective` to reduce the goal to its premises.

Rewrite using `[Descent.sectionHom, Equiv.apply_symm_apply]`. Use extensionality with `⟨W⟩`. Establish `h₁` using `app_map φ.hom (le_top : W ≤ ⊤) (1 : Γ(U.toScheme, ⊤))`. Establish `h₂ : (unitMod U.toScheme).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(U.toScheme, ⊤)) = (1 : Γ(U.toScheme, W))` using `map_one (resG U.toScheme le_top)`. Rewrite `h₁` using `[h₂]`.

Use `(SheafOfModules.unitHomEquiv_apply_coe (F.restrict U.ι) φ.hom (op W)).trans (h₁.trans ?_)` and prove the remaining obligations. Conclude with `(QCoh.res_res F hU (U.ι_image_le W) e₀).symm`. Establish `: IsIso (Descent.sectionHom e)` using `hφ ▸ φ.isIso_hom`. Conclude with `⟨e, fun V h => Descent.bijective_smul_of_stalk (Descent.isIso_sectionHom_iff.1 this) h⟩`.
-/
theorem exists_isFrame_of_iso (φ : unitMod U.toScheme ≅ F.restrict U.ι) :
    ∃ e : Γ(F, U), IsFrame e := by
  let e₀ : Γ(F, U.ι ''ᵁ ⊤) := φ.hom.app ⊤ (1 : Γ(U.toScheme, ⊤))
  have hU : U ≤ U.ι ''ᵁ ⊤ := by simp
  let e : Γ(F, U) := F.presheaf.map (homOfLE hU).op e₀
  have hφ : φ.hom = Descent.sectionHom e := by
    apply (SheafOfModules.unitHomEquiv (F.restrict U.ι)).injective
    rw [Descent.sectionHom, Equiv.apply_symm_apply]
    ext ⟨W⟩
    have h₁ := app_map φ.hom (le_top : W ≤ ⊤) (1 : Γ(U.toScheme, ⊤))
    have h₂ : (unitMod U.toScheme).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (1 : Γ(U.toScheme, ⊤)) = (1 : Γ(U.toScheme, W)) := map_one (resG U.toScheme le_top)
    rw [h₂] at h₁
    refine (SheafOfModules.unitHomEquiv_apply_coe (F.restrict U.ι) φ.hom (op W)).trans
      (h₁.trans ?_)
    exact (QCoh.res_res F hU (U.ι_image_le W) e₀).symm
  have : IsIso (Descent.sectionHom e) := hφ ▸ φ.isIso_hom
  exact ⟨e, fun V h => Descent.bijective_smul_of_stalk (Descent.isIso_sectionHom_iff.1 this) h⟩

end Frames

section OfFrames

variable {F : X.Modules} {ι : Type} {U : ι → X.Opens} {e : ∀ i, Γ(F, U i)}

abbrev ofFrames (he : ∀ i, IsFrame (e i)) : LB X where
  ι := ι
  U := U
  g i j := (he i).unit (he j) inf_le_left inf_le_right

/- English proof (translation)
The claim follows from `(he i).resG_unit (he j) _ _ h`.
-/
theorem resG_ofFrames_g (he : ∀ i, IsFrame (e i)) (i j : ι) {W : X.Opens} (h : W ≤ U i ⊓ U j) :
    resG X h ((ofFrames he).g i j : Γ(X, U i ⊓ U j)) =
      (he i).repr (h.trans inf_le_left)
        (F.presheaf.map (homOfLE (h.trans inf_le_right)).op (e j)) :=
  (he i).resG_unit (he j) _ _ h

/- English proof (translation)
The claim follows from `hU g_self i := Units.ext ((resG_ofFrames_g he i i _).trans ((he i).repr_self _)) cocycle i j k := Units.ext <| by rw [Units.val_mul, val_res, val_res, val_res] rw [resG_ofFrames_g, resG_ofFrames_g, resG_ofFrames_g] exact ((he i).repr_change (he j) _ _ _).symm`.
-/
theorem ofFrames_isLB (he : ∀ i, IsFrame (e i)) (hU : ⨆ i, U i = ⊤) : (ofFrames he).IsLB where
  cover := hU
  g_self i := Units.ext ((resG_ofFrames_g he i i _).trans ((he i).repr_self _))
  cocycle i j k := Units.ext <| by
    rw [Units.val_mul, val_res, val_res, val_res]
    rw [resG_ofFrames_g, resG_ofFrames_g, resG_ofFrames_g]
    exact ((he i).repr_change (he j) _ _ _).symm

def toFramesLinear (he : ∀ i, IsFrame (e i)) (V : X.Opens) :
    Γ(F, V) →ₗ[Γ(X, V)] Γ(toMod (ofFrames he), V) where
  toFun s := mkSec (L := ofFrames he) (fun i => (he i).repr (inf_le_right : V ⊓ U i ≤ U i)
      (F.presheaf.map (homOfLE inf_le_left).op s)) fun i j => by
    rw [resG_ofFrames_g, IsFrame.resG_repr, IsFrame.resG_repr, QCoh.res_res, QCoh.res_res]
    exact (he i).repr_change (he j) _ _ _
  map_add' s t := sec_ext fun i => by
    simp only [coord_add, map_add]
    rfl
  map_smul' a s := sec_ext fun i => by
    simp only [coord_smul, map_smul_resG, map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_toFramesLinear (he : ∀ i, IsFrame (e i)) (V : X.Opens) (s : Γ(F, V)) (i : ι) :
    coord (toFramesLinear he V s) i = (he i).repr (inf_le_right : V ⊓ U i ≤ U i)
      (F.presheaf.map (homOfLE inf_le_left).op s) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `s t h`. Use `mod_ext_of_cover (fun i => V ⊓ U i) (fun _ => inf_le_left) (le_iSup_inf hU V) fun i => ((he i).repr inf_le_right).injective ?_` and prove the remaining obligations. Conclude with `congrArg (fun s => coord s i) h`. Introduce `t`.

Take `⟨s, hs⟩` from `exists_mod_of_cover (F := F) (fun i => V ⊓ U i) (fun _ => inf_le_left) (le_iSup_inf hU V) (fun i => coord t i • F.presheaf.map (homOfLE inf_le_right).op (e i)) fun i j => by`. Establish `hij : V ⊓ U i ⊓ (V ⊓ U j) ≤ U i ⊓ U j` using `inf_le_inf inf_le_right inf_le_right`. Establish `h₁` using `coord_rel t i j inf_le_left inf_le_right hij`. Rewrite `h₁` using `[resG_ofFrames_g]`. Rewrite using `[map_smul_resG, map_smul_resG, QCoh.res_res, QCoh.res_res]`.

Rewrite using `[h₁]`. Rewrite using `[mul_comm, mul_smul, IsFrame.repr_smul]`. Use `⟨s, sec_ext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[coord_toFramesLinear, hs]`. Conclude with `(he i).repr_eq _ rfl`.
-/
theorem bijective_toFramesLinear (he : ∀ i, IsFrame (e i)) (hU : ⨆ i, U i = ⊤) (V : X.Opens) :
    Function.Bijective (toFramesLinear he V) := by
  constructor
  · intro s t h
    refine mod_ext_of_cover (fun i => V ⊓ U i) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun i => ((he i).repr inf_le_right).injective ?_
    exact congrArg (fun s => coord s i) h
  · intro t
    obtain ⟨s, hs⟩ := exists_mod_of_cover (F := F) (fun i => V ⊓ U i) (fun _ => inf_le_left)
      (le_iSup_inf hU V)
      (fun i => coord t i •
        F.presheaf.map (homOfLE inf_le_right).op (e i)) fun i j => by
        have hij : V ⊓ U i ⊓ (V ⊓ U j) ≤ U i ⊓ U j := inf_le_inf inf_le_right inf_le_right
        have h₁ := coord_rel t i j inf_le_left inf_le_right hij
        rw [resG_ofFrames_g] at h₁
        rw [map_smul_resG, map_smul_resG, QCoh.res_res, QCoh.res_res]
        rw [h₁]
        rw [mul_comm, mul_smul, IsFrame.repr_smul]
    refine ⟨s, sec_ext fun i => ?_⟩
    rw [coord_toFramesLinear, hs]
    exact (he i).repr_eq _ rfl

def ofFramesIso (he : ∀ i, IsFrame (e i)) (hU : ⨆ i, U i = ⊤) : F ≅ toMod (ofFrames he) :=
  isoOfLinear (fun V => LinearEquiv.ofBijective _ (bijective_toFramesLinear he hU V))
    fun {V W} h s => sec_ext fun i => by
      rw [coord_map, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        coord_toFramesLinear, coord_toFramesLinear, IsFrame.resG_repr, QCoh.res_res,
        QCoh.res_res]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_ofFramesIso_hom_app (he : ∀ i, IsFrame (e i)) (hU : ⨆ i, U i = ⊤) (V : X.Opens)
    (s : Γ(F, V)) (i : ι) :
    coord ((ofFramesIso he hU).hom.app V s) i = (he i).repr (inf_le_right : V ⊓ U i ≤ U i)
      (F.presheaf.map (homOfLE inf_le_left).op s) := rfl

/- English proof (translation)
The claim follows from `sec_ext fun j => (resG_ofFrames_g he j i _).symm`.
-/
theorem ofFramesIso_hom_app_frame (he : ∀ i, IsFrame (e i)) (hU : ⨆ i, U i = ⊤) (i : ι) :
    (ofFramesIso he hU).hom.app (U i) (e i) = chartSec (ofFrames_isLB he hU) i :=
  sec_ext fun j => (resG_ofFrames_g he j i _).symm

/- English proof (translation)
Use `choose U hx e he using h`. Establish `hU : ⨆ x, U x = ⊤` using `eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩`. Conclude with `⟨ofFrames he, ofFrames_isLB he hU, ⟨(ofFramesIso he hU).symm⟩⟩`.
-/
theorem exists_toMod_iso (F : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (e : Γ(F, U)), IsFrame e) :
    ∃ L : LB X, L.IsLB ∧ Nonempty (toMod L ≅ F) := by
  choose U hx e he using h
  have hU : ⨆ x, U x = ⊤ := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
  exact ⟨ofFrames he, ofFrames_isLB he hU, ⟨(ofFramesIso he hU).symm⟩⟩

/- English proof (translation)
Use `⟨fun ⟨L, hL, ⟨φ⟩⟩ x => ?_, exists_toMod_iso F⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))`. Conclude with `⟨L.U i, hi, _, (isFrame_chartSec hL i).app φ⟩`.
-/
theorem exists_toMod_iso_iff (F : X.Modules) :
    (∃ L : LB X, L.IsLB ∧ Nonempty (toMod L ≅ F)) ↔
      ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (e : Γ(F, U)), IsFrame e := by
  refine ⟨fun ⟨L, hL, ⟨φ⟩⟩ x => ?_, exists_toMod_iso F⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))
  exact ⟨L.U i, hi, _, (isFrame_chartSec hL i).app φ⟩

/- English proof (translation)
The claim follows from `exists_toMod_iso F fun x => let ⟨U, hx, ⟨φ⟩⟩ := h x ⟨U, hx, exists_isFrame_of_iso φ⟩`.
-/
theorem exists_toMod_iso_of_restrict_iso (F : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
      Nonempty (unitMod U.toScheme ≅ F.restrict U.ι)) :
    ∃ L : LB X, L.IsLB ∧ Nonempty (toMod L ≅ F) :=
  exists_toMod_iso F fun x =>
    let ⟨U, hx, ⟨φ⟩⟩ := h x
    ⟨U, hx, exists_isFrame_of_iso φ⟩

end OfFrames

section Hom

variable {L M : LB X}

/- English proof (translation)
The claim follows from `(isFrame_chartSec hL i).repr_eq h ((chartEquiv hL i h).symm_apply_apply s)`.
-/
theorem repr_chartSec (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (s : Γ(toMod L, V)) :
    (isFrame_chartSec hL i).repr h s = chartEquiv hL i h s :=
  (isFrame_chartSec hL i).repr_eq h ((chartEquiv hL i h).symm_apply_apply s)

/- English proof (translation)
The claim follows from `sec_ext fun k => by simp only [coord_map, coord_smul, coord_chartSec, resG_resG] rw [mul_comm] exact (resG_cocycle hL k i j _ _ _).symm`.
-/
theorem map_chartSec_change (hL : L.IsLB) (i j : L.ι) {V : X.Opens} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) :
    (toMod L).presheaf.map (homOfLE hj).op (chartSec hL j) =
      resG X (le_inf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        (toMod L).presheaf.map (homOfLE hi).op (chartSec hL i) :=
  sec_ext fun k => by
    simp only [coord_map, coord_smul, coord_chartSec, resG_resG]
    rw [mul_comm]
    exact (resG_cocycle hL k i j _ _ _).symm

def homFun (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) (p : M.ι) (q : L.ι) :
    Γ(X, M.U p ⊓ L.U q) :=
  chartEquiv hM p inf_le_left
    ((toMod M).presheaf.map (homOfLE inf_le_right).op (φ.app _ (chartSec hL q)))

/- English proof (translation)
Rewrite using `[homFun, ← chartEquiv_map, QCoh.res_res, appLinear_apply, app_map]`.
-/
theorem resG_homFun (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) (p : M.ι) (q : L.ι)
    {W : X.Opens} (h : W ≤ M.U p ⊓ L.U q) :
    resG X h (homFun hL hM φ p q) = chartEquiv hM p (h.trans inf_le_left) (appLinear φ W
      ((toMod L).presheaf.map (homOfLE (h.trans inf_le_right)).op (chartSec hL q))) := by
  rw [homFun, ← chartEquiv_map, QCoh.res_res, appLinear_apply, app_map]

def secOfHom (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) : LB.Sec (LB.div M L) where
  f p := homFun hL hM φ p.1 p.2
  compat := by
    rintro ⟨p, q⟩ ⟨p', q'⟩
    let W : X.Opens := M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')
    have hp : W ≤ M.U p ⊓ M.U p' := inf_le_inf inf_le_left inf_le_left
    have hq : W ≤ L.U q ⊓ L.U q' := inf_le_inf inf_le_right inf_le_right
    change resG X (inf_le_left : W ≤ _) (homFun hL hM φ p q) =
      ((res hp (M.g p p') * (res hq (L.g q q'))⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) *
        resG X (inf_le_right : W ≤ _) (homFun hL hM φ p' q')
    rw [resG_homFun, resG_homFun, map_chartSec_change hL q q' (hq.trans inf_le_left), map_smul,
      map_smul, smul_eq_mul, chartEquiv_change hM p p' _ (hp.trans inf_le_right), ← val_res,
      ← val_res, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homCoord_secOfHom (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) (p : M.ι)
    (q : L.ι) : homCoord (secOfHom hL hM φ) p q = homFun hL hM φ p q := rfl

/- English proof (translation)
Use extensionality with `V s : 3`. Use `sec_ext_of_cover hL.cover fun p q => ?_` and prove the remaining obligations. Establish `h₁ : V ⊓ M.U p ⊓ L.U q ≤ V` using `inf_le_left.trans inf_le_left`. Establish `h₂ : V ⊓ M.U p ⊓ L.U q ≤ M.U p` using `inf_le_left.trans inf_le_right`. Establish `e₁` using `chartEquiv_apply hM p h₂ ((toMod M).presheaf.map (homOfLE h₁).op (φ.app V s))`.

Establish `e₂` using `chartEquiv_apply hL q (inf_le_right : V ⊓ M.U p ⊓ L.U q ≤ L.U q) ((toMod L).presheaf.map (homOfLE h₁).op s)`. Rewrite `e₁`, `e₂` using `[coord_map, resG_resG]`. Rewrite using `[coord_homOfSec_app hL hM _ s p q _ (le_inf h₁ inf_le_right) (le_inf h₂ inf_le_right), homCoord_secOfHom, resG_homFun, ← e₁, ← e₂, mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, ← chartEquiv_symm_apply, LinearEquiv.symm_apply_apply, appLinear_apply, app_map]`.
-/
theorem homOfSec_secOfHom (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) :
    homOfSec hL hM (secOfHom hL hM φ) = φ := by
  ext V s : 3
  refine sec_ext_of_cover hL.cover fun p q => ?_
  have h₁ : V ⊓ M.U p ⊓ L.U q ≤ V := inf_le_left.trans inf_le_left
  have h₂ : V ⊓ M.U p ⊓ L.U q ≤ M.U p := inf_le_left.trans inf_le_right
  have e₁ := chartEquiv_apply hM p h₂ ((toMod M).presheaf.map (homOfLE h₁).op (φ.app V s))
  have e₂ := chartEquiv_apply hL q (inf_le_right : V ⊓ M.U p ⊓ L.U q ≤ L.U q)
    ((toMod L).presheaf.map (homOfLE h₁).op s)
  rw [coord_map, resG_resG] at e₁ e₂
  rw [coord_homOfSec_app hL hM _ s p q _ (le_inf h₁ inf_le_right) (le_inf h₂ inf_le_right),
    homCoord_secOfHom, resG_homFun, ← e₁, ← e₂, mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul,
    ← chartEquiv_symm_apply, LinearEquiv.symm_apply_apply, appLinear_apply, app_map]

/- English proof (translation)
Use `f_injective (funext fun ⟨p, q⟩ => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `homFun hL hM _ p q = homCoord w p q`. Rewrite using `[homFun, chartEquiv_apply, coord_map, resG_resG, coord_homOfSec_app hL hM w _ p q _ (le_inf inf_le_right inf_le_right) le_rfl, coord_chartSec, resG_resG, resG_g_self hL, mul_one, resG_self]`.
-/
theorem secOfHom_homOfSec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) :
    secOfHom hL hM (homOfSec hL hM w) = w := by
  refine f_injective (funext fun ⟨p, q⟩ => ?_)
  change homFun hL hM _ p q = homCoord w p q
  rw [homFun, chartEquiv_apply, coord_map, resG_resG,
    coord_homOfSec_app hL hM w _ p q _ (le_inf inf_le_right inf_le_right) le_rfl, coord_chartSec,
    resG_resG, resG_g_self hL, mul_one, resG_self]

def homEquiv (hL : L.IsLB) (hM : M.IsLB) : LB.Sec (LB.div M L) ≃ (toMod L ⟶ toMod M) where
  toFun := homOfSec hL hM
  invFun := secOfHom hL hM
  left_inv := secOfHom_homOfSec hL hM
  right_inv := homOfSec_secOfHom hL hM

/- English proof (translation)
Take `⟨s⟩` from `t`. Take `⟨s'⟩` from `t'`. Use `congr 1`. Conclude with `funext fun i => Units.ext (congrFun (congrArg LB.Sec.f h) i)`.
-/
theorem genSec_injective {t t' : LB.Gen L} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : DVR.genSec t ht = DVR.genSec t' ht') : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  exact funext fun i => Units.ext (congrFun (congrArg LB.Sec.f h) i)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun i => (h i).unit⟩, fun i j => Units.ext (σ.compat i j), rfl⟩`.
-/
theorem exists_genSec_eq (σ : LB.Sec L) (h : ∀ i, IsUnit (σ.f i)) :
    ∃ (t : LB.Gen L) (ht : t.IsGen), DVR.genSec t ht = σ :=
  ⟨⟨fun i => (h i).unit⟩, fun i j => Units.ext (σ.compat i j), rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(isFrame_chartSec hM p).unit ((isFrame_chartSec hL q).app φ) inf_le_left inf_le_right, repr_chartSec hM p _ _⟩`.
-/
theorem isUnit_homFun (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ≅ toMod M) (p : M.ι) (q : L.ι) :
    IsUnit (homFun hL hM φ.hom p q) :=
  ⟨(isFrame_chartSec hM p).unit ((isFrame_chartSec hL q).app φ) inf_le_left inf_le_right,
    repr_chartSec hM p _ _⟩

/- English proof (translation)
Take `⟨w, hw, e⟩` from `exists_genSec_eq (secOfHom hL hM φ.hom) fun p => isUnit_homFun hL hM φ p.1 p.2`. Use `⟨w, ⟨hw, Iso.ext ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `homOfSec hL hM (DVR.genSec w hw) = _`. Rewrite using `[e, homOfSec_secOfHom]`. Introduce and unpack `w' ⟨hw', rfl⟩`.

Conclude with `genSec_injective hw' hw ((secOfHom_homOfSec hL hM _).symm.trans e.symm)`.
-/
theorem existsUnique_gen_of_iso (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ≅ toMod M) :
    ∃! w : LB.Gen (LB.div M L), ∃ hw : w.IsGen, isoOfGen hL hM w hw = φ := by
  obtain ⟨w, hw, e⟩ := exists_genSec_eq (secOfHom hL hM φ.hom)
    fun p => isUnit_homFun hL hM φ p.1 p.2
  refine ⟨w, ⟨hw, Iso.ext ?_⟩, ?_⟩
  · change homOfSec hL hM (DVR.genSec w hw) = _
    rw [e, homOfSec_secOfHom]
  · rintro w' ⟨hw', rfl⟩
    exact genSec_injective hw' hw ((secOfHom_homOfSec hL hM _).symm.trans e.symm)

/- English proof (translation)
Assemble the required witnesses or components as `⟨nonempty_iso_of_lbIso hL hM, fun ⟨φ⟩ => let ⟨w, ⟨hw, _⟩, _⟩ := existsUnique_gen_of_iso hL hM φ ⟨w, hw⟩⟩`.
-/
theorem lbIso_iff_nonempty_iso (hL : L.IsLB) (hM : M.IsLB) :
    LBIso L M ↔ Nonempty (toMod L ≅ toMod M) :=
  ⟨nonempty_iso_of_lbIso hL hM, fun ⟨φ⟩ =>
    let ⟨w, ⟨hw, _⟩, _⟩ := existsUnique_gen_of_iso hL hM φ
    ⟨w, hw⟩⟩

/- English proof (translation)
Use `⟨fun h => exists_genSec_eq σ fun i => ?_, ?_⟩` and prove the remaining obligations. Use `⟨(isFrame_chartSec hL i).unit h le_rfl le_top, ?_⟩` and prove the remaining obligations. Rewrite using `[IsFrame.val_unit, repr_chartSec, map_ofSec, chartEquiv_apply, coord_ofSec, resG_resG, resG_self]`. Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `isFrame_genSec hL ht ⊤`.
-/
theorem isFrame_ofSec_iff (hL : L.IsLB) (σ : LB.Sec L) :
    IsFrame (ofSec σ ⊤) ↔ ∃ (t : LB.Gen L) (ht : t.IsGen), DVR.genSec t ht = σ := by
  refine ⟨fun h => exists_genSec_eq σ fun i => ?_, ?_⟩
  · refine ⟨(isFrame_chartSec hL i).unit h le_rfl le_top, ?_⟩
    rw [IsFrame.val_unit, repr_chartSec, map_ofSec, chartEquiv_apply, coord_ofSec, resG_resG,
      resG_self]
  · rintro ⟨t, ht, rfl⟩
    exact isFrame_genSec hL ht ⊤

/- English proof (translation)
Use `⟨fun ⟨t, ht⟩ => ⟨_, isFrame_genSec hL ht ⊤⟩, fun ⟨e, he⟩ => ?_⟩` and prove the remaining obligations. Take `⟨σ, rfl⟩` from `(globalEquiv L).symm.surjective e`. Take `⟨t, ht, -⟩` from `(isFrame_ofSec_iff hL σ).1 he`. Conclude with `⟨t, ht⟩`.
-/
theorem exists_isGen_iff_isFrame (hL : L.IsLB) :
    (∃ t : LB.Gen L, t.IsGen) ↔ ∃ e : Γ(toMod L, ⊤), IsFrame e := by
  refine ⟨fun ⟨t, ht⟩ => ⟨_, isFrame_genSec hL ht ⊤⟩, fun ⟨e, he⟩ => ?_⟩
  obtain ⟨σ, rfl⟩ := (globalEquiv L).symm.surjective e
  obtain ⟨t, ht, -⟩ := (isFrame_ofSec_iff hL σ).1 he
  exact ⟨t, ht⟩

/- English proof (translation)
Use `⟨fun ⟨t, ht⟩ => ⟨unitIso hL t ht⟩, fun ⟨φ⟩ => (exists_isGen_iff_isFrame hL).2 ?_⟩` and prove the remaining obligations. Establish `h : IsFrame (F` using `unitMod X) (U := ⊤) (1 : Γ(X, ⊤)) := fun V h => by`. Establish `: (fun a : Γ(X, V) => a • (unitMod X).presheaf.map (homOfLE h).op (1 : Γ(X, ⊤))) = fun a : Γ(X, V) => a` using `funext fun a => by`. Express the relevant statement in the definitionally equal form `a * resG X h 1 = a`. Rewrite using `[map_one, mul_one]`.

Rewrite using `[this]`. Conclude with `Function.bijective_id`. Conclude with `⟨_, h.app φ⟩`.
-/
theorem exists_isGen_iff_nonempty_iso (hL : L.IsLB) :
    (∃ t : LB.Gen L, t.IsGen) ↔ Nonempty (unitMod X ≅ toMod L) := by
  refine ⟨fun ⟨t, ht⟩ => ⟨unitIso hL t ht⟩, fun ⟨φ⟩ => (exists_isGen_iff_isFrame hL).2 ?_⟩
  have h : IsFrame (F := unitMod X) (U := ⊤) (1 : Γ(X, ⊤)) := fun V h => by
    have : (fun a : Γ(X, V) => a • (unitMod X).presheaf.map (homOfLE h).op (1 : Γ(X, ⊤))) =
        fun a : Γ(X, V) => a := funext fun a => by
      change a * resG X h 1 = a
      rw [map_one, mul_one]
    rw [this]
    exact Function.bijective_id
  exact ⟨_, h.app φ⟩

end Hom

section Affine

variable {F : X.Modules} {U : X.Opens} {L M : LB X}

/- English proof (translation)
The claim follows from `have H (x : U) := bijective_smul_of_isBaseChange (QCoh.isBaseChange_germLinear F hU x) he fun _ h => Descent.bijective_smul_of_stalk (fun x hx => H ⟨x, hx⟩) h`.
-/
theorem isFrame_of_bijective [F.IsQuasicoherent] (hU : IsAffineOpen U) {e : Γ(F, U)}
    (he : Function.Bijective fun a : Γ(X, U) => a • e) : IsFrame e :=
  have H (x : U) := bijective_smul_of_isBaseChange (QCoh.isBaseChange_germLinear F hU x) he
  fun _ h => Descent.bijective_smul_of_stalk (fun x hx => H ⟨x, hx⟩) h

/- English proof (translation)
Use `⟨fun h => ?_, isFrame_of_bijective hU⟩` and prove the remaining obligations. Use `h U le_rfl` as an intermediate fact. Rewrite `this` using `[QCoh.res_self]`. Then use the resulting hypothesis.
-/
theorem isFrame_iff_bijective [F.IsQuasicoherent] (hU : IsAffineOpen U) (e : Γ(F, U)) :
    IsFrame e ↔ Function.Bijective fun a : Γ(X, U) => a • e := by
  refine ⟨fun h => ?_, isFrame_of_bijective hU⟩
  have := h U le_rfl
  rwa [QCoh.res_self] at this

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_sum_dual_apply_eq_one Γ(X, U) Γ(F, U)`. Establish `hspan : Ideal.span {a : Γ(X, U) | ∃ (ξ : Module.Dual Γ(X, U) Γ(F, U)) (m : Γ(F, U)), ξ m = a} = ⊤`. Rewrite using `[Ideal.eq_top_iff_one, ← hs]`. Conclude with `sum_mem fun p _ => Ideal.subset_span ⟨p.1, p.2, rfl⟩`. Take `⟨⟨_, ξ, m, rfl⟩, hxV⟩` from `Opens.mem_iSup.1 (hU.self_le_iSup_basicOpen_iff.2 hspan hx)`.

Use `hU.isLocalization_basicOpen (ξ m)` as an intermediate fact. Use `QCoh.isLocalizedModule_resBasicOpen F hU (ξ m)` as an intermediate fact. Conclude with `⟨X.basicOpen (ξ m), hxV, QCoh.resBasicOpen F (ξ m) m, isFrame_of_bijective (hU.basicOpen _) (bijective_toSpanSingleton_of_isBaseChange ξ m _ (IsLocalizedModule.isBaseChange (.powers (ξ m)) _ _) (IsLocalization.Away.algebraMap_isUnit (ξ m)))⟩`.
-/
theorem exists_isFrame_of_invertible [F.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Invertible Γ(X, U) Γ(F, U)] {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_ : x ∈ V) (e : Γ(F, V)), IsFrame e := by
  obtain ⟨s, hs⟩ := exists_sum_dual_apply_eq_one Γ(X, U) Γ(F, U)
  have hspan : Ideal.span {a : Γ(X, U) | ∃ (ξ : Module.Dual Γ(X, U) Γ(F, U)) (m : Γ(F, U)),
      ξ m = a} = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hs]
    exact sum_mem fun p _ => Ideal.subset_span ⟨p.1, p.2, rfl⟩
  obtain ⟨⟨_, ξ, m, rfl⟩, hxV⟩ := Opens.mem_iSup.1 (hU.self_le_iSup_basicOpen_iff.2 hspan hx)
  have := hU.isLocalization_basicOpen (ξ m)
  have := QCoh.isLocalizedModule_resBasicOpen F hU (ξ m)
  exact ⟨X.basicOpen (ξ m), hxV, QCoh.resBasicOpen F (ξ m) m,
    isFrame_of_bijective (hU.basicOpen _) (bijective_toSpanSingleton_of_isBaseChange ξ m _
      (IsLocalizedModule.isBaseChange (.powers (ξ m)) _ _)
      (IsLocalization.Away.algebraMap_isUnit (ξ m)))⟩

/- English proof (translation)
Use `isQuasicoherent_toMod hL` as an intermediate fact. Set `s : Set Γ(X, U)` to `{f | ∃ i, X.basicOpen f ≤ L.U i}`. Establish `hs : Ideal.span s = ⊤`. Rewrite using `[← hU.self_le_iSup_basicOpen_iff]`. Introduce `x hx`.

Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))`. Take `⟨f, hf, hxf⟩` from `hU.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ hx`. Conclude with `Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩`. Establish `(f : s)` using `hU.isLocalization_basicOpen f.1`. Establish `(f : s)` using `QCoh.isLocalizedModule_resBasicOpen (toMod L) hU f.1`.

Conclude with `invertible_of_isLocalizedModule_span s hs (fun f => Γ(X, X.basicOpen f.1)) (fun f => Γ(toMod L, X.basicOpen f.1)) (fun f => QCoh.resBasicOpen (toMod L) f.1) fun f => .congr (chartEquiv hL _ f.2.choose_spec).symm`.
-/
theorem invertible_sections (hL : L.IsLB) (hU : IsAffineOpen U) :
    Module.Invertible Γ(X, U) Γ(toMod L, U) := by
  have := isQuasicoherent_toMod hL
  let s : Set Γ(X, U) := {f | ∃ i, X.basicOpen f ≤ L.U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))
    obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ hx
    exact Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
  have (f : s) := hU.isLocalization_basicOpen f.1
  have (f : s) := QCoh.isLocalizedModule_resBasicOpen (toMod L) hU f.1
  exact invertible_of_isLocalizedModule_span s hs (fun f => Γ(X, X.basicOpen f.1))
    (fun f => Γ(toMod L, X.basicOpen f.1)) (fun f => QCoh.resBasicOpen (toMod L) f.1)
    fun f => .congr (chartEquiv hL _ f.2.choose_spec).symm

/- English proof (translation)
Use `isQuasicoherent_toMod hL` as an intermediate fact. Use `invertible_sections hL hU` as an intermediate fact. Simplify using `only [free_iff_exists_bijective_smul, isFrame_iff_bijective hU]`.
-/
theorem exists_isFrame_iff_free (hL : L.IsLB) (hU : IsAffineOpen U) :
    (∃ e : Γ(toMod L, U), IsFrame e) ↔ Module.Free Γ(X, U) Γ(toMod L, U) := by
  have := isQuasicoherent_toMod hL
  have := invertible_sections hL hU
  simp only [free_iff_exists_bijective_smul, isFrame_iff_bijective hU]

/- English proof (translation)
The claim follows from `have := invertible_sections hL (isAffineOpen_top X) .congr (globalEquiv L)`.
-/
theorem invertible_sec_top [IsAffine X] (hL : L.IsLB) : Module.Invertible Γ(X, ⊤) (LB.Sec L) :=
  have := invertible_sections hL (isAffineOpen_top X)
  .congr (globalEquiv L)

/- English proof (translation)
Use `isQuasicoherent_toMod hL` as an intermediate fact. Establish `: (fun a : Γ(X, ⊤) => a • ofSec σ ⊤) = (globalEquiv L).symm ∘ fun a : Γ(X, ⊤) => a • σ` using `funext fun a => (map_smul (globalEquiv L).symm a σ).symm`. Rewrite using `[← isFrame_ofSec_iff hL, isFrame_iff_bijective (isAffineOpen_top X), this, (globalEquiv L).symm.bijective.of_comp_iff']`.
-/
theorem exists_genSec_eq_iff_bijective [IsAffine X] (hL : L.IsLB) (σ : LB.Sec L) :
    (∃ (t : LB.Gen L) (ht : t.IsGen), DVR.genSec t ht = σ) ↔
      Function.Bijective fun a : Γ(X, ⊤) => a • σ := by
  have := isQuasicoherent_toMod hL
  have : (fun a : Γ(X, ⊤) => a • ofSec σ ⊤) =
      (globalEquiv L).symm ∘ fun a : Γ(X, ⊤) => a • σ := funext fun a =>
    (map_smul (globalEquiv L).symm a σ).symm
  rw [← isFrame_ofSec_iff hL, isFrame_iff_bijective (isAffineOpen_top X), this,
    (globalEquiv L).symm.bijective.of_comp_iff']

/- English proof (translation)
Rewrite using `[exists_isGen_iff_isFrame hL, exists_isFrame_iff_free hL (isAffineOpen_top X)]`. Conclude with `⟨fun _ => .of_equiv (globalEquiv L), fun _ => .of_equiv (globalEquiv L).symm⟩`.
-/
theorem exists_isGen_iff_free_top [IsAffine X] (hL : L.IsLB) :
    (∃ t : LB.Gen L, t.IsGen) ↔ Module.Free Γ(X, ⊤) (LB.Sec L) := by
  rw [exists_isGen_iff_isFrame hL, exists_isFrame_iff_free hL (isAffineOpen_top X)]
  exact ⟨fun _ => .of_equiv (globalEquiv L), fun _ => .of_equiv (globalEquiv L).symm⟩

/- English proof (translation)
The claim follows from `have := invertible_sections hL hU (exists_isFrame_iff_free hL hU).2 inferInstance`.
-/
theorem exists_isFrame_of_subsingleton_pic (hL : L.IsLB) (hU : IsAffineOpen U)
    [Subsingleton (CommRing.Pic Γ(X, U))] : ∃ e : Γ(toMod L, U), IsFrame e :=
  have := invertible_sections hL hU
  (exists_isFrame_iff_free hL hU).2 inferInstance

/- English proof (translation)
The claim follows from `(exists_isGen_iff_isFrame hL).2 (exists_isFrame_of_subsingleton_pic hL (isAffineOpen_top X))`.
-/
theorem exists_isGen_of_subsingleton_pic_top [IsAffine X] [Subsingleton (CommRing.Pic Γ(X, ⊤))]
    (hL : L.IsLB) : ∃ t : LB.Gen L, t.IsGen :=
  (exists_isGen_iff_isFrame hL).2 (exists_isFrame_of_subsingleton_pic hL (isAffineOpen_top X))

/- English proof (translation)
The claim follows from `exists_toMod_iso F fun x => exists_isFrame_of_invertible (isAffineOpen_top X) (Opens.mem_top x)`.
-/
theorem exists_toMod_iso_of_invertible [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
    [Module.Invertible Γ(X, ⊤) Γ(F, ⊤)] : ∃ L : LB X, L.IsLB ∧ Nonempty (toMod L ≅ F) :=
  exists_toMod_iso F fun x =>
    exists_isFrame_of_invertible (isAffineOpen_top X) (Opens.mem_top x)

end Affine

section Spectrum

variable {R : Type} [CommRing R] {L M : LB (Sp R)}

variable (R) in

def globalRingEquiv : R ≃+* Γ(Sp R, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem globalRingEquiv_apply (r : R) :
    globalRingEquiv R r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv r := rfl

instance secModuleSp : Module R (LB.Sec L) :=
  Module.compHom (LB.Sec L) (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sp_smul_def (r : R) (σ : LB.Sec L) :
    r • σ = (show Γ(Sp R, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv r) • σ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sp_smul_f (r : R) (σ : LB.Sec L) (i : L.ι) :
    (r • σ).f i = resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) * σ.f i := rfl

/- English proof (translation)
The claim follows from `congrArg (fun a : Γ(Spec S, ⊤) => a • s) (resG_self (X := Spec S) le_top _)`.
-/
theorem spec_smul_top {S : CommRingCat.{0}} (F : (Spec S).Modules) (r : S) (s : Γ(F, ⊤)) :
    r • s = (show Γ(Spec S, ⊤) from (Scheme.ΓSpecIso S).inv r) • s :=
  congrArg (fun a : Γ(Spec S, ⊤) => a • s) (resG_self (X := Spec S) le_top _)

variable (L) in

def globalEquivSp :
    (modulesSpecToSheaf (R := CommRingCat.of R).obj (toMod L)).presheaf.obj (op ⊤) ≃ₗ[R]
      LB.Sec L where
  __ := (globalEquiv L).toAddEquiv
  map_smul' r s := (congrArg (globalEquiv L)
    (spec_smul_top (S := CommRingCat.of R) (toMod L) r s)).trans ((globalEquiv L).map_smul _ s)

/- English proof (translation)
The claim follows from `have := invertible_sec_top hL invertible_of_ringEquiv (globalRingEquiv R).symm fun a σ => by change a • σ = globalRingEquiv R ((globalRingEquiv R).symm a) • σ rw [RingEquiv.apply_symm_apply]`.
-/
theorem invertible_sec (hL : L.IsLB) : Module.Invertible R (LB.Sec L) :=
  have := invertible_sec_top hL
  invertible_of_ringEquiv (globalRingEquiv R).symm fun a σ => by
    change a • σ = globalRingEquiv R ((globalRingEquiv R).symm a) • σ
    rw [RingEquiv.apply_symm_apply]

/- English proof (translation)
The claim follows from `(exists_genSec_eq_iff_bijective hL σ).trans ((globalRingEquiv R).bijective.of_comp_iff (fun a : Γ(Sp R, ⊤) => a • σ)).symm`.
-/
theorem exists_genSec_eq_iff_bijective_sp (hL : L.IsLB) (σ : LB.Sec L) :
    (∃ (t : LB.Gen L) (ht : t.IsGen), DVR.genSec t ht = σ) ↔
      Function.Bijective fun r : R => r • σ :=
  (exists_genSec_eq_iff_bijective hL σ).trans
    ((globalRingEquiv R).bijective.of_comp_iff (fun a : Γ(Sp R, ⊤) => a • σ)).symm

/- English proof (translation)
Use `invertible_sec hL` as an intermediate fact. Simplify using `only [free_iff_exists_bijective_smul, ← exists_genSec_eq_iff_bijective_sp hL]`. Conclude with `⟨fun ⟨t, ht⟩ => ⟨_, t, ht, rfl⟩, fun ⟨_, t, ht, _⟩ => ⟨t, ht⟩⟩`.
-/
theorem exists_isGen_iff_free (hL : L.IsLB) :
    (∃ t : LB.Gen L, t.IsGen) ↔ Module.Free R (LB.Sec L) := by
  have := invertible_sec hL
  simp only [free_iff_exists_bijective_smul, ← exists_genSec_eq_iff_bijective_sp hL]
  exact ⟨fun ⟨t, ht⟩ => ⟨_, t, ht, rfl⟩, fun ⟨_, t, ht, _⟩ => ⟨t, ht⟩⟩

def secEquivOfIso (φ : toMod L ≅ toMod M) : LB.Sec L ≃ₗ[R] LB.Sec M where
  __ := ((globalEquiv L).symm ≪≫ₗ appLinearEquiv φ ⊤ ≪≫ₗ globalEquiv M).toAddEquiv
  map_smul' r σ := map_smul ((globalEquiv L).symm ≪≫ₗ appLinearEquiv φ ⊤ ≪≫ₗ globalEquiv M)
    (globalRingEquiv R r) σ

def tildeSecIso (hL : L.IsLB) :
    tilde (R := CommRingCat.of R) (ModuleCat.of R (LB.Sec L)) ≅ toMod L :=
  haveI := isQuasicoherent_toMod hL
  (tilde.functor (CommRingCat.of R)).mapIso (globalEquivSp L).symm.toModuleIso ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) (toMod L))
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) (toMod L))

/- English proof (translation)
Rewrite using `[lbIso_iff_nonempty_iso hL hM]`. Conclude with `⟨fun ⟨φ⟩ => ⟨secEquivOfIso φ⟩, fun ⟨ψ⟩ => ⟨(tildeSecIso hL).symm ≪≫ (tilde.functor (CommRingCat.of R)).mapIso ψ.toModuleIso ≪≫ tildeSecIso hM⟩⟩`.
-/
theorem lbIso_iff_nonempty_linearEquiv (hL : L.IsLB) (hM : M.IsLB) :
    LBIso L M ↔ Nonempty (LB.Sec L ≃ₗ[R] LB.Sec M) := by
  rw [lbIso_iff_nonempty_iso hL hM]
  exact ⟨fun ⟨φ⟩ => ⟨secEquivOfIso φ⟩, fun ⟨ψ⟩ => ⟨(tildeSecIso hL).symm ≪≫
    (tilde.functor (CommRingCat.of R)).mapIso ψ.toModuleIso ≪≫ tildeSecIso hM⟩⟩

/- English proof (translation)
Establish `: Module.Invertible S Γ(tilde N, ⊤)` using `.congr (tilde.isoTop N).toLinearEquiv`. Establish `: Module.Invertible Γ(Spec S, ⊤) Γ(tilde N, ⊤)` using `invertible_of_ringEquiv (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv (spec_smul_top (tilde N))`. Conclude with `exists_toMod_iso_of_invertible (tilde N)`.
-/
theorem exists_toMod_iso_tilde {S : CommRingCat.{0}} (N : ModuleCat.{0} S)
    [Module.Invertible S N] : ∃ L : LB (Spec S), L.IsLB ∧ Nonempty (toMod L ≅ tilde N) := by
  have : Module.Invertible S Γ(tilde N, ⊤) := .congr (tilde.isoTop N).toLinearEquiv
  have : Module.Invertible Γ(Spec S, ⊤) Γ(tilde N, ⊤) :=
    invertible_of_ringEquiv (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv
      (spec_smul_top (tilde N))
  exact exists_toMod_iso_of_invertible (tilde N)

variable (R) in

/- English proof (translation)
Take `⟨L, hL, ⟨φ⟩⟩` from `exists_toMod_iso_tilde (S := CommRingCat.of R) (ModuleCat.of R (CommRing.Pic.mk R N))`. Establish `ψ` using `(tilde.fullyFaithfulFunctor (R := CommRingCat.of R)).preimageIso (X := ModuleCat.of R (LB.Sec L)) (Y := ModuleCat.of R (CommRing.Pic.mk R N)) (tildeSecIso hL ≪≫ φ)`. Conclude with `⟨L, hL, ⟨ψ.toLinearEquiv ≪≫ₗ CommRing.Pic.mk.linearEquiv R N⟩⟩`.
-/
theorem exists_sec_linearEquiv (N : Type*) [AddCommGroup N] [Module R N] [Module.Invertible R N] :
    ∃ L : LB (Sp R), L.IsLB ∧ Nonempty (LB.Sec L ≃ₗ[R] N) := by
  obtain ⟨L, hL, ⟨φ⟩⟩ := exists_toMod_iso_tilde (S := CommRingCat.of R)
    (ModuleCat.of R (CommRing.Pic.mk R N))
  have ψ := (tilde.fullyFaithfulFunctor (R := CommRingCat.of R)).preimageIso
    (X := ModuleCat.of R (LB.Sec L)) (Y := ModuleCat.of R (CommRing.Pic.mk R N))
    (tildeSecIso hL ≪≫ φ)
  exact ⟨L, hL, ⟨ψ.toLinearEquiv ≪≫ₗ CommRing.Pic.mk.linearEquiv R N⟩⟩

/- English proof (translation)
The claim follows from `haveI := invertible_sec hL (exists_isGen_iff_free hL).2 inferInstance`.
-/
theorem exists_isGen_of_subsingleton_pic [Subsingleton (CommRing.Pic R)] (hL : L.IsLB) :
    ∃ t : LB.Gen L, t.IsGen :=
  haveI := invertible_sec hL
  (exists_isGen_iff_free hL).2 inferInstance

variable (R) in

/- English proof (translation)
Use `⟨fun _ _ => exists_isGen_of_subsingleton_pic, fun h => CommRing.Pic.subsingleton_iff.2 fun N _ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨L, hL, ⟨ψ⟩⟩` from `exists_sec_linearEquiv R N`. Use `haveI := (exists_isGen_iff_free hL).1 (h L hL)`. Conclude with `.of_equiv ψ`.
-/
theorem subsingleton_pic_iff : Subsingleton (CommRing.Pic R) ↔
    ∀ L : LB (Sp R), L.IsLB → ∃ t : LB.Gen L, t.IsGen := by
  refine ⟨fun _ _ => exists_isGen_of_subsingleton_pic, fun h =>
    CommRing.Pic.subsingleton_iff.2 fun N _ _ _ => ?_⟩
  obtain ⟨L, hL, ⟨ψ⟩⟩ := exists_sec_linearEquiv R N
  haveI := (exists_isGen_iff_free hL).1 (h L hL)
  exact .of_equiv ψ

/- English proof (translation)
The claim follows from `exists_isGen_of_subsingleton_pic hL`.
-/
theorem exists_isGen_of_isLocalRing [IsLocalRing R] (hL : L.IsLB) : ∃ t : LB.Gen L, t.IsGen :=
  exists_isGen_of_subsingleton_pic hL

/- English proof (translation)
The claim follows from `exists_isGen_of_subsingleton_pic hL`.
-/
theorem exists_isGen_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] (hL : L.IsLB) :
    ∃ t : LB.Gen L, t.IsGen :=
  exists_isGen_of_subsingleton_pic hL

/- English proof (translation)
The claim follows from `exists_isGen_of_subsingleton_pic hL`.
-/
theorem exists_isGen_of_uniqueFactorizationMonoid [IsDomain R] [UniqueFactorizationMonoid R]
    (hL : L.IsLB) : ∃ t : LB.Gen L, t.IsGen :=
  exists_isGen_of_subsingleton_pic hL

/- English proof (translation)
The claim follows from `exists_isGen_of_subsingleton_pic hL`.
-/
theorem exists_isGen_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    (hL : L.IsLB) : ∃ t : LB.Gen L, t.IsGen :=
  exists_isGen_of_subsingleton_pic hL

end Spectrum

end LB

open LB in

/- English proof (translation)
Use `⟨fun _ => exists_toMod_iso, fun R _ => ⟨fun _ => invertible_sec, fun N _ _ _ => exists_sec_linearEquiv R N, fun _ => exists_isGen_iff_free, fun _ _ => lbIso_iff_nonempty_linearEquiv, ?_⟩, fun _ _ _ => existsUnique_gen_of_iso⟩` and prove the remaining obligations. Introduce and unpack `(_ | _ | ⟨_, _ | _⟩) L hL`. Conclude with `exists_isGen_of_isLocalRing hL`. Conclude with `exists_isGen_of_finite_maximalSpectrum hL`. Conclude with `exists_isGen_of_isPrincipalIdealRing hL`.

Conclude with `exists_isGen_of_uniqueFactorizationMonoid hL`.
-/
theorem invertible_sheaves_and_modules.{v} :
    (∀ (X : Scheme.{0}) (F : X.Modules),
      (∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (e : Γ(F, U)), ∀ (V : X.Opens) (h : V ≤ U),
        Function.Bijective fun a : Γ(X, V) => a • F.presheaf.map (homOfLE h).op e) →
      ∃ L : LB X, L.IsLB ∧ Nonempty (toMod L ≅ F)) ∧
    (∀ (R : Type) [CommRing R],
      (∀ L : LB (Sp R), L.IsLB → Module.Invertible R (LB.Sec L)) ∧
      (∀ (N : Type v) [AddCommGroup N] [Module R N], Module.Invertible R N →
        ∃ L : LB (Sp R), L.IsLB ∧ Nonempty (LB.Sec L ≃ₗ[R] N)) ∧
      (∀ L : LB (Sp R), L.IsLB → ((∃ t : LB.Gen L, t.IsGen) ↔ Module.Free R (LB.Sec L))) ∧
      (∀ L M : LB (Sp R), L.IsLB → M.IsLB →
        (LBIso L M ↔ Nonempty (LB.Sec L ≃ₗ[R] LB.Sec M))) ∧
      ((IsLocalRing R ∨ Finite (MaximalSpectrum R) ∨
          (∃ _ : IsDomain R, IsPrincipalIdealRing R ∨ UniqueFactorizationMonoid R)) →
        ∀ L : LB (Sp R), L.IsLB → ∃ t : LB.Gen L, t.IsGen)) ∧
    (∀ (X : Scheme.{0}) (L M : LB X) (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ≅ toMod M),
      ∃! w : LB.Gen (LB.div M L), ∃ hw : w.IsGen, isoOfGen hL hM w hw = φ) := by
  refine ⟨fun _ => exists_toMod_iso, fun R _ => ⟨fun _ => invertible_sec,
    fun N _ _ _ => exists_sec_linearEquiv R N, fun _ => exists_isGen_iff_free,
    fun _ _ => lbIso_iff_nonempty_linearEquiv, ?_⟩, fun _ _ _ => existsUnique_gen_of_iso⟩
  rintro (_ | _ | ⟨_, _ | _⟩) L hL
  · exact exists_isGen_of_isLocalRing hL
  · exact exists_isGen_of_finite_maximalSpectrum hL
  · exact exists_isGen_of_isPrincipalIdealRing hL
  · exact exists_isGen_of_uniqueFactorizationMonoid hL

end GlobalTheory
