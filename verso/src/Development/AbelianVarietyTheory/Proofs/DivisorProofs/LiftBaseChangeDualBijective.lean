import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.VB GlobalTheory.QCoh
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open scoped TensorProduct

namespace GlobalTheory.ChainPts.SecPair

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {U : X.Opens}

def frameFuns (F : X.Modules) (r : ℕ) (U : X.Opens) : Set Γ(X, U) :=
  {f | ∃ (V : X.Opens) (e : Fin r → Γ(F, V)), IsFrame e ∧ X.basicOpen f ≤ V}

/- English proof (translation)
Rewrite using `[← hU.self_le_iSup_basicOpen_iff]`. Introduce `y hy`. Take `⟨V, e, hyV, he⟩` from `h y`. Take `⟨f, hf, hyf⟩` from `hU.exists_basicOpen_le (V := V) ⟨y, hyV⟩ hy`. Conclude with `Opens.mem_iSup.2 ⟨⟨f, V, e, he, hf⟩, hyf⟩`.
-/
theorem span_frameFuns (h : IsVB F r) (hU : IsAffineOpen U) : Ideal.span (frameFuns F r U) = ⊤ := by
  rw [← hU.self_le_iSup_basicOpen_iff]
  intro y hy
  obtain ⟨V, e, hyV, he⟩ := h y
  obtain ⟨f, hf, hyf⟩ := hU.exists_basicOpen_le (V := V) ⟨y, hyV⟩ hy
  exact Opens.mem_iSup.2 ⟨⟨f, V, e, he, hf⟩, hyf⟩

/- English proof (translation)
Use `haveI := h.isQuasicoherent`. Establish `hs` using `span_frameFuns h hU`. Set `s` to `frameFuns F r U`. Use `haveI (g : s) := hU.isLocalization_basicOpen g.1`. Use `haveI (g : s) := isLocalizedModule_resBasicOpen F hU g.1`.

Establish `b (g : s) : Nonempty (Module.Basis (Fin r) Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1))`. Take `⟨V, e, he, hV⟩` from `g.2`. Conclude with `⟨he.basis hV⟩`. Use `haveI (g : s) : Module.Free Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1) := .of_basis (b g).some`. Use `haveI (g : s) : Module.Finite Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1) := .of_basis (b g).some`.

Use `haveI (g : s) : Module.Flat Γ(X, U) Γ(F, X.basicOpen g.1) := by haveI : Module.Flat Γ(X, U) Γ(X, X.basicOpen g.1) := IsLocalization.flat _ (Submonoid.powers g.1)`. Conclude with `Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen g.1) _`. Use `haveI hfp : Module.FinitePresentation Γ(X, U) Γ(F, U) := Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := fun g : s => Γ(F, X.basicOpen g.1)) (Rₚ := fun g : s => Γ(X, X.basicOpen g.1)) (fun g => resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Flat Γ(X, U) Γ(F, U) := Module.flat_of_isLocalized_span Γ(X, U) Γ(F, U) s hs (fun g : s => Γ(F, X.basicOpen g.1)) (fun g => resBasicOpen F g.1) fun _ => inferInstance`. Conclude with `⟨hfp, Module.Flat.projective_of_finitePresentation⟩`.
-/
theorem finitePresentation_projective (h : IsVB F r) (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(F, U) ∧ Module.Projective Γ(X, U) Γ(F, U) := by
  haveI := h.isQuasicoherent
  have hs := span_frameFuns h hU
  let s := frameFuns F r U
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := isLocalizedModule_resBasicOpen F hU g.1
  have b (g : s) : Nonempty (Module.Basis (Fin r) Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1)) := by
    obtain ⟨V, e, he, hV⟩ := g.2
    exact ⟨he.basis hV⟩
  haveI (g : s) : Module.Free Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1) := .of_basis (b g).some
  haveI (g : s) : Module.Finite Γ(X, X.basicOpen g.1) Γ(F, X.basicOpen g.1) := .of_basis (b g).some
  haveI (g : s) : Module.Flat Γ(X, U) Γ(F, X.basicOpen g.1) := by
    haveI : Module.Flat Γ(X, U) Γ(X, X.basicOpen g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen g.1) _
  haveI hfp : Module.FinitePresentation Γ(X, U) Γ(F, U) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Mₚ := fun g : s => Γ(F, X.basicOpen g.1)) (Rₚ := fun g : s => Γ(X, X.basicOpen g.1))
      (fun g => resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat Γ(X, U) Γ(F, U) :=
    Module.flat_of_isLocalized_span Γ(X, U) Γ(F, U) s hs
      (fun g : s => Γ(F, X.basicOpen g.1)) (fun g => resBasicOpen F g.1) fun _ => inferInstance
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

variable (F U) in

def toForm : Γ(dual F, U) →ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(F, U) where
  toFun l := dualApp l le_rfl
  map_add' _ _ := rfl
  map_smul' a l := by rw [dualApp_smul, GlobalTheory.LB.resG_self]; rfl

/- English proof (translation)
Use `⟨fun l l' H => he.dual_ext hV fun i => congr($H _), fun φ => ?_⟩` and prove the remaining obligations. Use `⟨∑ i, φ (he.basis hV i) • resM (dual F) hV (he.coord i), (he.basis hV).ext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]`. Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `φ _ * dualApp (he.coord j) hV _ = _`.

Rewrite using `[he.dualApp_coord, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]`. Introduce `i _ hij`. Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `φ _ * dualApp (he.coord i) hV _ = _`. Rewrite using `[he.dualApp_coord, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij, mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem toForm_bijective_of_frame {V : X.Opens} {e : Fin r → Γ(F, V)} (he : IsFrame e) (hV : U ≤ V) :
    Function.Bijective (toForm F U) := by
  classical
  refine ⟨fun l l' H => he.dual_ext hV fun i => congr($H _), fun φ => ?_⟩
  refine ⟨∑ i, φ (he.basis hV i) • resM (dual F) hV (he.coord i), (he.basis hV).ext fun j => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [map_smul]
    change φ _ * dualApp (he.coord j) hV _ = _
    rw [he.dualApp_coord, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · intro i _ hij
    rw [map_smul]
    change φ _ * dualApp (he.coord i) hV _ = _
    rw [he.dualApp_coord, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij, mul_zero]
  · simp

/- English proof (translation)
Use `haveI := h.isQuasicoherent`. Use `haveI := h.dual.isQuasicoherent`. Use `haveI := (finitePresentation_projective h hU).1`. Set `s` to `frameFuns F r U`. Use `haveI (g : s) := hU.isLocalization_basicOpen g.1`.

Use `haveI (g : s) := isLocalizedModule_resBasicOpen F hU g.1`. Use `haveI (g : s) := isLocalizedModule_resBasicOpen (dual F) hU g.1`. Set `m (g : s)` to `IsLocalizedModule.mapExtendScalars (.powers g.1) (resBasicOpen F g.1) (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) Γ(X, X.basicOpen g.1)`. Use `haveI (g : s) : IsLocalizedModule.Away g.1 (m g) := Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _`. Use `bijective_of_isLocalized_span s (span_frameFuns h hU) (fun g : s => Γ(dual F, X.basicOpen g.1)) (fun g => resBasicOpen (dual F) g.1) _ m _ fun g => ?_` and prove the remaining obligations.

Establish `key : IsLocalizedModule.map (.powers g.1) (resBasicOpen (dual F) g.1) (m g) (toForm F U) = (toForm F (X.basicOpen g.1)).restrictScalars Γ(X, U)`. Use `IsLocalizedModule.linearMap_ext (.powers g.1) (resBasicOpen (dual F) g.1) (m g) (LinearMap.ext fun l => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, IsLocalizedModule.map_apply]`. Use `LinearMap.restrictScalars_injective Γ(X, U) ?_` and prove the remaining obligations. Use `IsLocalizedModule.linearMap_ext (.powers g.1) (resBasicOpen F g.1) (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) (LinearMap.ext fun t => ?_)` and prove the remaining obligations.

Use `(IsLocalizedModule.map_apply (.powers g.1) (resBasicOpen F g.1) (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) (toForm F U l) t).trans ?_` and prove the remaining obligations. Conclude with `(dualApp_resM l le_rfl (X.basicOpen_le g.1) t).symm`. Rewrite using `[key]`. Take `⟨V, e, he, hV⟩` from `g.2`. Conclude with `toForm_bijective_of_frame he hV`.
-/
theorem toForm_bijective (h : IsVB F r) (hU : IsAffineOpen U) : Function.Bijective (toForm F U) := by
  haveI := h.isQuasicoherent
  haveI := h.dual.isQuasicoherent
  haveI := (finitePresentation_projective h hU).1
  let s := frameFuns F r U
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := isLocalizedModule_resBasicOpen F hU g.1
  haveI (g : s) := isLocalizedModule_resBasicOpen (dual F) hU g.1
  let m (g : s) := IsLocalizedModule.mapExtendScalars (.powers g.1) (resBasicOpen F g.1)
    (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) Γ(X, X.basicOpen g.1)
  haveI (g : s) : IsLocalizedModule.Away g.1 (m g) :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  refine bijective_of_isLocalized_span s (span_frameFuns h hU) (fun g : s => Γ(dual F, X.basicOpen g.1))
    (fun g => resBasicOpen (dual F) g.1) _ m _ fun g => ?_
  have key : IsLocalizedModule.map (.powers g.1) (resBasicOpen (dual F) g.1) (m g) (toForm F U) =
      (toForm F (X.basicOpen g.1)).restrictScalars Γ(X, U) := by
    refine IsLocalizedModule.linearMap_ext (.powers g.1) (resBasicOpen (dual F) g.1) (m g) (LinearMap.ext fun l => ?_)
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    refine LinearMap.restrictScalars_injective Γ(X, U) ?_
    refine IsLocalizedModule.linearMap_ext (.powers g.1) (resBasicOpen F g.1)
      (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) (LinearMap.ext fun t => ?_)
    refine (IsLocalizedModule.map_apply (.powers g.1) (resBasicOpen F g.1)
      (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g.1)) (toForm F U l) t).trans ?_
    exact (dualApp_resM l le_rfl (X.basicOpen_le g.1) t).symm
  rw [key]
  obtain ⟨V, e, he, hV⟩ := g.2
  exact toForm_bijective_of_frame he hV

/- English proof (translation)
Set `e : (M →ₗ[R] A) ≃ₗ[A] (A ⊗[R] M →ₗ[A] A)` to `LinearMap.liftBaseChangeEquiv A`. Establish `: ⇑(LinearMap.liftBaseChange A (Module.Dual.baseChange (R` using `R) (V := M) A)) = e ∘ dualTensorHom R M A ∘ TensorProduct.comm R _ _ := by`. Use function extensionality and compare the values at `x`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `tmul a φ`. Use `TensorProduct.AlgebraTensorModule.ext fun b m => ?_` and prove the remaining obligations. Simplify using `[e, mul_comm]`.

Rewrite using `[this]`. Conclude with `(LinearEquiv.bijective _).comp <| dualTensorHom_bijective.comp (LinearEquiv.bijective _)`.
-/
theorem liftBaseChange_dual_bijective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (LinearMap.liftBaseChange A (Module.Dual.baseChange (R := R) (V := M) A)) := by
  let e : (M →ₗ[R] A) ≃ₗ[A] (A ⊗[R] M →ₗ[A] A) := LinearMap.liftBaseChangeEquiv A
  have : ⇑(LinearMap.liftBaseChange A (Module.Dual.baseChange (R := R) (V := M) A)) =
      e ∘ dualTensorHom R M A ∘ TensorProduct.comm R _ _ := by
    funext x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul a φ =>
      refine TensorProduct.AlgebraTensorModule.ext fun b m => ?_
      simp [e, mul_comm]
  rw [this]
  exact (LinearEquiv.bijective _).comp <| dualTensorHom_bijective.comp (LinearEquiv.bijective _)

/- English proof (translation)
Take `⟨h₁, h₂⟩` from `finitePresentation_projective h hU`. Use `⟨inferInstance, inferInstance, LinearMap.liftBaseChange A (Module.Dual.baseChange A) ∘ₗ ((LinearEquiv.ofBijective _ (toForm_bijective h hU)).baseChange _ A _ _).toLinearMap, (liftBaseChange_dual_bijective _ A _).comp (LinearEquiv.bijective _), fun y w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = algebraMap Γ(X, U) A (toForm F U y w)`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem pairing_baseChange (h : IsVB F r) (hU : IsAffineOpen U) (A : Type) [CommRing A] [Algebra Γ(X, U) A] :
    Module.Finite A (A ⊗[Γ(X, U)] Γ(F, U)) ∧ Module.Projective A (A ⊗[Γ(X, U)] Γ(F, U)) ∧
    ∃ pr : A ⊗[Γ(X, U)] Γ(dual F, U) →ₗ[A] Module.Dual A (A ⊗[Γ(X, U)] Γ(F, U)),
      Function.Bijective pr ∧ ∀ y w, pr (1 ⊗ₜ y) (1 ⊗ₜ w) = algebraMap Γ(X, U) A (dualApp y le_rfl w) := by
  obtain ⟨h₁, h₂⟩ := finitePresentation_projective h hU
  refine ⟨inferInstance, inferInstance,
    LinearMap.liftBaseChange A (Module.Dual.baseChange A) ∘ₗ
      ((LinearEquiv.ofBijective _ (toForm_bijective h hU)).baseChange _ A _ _).toLinearMap,
    (liftBaseChange_dual_bijective _ A _).comp (LinearEquiv.bijective _), fun y w => ?_⟩
  change _ = algebraMap Γ(X, U) A (toForm F U y w)
  simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Introduce `_ _ _ _ h U` and use `pairing_baseChange h U.2.1 U.Bp`.
-/
theorem pairSt : GlobalTheory.ChainPts.SysB.PairSt := fun _ _ _ _ h U => pairing_baseChange h U.2.1 U.Bp

end GlobalTheory.ChainPts.SecPair

end
