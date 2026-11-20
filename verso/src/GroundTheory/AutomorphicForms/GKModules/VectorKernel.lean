import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

namespace GroundTheory.Automorphic

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

/- English proof (translation)
Establish `e : (fun Y : 𝔤 => π (g * h.expG Y) v) = ((π g).restrictScalars ℝ) ∘ h.expOrbit π v`. Use function extensionality and compare the values at `Y`. Simplify using `[expOrbit]`. Establish `hd` using `(h.differentiable_expOrbit π hv 0).hasFDerivAt`. Establish `hc` using `((π g).restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤) hd`.

Unfold `rightDeriv`. Rewrite using `[e, hc.fderiv]`. Both sides reduce to the same expression.
-/
theorem rightDeriv_orbit {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) (g : G) :
    h.rightDeriv X (fun g => π g v) g = π g (h.derivOp π X v) := by
  have e : (fun Y : 𝔤 => π (g * h.expG Y) v) = ((π g).restrictScalars ℝ) ∘ h.expOrbit π v := by
    funext Y
    simp [expOrbit]
  have hd := (h.differentiable_expOrbit π hv 0).hasFDerivAt
  have hc := ((π g).restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤) hd
  unfold rightDeriv
  rw [e, hc.fderiv]
  rfl

def orbitL : h.smoothVectors π →ₗ[ℂ] h.smoothFuns (F := E) where
  toFun v := ⟨fun g => π g v, v.2⟩
  map_add' v w := by
    apply Subtype.ext
    funext g
    simp
  map_smul' c v := by
    apply Subtype.ext
    funext g
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_orbitL (v : h.smoothVectors π) :
    ((h.orbitL π v : h.smoothFuns (F := E)) : G → E) = fun g => π g v := rfl

/- English proof (translation)
Take `⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u` from `RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u`. Proceed by induction on `t using TensorAlgebra.induction generalizing v with`. Consider the case `algebraMap r`. Rewrite using `[AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Simplify using `[Module.algebraMap_end_apply]`. Consider the case `ι X`. Express the relevant statement in the definitionally equal form `h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ X) (h.orbitL π v) = h.orbitL π (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ X) v)`. Rewrite using `[rightUAction_ι, uAction_ι]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Conclude with `h.rightDeriv_orbit π v.2 (h.ofLie X) g`. Consider the case `mul a b ha hb`. Rewrite using `[map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]`.

Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, map_add]`.
-/
theorem rightUAction_orbitL (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra)
    (v : h.smoothVectors π) :
    h.rightUAction u (h.orbitL π v) = h.orbitL π (h.uAction π u v) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing v with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    apply Subtype.ext
    funext g
    simp [Module.algebraMap_end_apply]
  | ι X =>
    change h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ X) (h.orbitL π v) =
      h.orbitL π (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ X) v)
    rw [rightUAction_ι, uAction_ι]
    apply Subtype.ext
    funext g
    exact h.rightDeriv_orbit π v.2 (h.ofLie X) g
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, map_add]

def dualComp (l : StrongDual ℂ E) : h.smoothFuns (F := E) →ₗ[ℂ] h.smoothFuns (F := ℂ) where
  toFun f := ⟨fun g => l ((f : G → E) g), by
    show h.IsSmoothFun (fun g => l ((f : G → E) g))
    let _ := h.chartedSpace
    have hf : h.IsSmoothFun (f : G → E) := f.2
    exact (l.restrictScalars ℝ).contDiff.comp_contMDiff hf⟩
  map_add' f f' := by
    apply Subtype.ext
    funext g
    simp
  map_smul' c f := by
    apply Subtype.ext
    funext g
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_dualComp (l : StrongDual ℂ E) (f : h.smoothFuns (F := E)) :
    ((h.dualComp l f : h.smoothFuns (F := ℂ)) : G → ℂ) = fun g => l ((f : G → E) g) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Simplify using `only [coe_dualComp, coe_rightDerivEnd]`. Establish `hf : h.IsSmoothFun (f : G → E)` using `f.2`. Establish `e : (fun Y : 𝔤 => l ((f : G → E) (g * h.expG Y))) = (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y)` using `rfl`.

Establish `hc` using `(l.restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤) (h.differentiable_comp_expG hf g 0).hasFDerivAt`. Unfold `rightDeriv`. Rewrite using `[show (fun Y : 𝔤 => (fun g => l ((f : G → E) g)) (g * h.expG Y)) = (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y) from e, hc.fderiv]`. Both sides reduce to the same expression.
-/
theorem dualComp_rightDerivEnd (l : StrongDual ℂ E) (X : 𝔤) (f : h.smoothFuns (F := E)) :
    h.dualComp l (h.rightDerivEnd X f) = h.rightDerivEnd X (h.dualComp l f) := by
  apply Subtype.ext
  funext g
  simp only [coe_dualComp, coe_rightDerivEnd]
  have hf : h.IsSmoothFun (f : G → E) := f.2
  have e : (fun Y : 𝔤 => l ((f : G → E) (g * h.expG Y))) =
      (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y) := rfl
  have hc := (l.restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤)
    (h.differentiable_comp_expG hf g 0).hasFDerivAt
  unfold rightDeriv
  rw [show (fun Y : 𝔤 => (fun g => l ((f : G → E) g)) (g * h.expG Y)) =
    (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y) from e, hc.fderiv]
  rfl

/- English proof (translation)
Simplify using `only [laplacian, LinearMap.sum_apply, map_sum, Module.End.mul_apply, dualComp_rightDerivEnd]`.
-/
theorem dualComp_laplacian (l : StrongDual ℂ E) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ h.lieSubalgebra) (f : h.smoothFuns (F := E)) :
    h.dualComp l (h.laplacian (F := E) b f) = h.laplacian (F := ℂ) b (h.dualComp l f) := by
  simp only [laplacian, LinearMap.sum_apply, map_sum, Module.End.mul_apply, dualComp_rightDerivEnd]

variable [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Set `T : E →ₗ[ℂ] (G → E)` to `{ toFun := fun w g => π g w map_add' := fun w w' => by funext g; simp map_smul' := fun c w => by funext g; simp }`. Use `set o := h.orbitL π v with ho`. Establish `hfK : IsRightKFinite Kc (o : G → E)`. Unfold `IsRightKFinite`. Establish `e : Set.range (fun k : Kc => rightTranslate (k : G) (o : G → E)) = T '' Set.range (fun k : Kc => π k (v : E))`.

Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Use `⟨_, ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Simplify using `[T, ho, rightTranslate]`. Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `[T, ho, rightTranslate]`.

Rewrite using `[e, Submodule.span_image]`. Use `infer_instance`. Establish `hfZ : h.IsZFinite o`. Unfold `IsZFinite`. Establish `e : (fun z => h.rightUAction z o) '' (h.centerU : Set _) = h.orbitL π '' ((fun z => h.uAction π z v) '' (h.centerU : Set _))`.

Rewrite using `[Set.image_image]`. Use `Set.image_congr fun z _ => ?_` and prove the remaining obligations. Conclude with `h.rightUAction_orbitL π z v`. Rewrite using `[e, Submodule.span_image]`. Use `infer_instance`.

Take `⟨P, hPm, hPd, hP⟩` from `h.exists_aeval_laplacian_eq_zero Kc B b ε hε horth hsymm hinv hK o hfK hfZ`. Take `⟨κ, hκs, hκc, hκU, hκ⟩` from `h.exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd hU`. Establish `htest : h.IsTestFunction κ` using `⟨hκs, hκc⟩`. Use `⟨κ, htest, hκU, ?_⟩` and prove the remaining obligations. Use `(SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun l => ?_` and prove the remaining obligations.

Establish `hζ : Polynomial.aeval (h.laplacian (F` using `ℂ) b) P (h.dualComp l o) = 0 := by`. Rewrite using `[← AutomorphicForm.map_aeval_apply_of_intertwine (h.dualComp l) (fun f => h.dualComp_laplacian l b f) P o, hP, map_zero]`. Establish `h1` using `hκ (h.dualComp l o) hζ 1`. Simplify using `only [coe_dualComp, ho, coe_orbitL, one_mul, BanachRep.map_one_apply] at h1`. Rewrite using `[BanachRep.integrated, ← l.integral_comp_comm (h.integrable_smul_orbit π μ htest v), h1]`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem exists_integrated_eq_of_zkFinite [CompleteSpace E] (μ : Measure G) [μ.IsHaarMeasure]
    (Kc : Subgroup G) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℝ h.lieSubalgebra) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : h.lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : h.lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ Kc)
    (v : h.smoothVectors π)
    (hvK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc => π k (v : E))))
    (hvZ : FiniteDimensional ℂ
      (Submodule.span ℂ ((fun z => h.uAction π z v) '' (h.centerU : Set _))))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, h.IsTestFunction κ ∧ tsupport κ ⊆ U ∧ π.integrated μ κ v = v := by

  let T : E →ₗ[ℂ] (G → E) :=
    { toFun := fun w g => π g w
      map_add' := fun w w' => by funext g; simp
      map_smul' := fun c w => by funext g; simp }
  set o := h.orbitL π v with ho
  have hfK : IsRightKFinite Kc (o : G → E) := by
    unfold IsRightKFinite
    have e : Set.range (fun k : Kc => rightTranslate (k : G) (o : G → E)) =
        T '' Set.range (fun k : Kc => π k (v : E)) := by
      ext f
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨_, ⟨k, rfl⟩, ?_⟩
        funext g
        simp [T, ho, rightTranslate]
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        refine ⟨k, ?_⟩
        funext g
        simp [T, ho, rightTranslate]
    rw [e, Submodule.span_image]
    infer_instance
  have hfZ : h.IsZFinite o := by
    unfold IsZFinite
    have e : (fun z => h.rightUAction z o) '' (h.centerU : Set _) =
        h.orbitL π '' ((fun z => h.uAction π z v) '' (h.centerU : Set _)) := by
      rw [Set.image_image]
      refine Set.image_congr fun z _ => ?_
      exact h.rightUAction_orbitL π z v
    rw [e, Submodule.span_image]
    infer_instance
  obtain ⟨P, hPm, hPd, hP⟩ :=
    h.exists_aeval_laplacian_eq_zero Kc B b ε hε horth hsymm hinv hK o hfK hfZ
  obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := h.exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd hU
  have htest : h.IsTestFunction κ := ⟨hκs, hκc⟩
  refine ⟨κ, htest, hκU, ?_⟩
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun l => ?_
  have hζ : Polynomial.aeval (h.laplacian (F := ℂ) b) P (h.dualComp l o) = 0 := by
    rw [← AutomorphicForm.map_aeval_apply_of_intertwine (h.dualComp l)
      (fun f => h.dualComp_laplacian l b f) P o, hP, map_zero]
  have h1 := hκ (h.dualComp l o) hζ 1
  simp only [coe_dualComp, ho, coe_orbitL, one_mul, BanachRep.map_one_apply] at h1
  rw [BanachRep.integrated, ← l.integral_comp_comm (h.integrable_smul_orbit π μ htest v), h1]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

end IsExpLieAlgebra

end

end GroundTheory.Automorphic
