import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import GroundTheory.AutomorphicForms.MeasuresModulus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory
open scoped NNReal Pointwise

namespace GlobalTheory.DetScale

/- English proof (translation)
Use `haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup k V`. Set `n` to `Module.finrank k V`. Set `e0 : V ≃ₗ[k] (Fin n → k)` to `(Module.finBasis k V).equivFun`. Set `e : V ≃L[k] (Fin n → k)` to `{ e0 with continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }`. Use `borelize (Fin n → k)`.

Set `ν : Measure (Fin n → k)` to `μ.map e`. Use `haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ`. Set `L' : (Fin n → k) ≃ₗ[k] (Fin n → k)` to `(e0.symm.trans L).trans e0`. Use `set c : ℝ≥0 := distribHaarChar k (LinearEquiv.det L) with hc`. Establish `hd : distribHaarChar (Fin n → k) L' = c`.

Rewrite using `[GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, LinearEquiv.det_conj]`. Establish `hc0 : c ≠ 0` using `(distribHaarChar_pos (A := k) (g := LinearEquiv.det L)).ne'`. Set `Lh : V ≃ₜ V` to `{ L.toEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }`. Establish `hν : ∀ s : Set V, ν (e '' s) = μ s` using `fun s => by`. Establish `h` using `e.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (e '' s)`.

Use `h.trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Set.preimage_image_eq s e.injective`. Establish `hm : μ.map Lh.toMeasurableEquiv = c⁻¹ • μ`. Use extensionality with `s _`.

Rewrite using `[MeasurableEquiv.map_apply, Measure.smul_apply, ← hν, ← hν s]`. Establish `h` using `distribHaarChar_mul ν L' (e '' (Lh ⁻¹' s))`. Establish `hs : L' • (e '' (Lh ⁻¹' s)) = e '' s`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Use `⟨L y, hy, ?_⟩` and prove the remaining obligations. Simplify using `[L', e, LinearEquiv.smul_def]`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨e (L.symm y), ⟨L.symm y, ?_, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify `hy` using `[Lh]`. Simplify using `[L', e, LinearEquiv.smul_def]`. Rewrite `h` using `[hs, hd]`. Rewrite using `[← h, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0, ENNReal.coe_one, one_mul]`. Both sides reduce to the same expression.

Establish `e1 : ∫ y, f (L y) ∂μ = ∫ y, f (Lh.toMeasurableEquiv y) ∂μ` using `rfl`. Rewrite using `[e1, ← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem integral_comp_linearEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [TopologicalSpace V] [IsModuleTopology k V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : V ≃ₗ[k] V) (f : V → ℂ) :
    ∫ y, f (L y) ∂μ = (((distribHaarChar k (LinearEquiv.det L) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ∫ y, f y ∂μ := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup k V
  let n := Module.finrank k V
  let e0 : V ≃ₗ[k] (Fin n → k) := (Module.finBasis k V).equivFun
  let e : V ≃L[k] (Fin n → k) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  borelize (Fin n → k)
  let ν : Measure (Fin n → k) := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let L' : (Fin n → k) ≃ₗ[k] (Fin n → k) := (e0.symm.trans L).trans e0
  set c : ℝ≥0 := distribHaarChar k (LinearEquiv.det L) with hc
  have hd : distribHaarChar (Fin n → k) L' = c := by
    rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, LinearEquiv.det_conj]
  have hc0 : c ≠ 0 := (distribHaarChar_pos (A := k) (g := LinearEquiv.det L)).ne'
  let Lh : V ≃ₜ V :=
    { L.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hν : ∀ s : Set V, ν (e '' s) = μ s := fun s => by
    have h := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (e '' s)
    refine h.trans ?_
    congr 1
    exact Set.preimage_image_eq s e.injective
  have hm : μ.map Lh.toMeasurableEquiv = c⁻¹ • μ := by
    ext s _
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, ← hν, ← hν s]
    have h := distribHaarChar_mul ν L' (e '' (Lh ⁻¹' s))
    have hs : L' • (e '' (Lh ⁻¹' s)) = e '' s := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨L y, hy, ?_⟩
        simp [L', e, LinearEquiv.smul_def]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨e (L.symm y), ⟨L.symm y, ?_, rfl⟩, ?_⟩
        · simpa [Lh] using hy
        · simp [L', e, LinearEquiv.smul_def]
    rw [hs, hd] at h
    rw [← h, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0,
      ENNReal.coe_one, one_mul]
    rfl
  have e1 : ∫ y, f (L y) ∂μ = ∫ y, f (Lh.toMeasurableEquiv y) ∂μ := rfl
  rw [e1, ← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

/- English proof (translation)
Introduce `F _ _ _ _ a b L hL φ μ hμ`. Use `letI : MeasurableSpace (Matrix (Fin a) (Fin b) F) := borel _`. Use `haveI : BorelSpace (Matrix (Fin a) (Fin b) F) := ⟨rfl⟩`. Use `haveI : IsModuleTopology F (Matrix (Fin a) (Fin b) F) := show IsModuleTopology F (Fin a → Fin b → F) from inferInstance`. Set `Le` to `LinearMap.equivOfDetNeZero L hL`.

Establish `hdet : LinearEquiv.det Le = Units.mk0 _ hL`. Use `ext`. Rewrite using `[LinearEquiv.coe_det, Units.val_mk0]`. Both sides reduce to the same expression. Establish `h` using `integral_comp_linearEquiv (k := F) μ Le φ`.

Rewrite `h` using `[hdet]`. Conclude with `h`.
-/
theorem integral_comp_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0)
    (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)),
    @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  intro F _ _ _ _ a b L hL φ μ hμ
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) F) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) F) := ⟨rfl⟩
  haveI : IsModuleTopology F (Matrix (Fin a) (Fin b) F) :=
    show IsModuleTopology F (Fin a → Fin b → F) from inferInstance
  let Le := LinearMap.equivOfDetNeZero L hL
  have hdet : LinearEquiv.det Le = Units.mk0 _ hL := by
    ext
    rw [LinearEquiv.coe_det, Units.val_mk0]
    rfl
  have h := integral_comp_linearEquiv (k := F) μ Le φ
  rw [hdet] at h
  exact h

end GlobalTheory.DetScale
