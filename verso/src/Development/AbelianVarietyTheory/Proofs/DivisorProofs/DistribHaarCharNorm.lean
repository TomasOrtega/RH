import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
import GroundTheory.AutomorphicForms.MeasuresModulus

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.FunExt GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LBCNu

open MeasureTheory

/- English proof (translation)
Set `b` to `Module.finBasis k k'`. Set `e : k' ≃ₗ[k] (Fin (Module.finrank k k') → k)` to `b.equivFun`. Set `e' : k' ≃ₜ+ (Fin (Module.finrank k k') → k)` to `{ e.toAddEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }`. Set `M : k' ≃ₗ[k] k'` to `LinearEquiv.ofLinear (LinearMap.mulLeft k (z : k')) (LinearMap.mulLeft k ((z⁻¹ : k'ˣ) : k')) (by ext x; simp) (by ext x; simp)`. Set `Lz : (Fin (Module.finrank k k') → k) ≃ₗ[k] (Fin (Module.finrank k k') → k)` to `(e.symm.trans M).trans e`.

Establish `h1 : distribHaarChar (Fin (Module.finrank k k') → k) Lz = distribHaarChar k' z` using `GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e' z Lz (fun x => by show e ((z : k') * x) = e (M (e.symm (e x)))`. Simplify using `[M])`. Rewrite using `[← h1, GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq]`. Use `congr 1`. Use `ext`.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe, LinearEquiv.coe_det, Lz, Algebra.norm_apply]`. Use `symm`. Use `show LinearMap.det (e.toLinearMap ∘ₗ M.toLinearMap ∘ₗ e.symm.toLinearMap) = _`. Rewrite using `[LinearMap.det_conj]`. Both sides reduce to the same expression.
-/
theorem distribHaarChar_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (z : k'ˣ) :
    distribHaarChar k (Units.map (Algebra.norm k : k' →* k) z) = distribHaarChar k' z := by
  let b := Module.finBasis k k'
  let e : k' ≃ₗ[k] (Fin (Module.finrank k k') → k) := b.equivFun
  let e' : k' ≃ₜ+ (Fin (Module.finrank k k') → k) :=
    { e.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  let M : k' ≃ₗ[k] k' := LinearEquiv.ofLinear (LinearMap.mulLeft k (z : k')) (LinearMap.mulLeft k ((z⁻¹ : k'ˣ) : k'))
    (by ext x; simp) (by ext x; simp)
  let Lz : (Fin (Module.finrank k k') → k) ≃ₗ[k] (Fin (Module.finrank k k') → k) := (e.symm.trans M).trans e
  have h1 : distribHaarChar (Fin (Module.finrank k k') → k) Lz = distribHaarChar k' z :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e' z Lz (fun x => by
      show e ((z : k') * x) = e (M (e.symm (e x)))
      simp [M])
  rw [← h1, GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, LinearEquiv.coe_det, Lz, Algebra.norm_apply]
  symm
  show LinearMap.det (e.toLinearMap ∘ₗ M.toLinearMap ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj]
  rfl

open GlobalTheory.SmGL GlobalTheory.SplitWeil in

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [MonoidHom.comp_apply, val_absPow, nabs, distribHaarChar_norm]`.
-/
theorem absPow_comp_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (t : ℂ) :
    (absPow k t).comp (Units.map (Algebra.norm k : k' →* k)) = absPow k' t := by
  ext z
  simp only [MonoidHom.comp_apply, val_absPow, nabs, distribHaarChar_norm]

end GlobalTheory.LBCNu
