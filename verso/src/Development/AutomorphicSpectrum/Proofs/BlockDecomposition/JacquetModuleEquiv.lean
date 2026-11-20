import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

/- English proof (translation)
Introduce `F _ _ _ _ n γ V V' _ _ _ _ π π' φ`. Set `e : V ≃ₗ[ℂ] V'` to `φ.toLinearEquiv`. Establish `he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V')`. Introduce `g`. Rewrite using `[Representation.Equiv.toLinearEquiv_toLinearMap]`.

Conclude with `φ.toIntertwiningMap.isIntertwining' g`. Establish `he'` using `LinearEquiv.isIntertwining_symm_isIntertwining he`. Set `f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype)` to `⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩`. Set `g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype)` to `⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩`. Set `M` to `Representation.Coinvariants.map _ _ f`.

Set `M'` to `Representation.Coinvariants.map _ _ g`. Establish `hMM' : M ∘ₗ M' = LinearMap.id`. Apply `Representation.Coinvariants.hom_ext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]`.

Use `congr 1`. Conclude with `e.apply_symm_apply v`. Establish `hM'M : M' ∘ₗ M = LinearMap.id`. Apply `Representation.Coinvariants.hom_ext` to reduce the goal to its premises. Use extensionality with `v`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]`. Use `congr 1`. Conclude with `e.symm_apply_apply v`. Set `E` to `LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M`. Use `⟨Representation.Equiv.mk E ?_⟩` and prove the remaining obligations.

Introduce `m`. Apply `Representation.Coinvariants.hom_ext` to reduce the goal to its premises. Use extensionality with `u`. Establish `hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u)` using `LinearMap.congr_fun (he m) u`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep, GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction, MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate …`.

Rewrite using `[hc]`.
-/
theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
