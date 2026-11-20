import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IdentityComponentOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Establish `hs : G.hom ((η[G]).left s) = s`. Establish `h` using `Over.w (η[G])`. Establish `h2 : (𝟙_ (Over S)).hom = 𝟙 S` using `rfl`. Rewrite `h` using `[h2]`. Rewrite using `[← Scheme.Hom.comp_apply, h]`.

Both sides reduce to the same expression. Use `show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))`. Rewrite using `[hs]`. Conclude with `mem_connectedComponentIn hs`.
-/
theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

/- English proof (translation)
Introduce `S G _ hG`. Take `⟨G₀, i, j, h1, h2, h3⟩` from `GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityCompo …`. Use `⟨G₀, i, j, h1, h2, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Both sides reduce to the same expression.
-/
theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
