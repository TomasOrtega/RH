import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

/- English proof (translation)
Introduce `E _ _ _ n w hw b b' ϖ ϖ' q q' σ α α' hb hb' hϖ hϖ' hU hU' hS hS'`. Take `⟨p, σ₁, hp, hα, ⟨e1⟩⟩` from `hS`. Take `⟨p', σ₂, hp', hα', ⟨e2⟩⟩` from `hS'`. Establish `hq : q = q'` using `Nat.pow_left_injective two_ne_zero (hU.2.2.2.2.2.2.symm.trans hU'.2.2.2.2.2.2)`. Substitute `hq` using the available equality.

Establish `hb2 : cT (cj w) b.1 * b.1 = antiJ _ n` using `hb.2`. Establish `hb'2 : cT (cj w) b'.1 * b'.1 = antiJ _ n` using `hb'.2`. Establish `hkm : b⁻¹ * b' ∈ GU (cj w) n`. Establish `hc : cT (cj w) (b⁻¹).1 * cT (cj w) b.1 = 1` using `by rw [← cT_mul, Units.mul_inv, cT_one]`. Establish `hd : b.1 * (b⁻¹).1 = 1` using `Units.mul_inv b`.

Express the relevant statement in the definitionally equal form `_ * _ * _ = _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, cT_mul, ← hb2]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = antiJ _ n := by rw [hc, hd, Matrix.mul_one, Matrix.mul_one, hb'2]`.

Set `k : GU (cj w) n` to `⟨b⁻¹ * b', hkm⟩`. Establish `hcomm : ∀ u, p u * k = k * p' u` using `fun u => Subtype.ext (by`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, hp, hp']`. Use `show b⁻¹ * u.1 * b * (b⁻¹ * b') = b⁻¹ * b' * (b'⁻¹ * u.1 * b')`. Use the proof step `group)`.

Set `L1` to `e1.toLinearEquiv`. Set `L2` to `e2.toLinearEquiv`. Establish `h1 : ∀ g v, L1 (σ.ρ g v) = σ₁.ρ (p g) (L1 v)` using `fun g v => LinearMap.congr_fun (e1.isIntertwining' g) v`. Establish `h2 : ∀ g v, L2 (σ.ρ g v) = σ₂.ρ (p' g) (L2 v)` using `fun g v => LinearMap.congr_fun (e2.isIntertwining' g) v`. Set `F : σ₁.V →ₗ[ℂ] σ₂.V` to `L2.toLinearMap ∘ₗ L1.symm.toLinearMap ∘ₗ σ₁.ρ k`.

Establish `hF : ∀ g y, F (σ₁.ρ g y) = σ₂.ρ g (F y)`. Introduce `g y`. Take `⟨u, rfl⟩` from `p'.surjective g`. Establish `e : ∀ z, L1.symm (σ₁.ρ (p u) z) = σ.ρ u (L1.symm z)` using `fun z => by`. Apply `L1.injective` to reduce the goal to its premises.

Rewrite using `[h1, L1.apply_symm_apply, L1.apply_symm_apply]`. Simplify using `only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← hcomm u, map_mul, Module.End.mul_apply, e, h2]`. Establish `hkinj : Function.Injective (σ₁.ρ k)` using `fun a c h => by`. Establish `h'` using `congrArg (σ₁.ρ k⁻¹) h`.

Rewrite `h'` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Then use the resulting hypothesis. Establish `hFinj : Function.Injective F` using `L2.injective.comp (L1.symm.injective.comp hkinj)`. Take `⟨x, hx⟩` from `hα.exists_vec`. Establish `hFx : F x ≠ 0` using `fun h => hx.1 (hFinj (h.trans (map_zero F).symm))`. Establish `h2x : GlobalTheory.LFun.IsSatVecU (ϖ : w.adicCompletion E) q σ₂.ρ (F x) α` using `hx.map hU F hF hFx`.

Establish `h3 : GlobalTheory.LFun.IsSatVecU (ϖ' : w.adicCompletion E) q σ₂.ρ (F x) α` using `h2x.of_unif hU hU'`. Conclude with `h3.unique hU' (hα'.2 _ h2x.2.1 hFx)`.
-/
theorem satUniq : SatUniq := by
  intro E _ _ _ n w hw b b' ϖ ϖ' q q' σ α α' hb hb' hϖ hϖ' hU hU' hS hS'
  obtain ⟨p, σ₁, hp, hα, ⟨e1⟩⟩ := hS
  obtain ⟨p', σ₂, hp', hα', ⟨e2⟩⟩ := hS'
  have hq : q = q' := Nat.pow_left_injective two_ne_zero (hU.2.2.2.2.2.2.symm.trans hU'.2.2.2.2.2.2)
  subst hq
  have hb2 : cT (cj w) b.1 * b.1 = antiJ _ n := hb.2
  have hb'2 : cT (cj w) b'.1 * b'.1 = antiJ _ n := hb'.2
  have hkm : b⁻¹ * b' ∈ GU (cj w) n := by
    have hc : cT (cj w) (b⁻¹).1 * cT (cj w) b.1 = 1 := by rw [← cT_mul, Units.mul_inv, cT_one]
    have hd : b.1 * (b⁻¹).1 = 1 := Units.mul_inv b
    change _ * _ * _ = _
    calc cT (cj w) (b⁻¹ * b').1 * antiJ _ n * (b⁻¹ * b').1
        = cT (cj w) b'.1 * (cT (cj w) (b⁻¹).1 * cT (cj w) b.1) * (b.1 * (b⁻¹).1) * b'.1 := by
          rw [Units.val_mul, cT_mul, ← hb2]; simp only [Matrix.mul_assoc]
      _ = antiJ _ n := by rw [hc, hd, Matrix.mul_one, Matrix.mul_one, hb'2]
  let k : GU (cj w) n := ⟨b⁻¹ * b', hkm⟩
  have hcomm : ∀ u, p u * k = k * p' u := fun u => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hp, hp']
    show b⁻¹ * u.1 * b * (b⁻¹ * b') = b⁻¹ * b' * (b'⁻¹ * u.1 * b')
    group)
  let L1 := e1.toLinearEquiv
  let L2 := e2.toLinearEquiv
  have h1 : ∀ g v, L1 (σ.ρ g v) = σ₁.ρ (p g) (L1 v) := fun g v => LinearMap.congr_fun (e1.isIntertwining' g) v
  have h2 : ∀ g v, L2 (σ.ρ g v) = σ₂.ρ (p' g) (L2 v) := fun g v => LinearMap.congr_fun (e2.isIntertwining' g) v
  let F : σ₁.V →ₗ[ℂ] σ₂.V := L2.toLinearMap ∘ₗ L1.symm.toLinearMap ∘ₗ σ₁.ρ k
  have hF : ∀ g y, F (σ₁.ρ g y) = σ₂.ρ g (F y) := by
    intro g y
    obtain ⟨u, rfl⟩ := p'.surjective g
    have e : ∀ z, L1.symm (σ₁.ρ (p u) z) = σ.ρ u (L1.symm z) := fun z => by
      apply L1.injective
      rw [h1, L1.apply_symm_apply, L1.apply_symm_apply]
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, ← hcomm u, map_mul, Module.End.mul_apply, e, h2]
  have hkinj : Function.Injective (σ₁.ρ k) := fun a c h => by
    have h' := congrArg (σ₁.ρ k⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one] at h'
  have hFinj : Function.Injective F := L2.injective.comp (L1.symm.injective.comp hkinj)
  obtain ⟨x, hx⟩ := hα.exists_vec
  have hFx : F x ≠ 0 := fun h => hx.1 (hFinj (h.trans (map_zero F).symm))
  have h2x : GlobalTheory.LFun.IsSatVecU (ϖ : w.adicCompletion E) q σ₂.ρ (F x) α := hx.map hU F hF hFx
  have h3 : GlobalTheory.LFun.IsSatVecU (ϖ' : w.adicCompletion E) q σ₂.ρ (F x) α := h2x.of_unif hU hU'
  exact h3.unique hU' (hα'.2 _ h2x.2.1 hFx)

end PositivityTheory.Rg.BcB.F.Inert

end
