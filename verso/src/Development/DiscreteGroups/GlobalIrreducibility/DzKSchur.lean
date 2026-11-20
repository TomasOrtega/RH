import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

open CategoryTheory

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Take `⟨V, hV, hch⟩` from `h`. Rewrite `hV`, the goal using `[FDRep.simple_iff_char_is_norm_one]`. Simplify `hV` using `only [hch]`.
-/
theorem simple_of_isIrr (τ : FDRep ℂ G) (h : GlobalTheory.GLq.IsIrr τ.character) : Simple τ := by
  obtain ⟨V, hV, hch⟩ := h
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [hch] using hV

/- English proof (translation)
Set `A : τ →ₗ[ℂ] τ` to `∑ y, f y • τ.ρ y⁻¹`. Establish `hAapp : ∀ v, A v = ∑ y, f y • τ.ρ y⁻¹ v` using `fun v => by`. Simplify using `only [A, LinearMap.sum_apply, LinearMap.smul_apply]`. Establish `hA : ∀ h, A ∘ₗ τ.ρ h = τ.ρ h ∘ₗ A`. Introduce `h`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hAapp, hAapp, map_sum]`. Rewrite using `[← Equiv.sum_comp (MulAut.conj h).toEquiv]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `e1 : f ((MulAut.conj h).toEquiv y) = f y`.

Simplify using `using hf y h`. Rewrite using `[e1, map_smul]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`.

Simplify using `[mul_assoc]`. Set `F : τ ⟶ τ` to `⟨FGModuleCat.ofHom A, fun g => by`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `A (τ.ρ g x) = τ.ρ g (A x)`. Conclude with `LinearMap.congr_fun (hA g) x⟩`.

Take `⟨c, hc⟩` from `endomorphism_simple_eq_smul_id ℂ F`. Establish `hAv : ∀ v, A v = c • v` using `fun v => by`. Establish `: F.hom.hom.hom v = c • v` using `by rw [← hc]; rfl`. Conclude with `this`. Use `⟨c, fun v => by rw [← hAv, hAapp], ?_⟩` and prove the remaining obligations.

Establish `hAc : A = c • LinearMap.id` using `LinearMap.ext fun v => by rw [hAv]; rfl`. Establish `htr : LinearMap.trace ℂ τ A = c * Module.finrank ℂ τ`. Rewrite using `[hAc, map_smul, LinearMap.trace_id, smul_eq_mul]`. Rewrite using `[← htr]`. Simplify using `only [A, map_sum, map_smul, smul_eq_mul]`.

Both sides reduce to the same expression.
-/
theorem central_scalar (τ : FDRep ℂ G) [Simple τ] (f : G → ℂ) (hf : ∀ x y : G, f (y * x * y⁻¹) = f x) :
    ∃ c : ℂ, (∀ v : τ, ∑ y, f y • τ.ρ y⁻¹ v = c • v) ∧
      c * (Module.finrank ℂ τ : ℂ) = ∑ y, f y * τ.character y⁻¹ := by
  classical
  let A : τ →ₗ[ℂ] τ := ∑ y, f y • τ.ρ y⁻¹
  have hAapp : ∀ v, A v = ∑ y, f y • τ.ρ y⁻¹ v := fun v => by
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply]
  have hA : ∀ h, A ∘ₗ τ.ρ h = τ.ρ h ∘ₗ A := by
    intro h
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hAapp, hAapp, map_sum]
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e1 : f ((MulAut.conj h).toEquiv y) = f y := by
      simpa using hf y h
    rw [e1, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp [mul_assoc]
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom A, fun g => by
    ext x
    change A (τ.ρ g x) = τ.ρ g (A x)
    exact LinearMap.congr_fun (hA g) x⟩
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ F
  have hAv : ∀ v, A v = c • v := fun v => by
    have : F.hom.hom.hom v = c • v := by rw [← hc]; rfl
    exact this
  refine ⟨c, fun v => by rw [← hAv, hAapp], ?_⟩
  have hAc : A = c • LinearMap.id := LinearMap.ext fun v => by rw [hAv]; rfl
  have htr : LinearMap.trace ℂ τ A = c * Module.finrank ℂ τ := by
    rw [hAc, map_smul, LinearMap.trace_id, smul_eq_mul]
  rw [← htr]
  simp only [A, map_sum, map_smul, smul_eq_mul]
  rfl

end DiscreteGroups.sglob.DzType.Kon
