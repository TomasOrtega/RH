import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `V W _ _ _ _ H H' Φ hΦ hH' Λ₁ Λ₂ α F hα hF hn z`. Use `set f : V →+ W := (Φ : V →ₗ[ℂ] W).toAddMonoidHom with hf`. Establish `hfs : Function.Surjective f` using `Φ.surjective`. Establish `hfx : ∀ v, f v = Φ v` using `fun v => rfl`. Establish `hH : IsHerm H`.

Introduce `x y`. Rewrite using `[hΦ, hΦ, hH']`. Establish `hα' : IsSemiChar H (Λ₂.comap f) (fun v => α (Φ v))`. Use `⟨fun x hx => hα.1 (Φ x) hx, fun x hx y hy => ?_⟩` and prove the remaining obligations. Use `hα.2 (Φ x) hx (Φ y) hy` as an intermediate fact.

Simplify using `only [map_add, altE] at this ⊢`. Rewrite using `[this, hΦ]`. Establish `hopU : ∀ x (G : W → ℂ) v, opU H x (fun w => G (Φ w)) v = opU H' (Φ x) G (Φ v)`. Introduce `x G v`. Simplify using `only [opU, map_add, hΦ]`.

Establish `hF' : (fun v => F (Φ v)) ∈ fixedBy H (fun v => α (Φ v)) (Λ₁.comap f)`. Introduce `x hx v`. Rewrite using `[hopU]`. Conclude with `hF (Φ x) hx (Φ v)`. Establish `hidx : relIdx (Λ₁.comap f) (Λ₂.comap f) = relIdx Λ₁ Λ₂`.

Unfold `relIdx`. Rewrite using `[AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hfs]`. Take `⟨S, hS⟩` from `(cosetRepsExist W Λ₁ Λ₂ hn).1`. Establish `hS' : IsReps (Λ₁.comap f) (Λ₂.comap f) (S.image Φ.symm)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hw`. Use `show f (Φ.symm x) ∈ Λ₂`. Rewrite using `[hfx, LinearEquiv.apply_symm_apply]`. Conclude with `hS.1 x hx`.

Introduce `w hw w' hw' hd`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hw`. Take `⟨x', hx', rfl⟩` from `Finset.mem_image.1 hw'`. Establish `hd' : x - x' ∈ Λ₁`. Establish `: f (Φ.symm x - Φ.symm x') ∈ Λ₁` using `hd`.

Rewrite `this` using `[hfx, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Rewrite using `[hS.2.1 x hx x' hx' hd']`. Introduce `y hy`. Take `⟨x, hx, hd⟩` from `hS.2.2 (Φ y) hy`. Use `⟨Φ.symm x, Finset.mem_image.2 ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show f (y - Φ.symm x) ∈ Λ₁`. Rewrite using `[hfx, map_sub, LinearEquiv.apply_symm_apply]`. Conclude with `hd`. Rewrite using `[InterReps_of semicharacterHom V H hH _ _ _ hα' _ hF' _ hS' z, InterReps_of semicharacterHom W H' hH' _ _ _ hα _ hF _ hS (Φ z), hidx]`. Use `congr 1`.

Unfold `sumU`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => Φ.symm.injective hab)]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hopU, LinearEquiv.apply_symm_apply]`. Simplify using `only [LinearEquiv.apply_symm_apply]`.
-/
theorem inter_comap_isom : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (Φ : V ≃ₗ[ℂ] W), (∀ x y, H x y = H' (Φ x) (Φ y)) → IsHerm H' → ∀ (Λ₁ Λ₂ : AddSubgroup W) (α : W → ℂ) (F : W → ℂ), IsSemiChar H' Λ₂ α → F ∈ fixedBy H' α Λ₁ → relIdx Λ₁ Λ₂ ≠ 0 → ∀ z, inter H (fun v => α (Φ v)) (Λ₁.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (fun v => F (Φ v)) z = inter H' α Λ₁ Λ₂ F (Φ z) := by
  intro V W _ _ _ _ H H' Φ hΦ hH' Λ₁ Λ₂ α F hα hF hn z
  set f : V →+ W := (Φ : V →ₗ[ℂ] W).toAddMonoidHom with hf
  have hfs : Function.Surjective f := Φ.surjective
  have hfx : ∀ v, f v = Φ v := fun v => rfl
  have hH : IsHerm H := by
    intro x y; rw [hΦ, hΦ, hH']
  have hα' : IsSemiChar H (Λ₂.comap f) (fun v => α (Φ v)) := by
    refine ⟨fun x hx => hα.1 (Φ x) hx, fun x hx y hy => ?_⟩
    have := hα.2 (Φ x) hx (Φ y) hy
    simp only [map_add, altE] at this ⊢
    rw [this, hΦ]
  have hopU : ∀ x (G : W → ℂ) v, opU H x (fun w => G (Φ w)) v = opU H' (Φ x) G (Φ v) := by
    intro x G v
    simp only [opU, map_add, hΦ]
  have hF' : (fun v => F (Φ v)) ∈ fixedBy H (fun v => α (Φ v)) (Λ₁.comap f) := by
    intro x hx v
    rw [hopU]
    exact hF (Φ x) hx (Φ v)
  have hidx : relIdx (Λ₁.comap f) (Λ₂.comap f) = relIdx Λ₁ Λ₂ := by
    unfold relIdx
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hfs]
  obtain ⟨S, hS⟩ := (cosetRepsExist W Λ₁ Λ₂ hn).1
  have hS' : IsReps (Λ₁.comap f) (Λ₂.comap f) (S.image Φ.symm) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
      show f (Φ.symm x) ∈ Λ₂
      rw [hfx, LinearEquiv.apply_symm_apply]; exact hS.1 x hx
    · intro w hw w' hw' hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hw'
      have hd' : x - x' ∈ Λ₁ := by
        have : f (Φ.symm x - Φ.symm x') ∈ Λ₁ := hd
        rwa [hfx, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      rw [hS.2.1 x hx x' hx' hd']
    · intro y hy
      obtain ⟨x, hx, hd⟩ := hS.2.2 (Φ y) hy
      refine ⟨Φ.symm x, Finset.mem_image.2 ⟨x, hx, rfl⟩, ?_⟩
      show f (y - Φ.symm x) ∈ Λ₁
      rw [hfx, map_sub, LinearEquiv.apply_symm_apply]; exact hd
  rw [InterReps_of semicharacterHom V H hH _ _ _ hα' _ hF' _ hS' z,
    InterReps_of semicharacterHom W H' hH' _ _ _ hα _ hF _ hS (Φ z), hidx]
  congr 1
  unfold sumU
  rw [Finset.sum_image (fun a _ b _ hab => Φ.symm.injective hab)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hopU, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.apply_symm_apply]

end GlobalTheory
