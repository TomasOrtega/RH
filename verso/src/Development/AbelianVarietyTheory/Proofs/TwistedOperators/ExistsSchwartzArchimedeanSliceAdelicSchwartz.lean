import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchSlice

/- English proof (translation)
Introduce `F _ _ κ _ Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, -, rfl⟩` from `hx`. Use `⟨g 0 • f, fun t => ?_⟩` and prove the remaining obligations.

Simplify using `only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, fun t => rfl⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨g₁, h₁⟩` from `hx`. Take `⟨g₂, h₂⟩` from `hy`. Conclude with `⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩`. Consider the case `smul c x _ hx`. Take `⟨g₁, h₁⟩` from `hx`.

Conclude with `⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩`.
-/
theorem exists_schwartz_slice : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    exact ⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    exact ⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩

end GlobalTheory.ArchSlice
