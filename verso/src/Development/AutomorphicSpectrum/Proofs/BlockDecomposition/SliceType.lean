import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f h`. Take `⟨w₁, h₁, w₂, -, rfl⟩` from `h`. Establish `: (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁`. Use function extensionality and compare the values at `k`.

Simplify using `[mul_comm]`. Simplify `W₁.smul_mem _ h₁` using `[this]`. Consider the case `zero => exact W₁.zero_mem`. Consider the case `add f g _ _ hf hg => exact W₁.add_mem hf hg`. Consider the case `smul c f _ hf => exact W₁.smul_mem c hf`.
-/
theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f h`. Take `⟨w₁, -, w₂, h₂, rfl⟩` from `h`. Establish `: (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂`. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Simplify `W₂.smul_mem _ h₂` using `[this]`. Consider the case `zero => exact W₂.zero_mem`. Consider the case `add f g _ _ hf hg => exact W₂.add_mem hf hg`. Consider the case `smul c f _ hf => exact W₂.smul_mem c hf`.
-/
theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

/- English proof (translation)
Introduce `E _ _ _ a b K₁ K₂ W₁ W₂ F hF`. Take `⟨hl, hk⟩` from `hF`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `φ m₂ hφ`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu g`. Use `hl u hu 1 K₂.one_mem (g, m₂)` as an intermediate fact. Simplify `this` using `[hφ, Prod.mk_mul_mk]`. Introduce `g`. Use `restrict_left W₁ W₂ _ (hk (g, m₂))` as an intermediate fact.

Simplify `this` using `[hφ, Prod.mk_mul_mk]`. Introduce and unpack `φ m₁ hφ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `u hu g`. Use `hl 1 K₁.one_mem u hu (m₁, g)` as an intermediate fact.

Simplify `this` using `[hφ, Prod.mk_mul_mk]`. Introduce `g`. Use `restrict_right W₁ W₂ _ (hk (m₁, g))` as an intermediate fact. Simplify `this` using `[hφ, Prod.mk_mul_mk]`.
-/
theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
