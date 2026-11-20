import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairSl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F h`. Take `⟨φ₁, h₁, φ₂, h₂, rfl⟩` from `h`. Use `⟨fun m₂ => ⟨φ₂.1 m₂ • φ₁, U₁.smul_mem _ h₁, ?_⟩, fun m₁ => ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[mul_comm]`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `zero`. Use `⟨fun m₂ => ⟨0, U₁.zero_mem, ?_⟩, fun m₁ => ⟨0, U₂.zero_mem, ?_⟩⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Consider the case `add F G _ _ h₁ h₂`.

Use `⟨fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, e⟩` from `h₁.1 m₂`. Take `⟨ψ, hψ, e'⟩` from `h₂.1 m₂`. Use `⟨φ + ψ, U₁.add_mem hφ hψ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Establish `i` using `congrFun e x`. Establish `i'` using `congrFun e' x`. Simplify the hypotheses and the goal together. Take `⟨φ, hφ, e⟩` from `h₁.2 m₁`. Take `⟨ψ, hψ, e'⟩` from `h₂.2 m₁`.

Use `⟨φ + ψ, U₂.add_mem hφ hψ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `i` using `congrFun e x`. Establish `i'` using `congrFun e' x`. Simplify the hypotheses and the goal together.

Consider the case `smul r F _ h`. Use `⟨fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, e⟩` from `h.1 m₂`. Use `⟨r • φ, U₁.smul_mem r hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Establish `i` using `congrFun e x`. Simplify the hypotheses and the goal together. Take `⟨φ, hφ, e⟩` from `h.2 m₁`. Use `⟨r • φ, U₂.smul_mem r hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Establish `i` using `congrFun e x`. Simplify the hypotheses and the goal together.
-/
theorem exists_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    (∀ m₂, ∃ φ ∈ U₁, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁, ∃ φ ∈ U₂, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine ⟨fun m₂ => ⟨φ₂.1 m₂ • φ₁, U₁.smul_mem _ h₁, ?_⟩, fun m₁ => ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, ?_⟩⟩
    · funext x
      simp [mul_comm]
    · funext x
      simp
  | zero =>
    refine ⟨fun m₂ => ⟨0, U₁.zero_mem, ?_⟩, fun m₁ => ⟨0, U₂.zero_mem, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ h₁ h₂ =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁.1 m₂
      obtain ⟨ψ, hψ, e'⟩ := h₂.1 m₂
      refine ⟨φ + ψ, U₁.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h₁.2 m₁
      obtain ⟨ψ, hψ, e'⟩ := h₂.2 m₁
      refine ⟨φ + ψ, U₂.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
  | smul r F _ h =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h.1 m₂
      refine ⟨r • φ, U₁.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h.2 m₁
      refine ⟨r • φ, U₂.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all

end GlobalTheory.CompanionTheory.EGlue.PairSl

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Introduce `E _ _ _ a b U₁ U₂ F hF`. Take `⟨h₁, h₂⟩` from `PairSl.exists_slices U₁ U₂ F hF`. Use `⟨fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, e⟩` from `h₁ m₂`. Establish `hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂)` using `⟨φ, e⟩`.

Establish `hs : sl₁ F m₂ = hex.choose` using `by simp only [sl₁, dif_pos hex]`. Establish `hc : hex.choose = φ` using `Subtype.ext (hex.choose_spec.trans e.symm)`. Rewrite using `[hs, hc]`. Conclude with `⟨hφ, e⟩`. Take `⟨φ, hφ, e⟩` from `h₂ m₁`.

Establish `hex : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x)` using `⟨φ, e⟩`. Establish `hs : sl₂ F m₁ = hex.choose` using `by simp only [sl₂, dif_pos hex]`. Establish `hc : hex.choose = φ` using `Subtype.ext (hex.choose_spec.trans e.symm)`. Rewrite using `[hs, hc]`. Conclude with `⟨hφ, e⟩`.
-/
theorem pairSlices : PairSlices := by
  intro E _ _ _ a b U₁ U₂ F hF
  obtain ⟨h₁, h₂⟩ := PairSl.exists_slices U₁ U₂ F hF
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h₁ m₂
    have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, e⟩
    have hs : sl₁ F m₂ = hex.choose := by simp only [sl₁, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩
  · obtain ⟨φ, hφ, e⟩ := h₂ m₁
    have hex : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) := ⟨φ, e⟩
    have hs : sl₂ F m₁ = hex.choose := by simp only [sl₂, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩

end GlobalTheory.CompanionTheory.EGlue

end
