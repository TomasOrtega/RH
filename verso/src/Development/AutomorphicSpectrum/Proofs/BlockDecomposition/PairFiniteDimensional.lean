import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F h`. Take `⟨φ₁, -, φ₂, -, rfl⟩` from `h`. Use `⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Use `⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using `[mul_comm]`. Use `⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Consider the case `zero`. Use `⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩, fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Consider the case `add F G _ _ hF hG`. Take `⟨A, B, hA, hB, h₁, h₂⟩` from `hF`. Take `⟨A', B', hA', hB', h₁', h₂'⟩` from `hG`. Use `⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations.

Take `⟨φ, hφ, e⟩` from `h₁ m₂`. Take `⟨φ', hφ', e'⟩` from `h₁' m₂`. Use `⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[e, e']`.

Take `⟨φ, hφ, e⟩` from `h₂ m₁`. Take `⟨φ', hφ', e'⟩` from `h₂' m₁`. Use `⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[e, e']`.

Consider the case `smul c F _ hF`. Take `⟨A, B, hA, hB, h₁, h₂⟩` from `hF`. Use `⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, e⟩` from `h₁ m₂`. Use `⟨c • φ, A.smul_mem c hφ, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using `[e]`. Take `⟨φ, hφ, e⟩` from `h₂ m₁`. Use `⟨c • φ, B.smul_mem c hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[e]`.
-/
theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

/- English proof (translation)
Introduce `E _ _ _ a b ι _ U₁ U₂ f hf`. Use `choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)`. Establish `hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a))` using `Submodule.finiteDimensional_iSup A`. Establish `hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b))` using `Submodule.finiteDimensional_iSup B`. Prove the components needed by the constructor for the conclusion.

Use `Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `φ ⟨i, m₂, e⟩`. Take `⟨ψ, hψ, e'⟩` from `h₁ i m₂`. Establish `: φ = ψ` using `Subtype.ext (e.trans e'.symm)`. Rewrite using `[this]`.

Conclude with `Submodule.mem_iSup_of_mem i hψ`. Use `Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `φ ⟨i, m₁, e⟩`. Take `⟨ψ, hψ, e'⟩` from `h₂ i m₁`. Establish `: φ = ψ` using `Subtype.ext (e.trans e'.symm)`.

Rewrite using `[this]`. Conclude with `Submodule.mem_iSup_of_mem i hψ`.
-/
theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
