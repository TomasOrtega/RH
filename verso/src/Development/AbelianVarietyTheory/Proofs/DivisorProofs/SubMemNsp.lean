import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Nsp (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {Z | ∃ g : GL A k, ∃ Ψ' ∈ SB (Matrix A D k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}

variable {k}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem Nsp_le_SB (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, Ψ', hΨ', rfl⟩
  exact Submodule.sub_mem _ (GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 hΨ') hΨ'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sub_mem_Nsp {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

end GlobalTheory.RankStrata
