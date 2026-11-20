import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitChar

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ χ hχ hψ`. Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `htr : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hc : Continuous fun a : k => psiE ψ (p.sec a)` using `hψ.1.1.comp (htr.comp p.cont_sec)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h' : Continuous fun a : k => ((χ a : Circle) : ℂ)`. Establish `he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a)` using `funext hχ`. Rewrite using `[he]`. Conclude with `hc`. Use `first`.

Consider the case `exact Circle.isEmbedding_coe.continuous_iff.2 h'`. Consider the case `exact continuous_induced_rng.2 h'`. Introduce `h1`. Take `⟨a, ha⟩` from `GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ`. Apply `ha` to reduce the goal to its premises.

Rewrite using `[← hχ a, h1]`. Simplify using the standard rewrite rules.
-/
theorem cont_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) →
    Continuous χ ∧ χ ≠ 1 := by
  intro D k _ _ _ _ p ψ χ hχ hψ
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  refine ⟨?_, ?_⟩
  · have h' : Continuous fun a : k => ((χ a : Circle) : ℂ) := by
      have he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hχ
      rw [he]; exact hc
    first
      | exact Circle.isEmbedding_coe.continuous_iff.2 h'
      | exact continuous_induced_rng.2 h'
  · intro h1
    obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
    apply ha
    rw [← hχ a, h1]
    simp

end GlobalTheory.FinPl.SplitChar
