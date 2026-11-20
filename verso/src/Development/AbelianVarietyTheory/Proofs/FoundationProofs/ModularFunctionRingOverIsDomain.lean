import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `E`. Use `haveI : Nontrivial (GlobalTheory.FN.ring E) := by`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h`. Simplify using `at h1`.

Use `haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by`. Use `⟨fun {a b} hab => ?_⟩` and prove the remaining obligations. Establish `hmem` using `(GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1`. Establish `ha` using `GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)`. Establish `hb` using `GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)`.

Establish `h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0`. Introduce `τ`. Use `congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab` as an intermediate fact. Simplify using `using this`. Break down `GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h` into its components or cases.

Use `left`. Conclude with `Subtype.ext h`. Use `right`. Conclude with `Subtype.ext h`. Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem ring_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  intro E
  haveI : Nontrivial (GlobalTheory.FN.ring E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h
    simp at h1
  haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1
    have ha := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)
    have hb := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)
    have h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0 := by
      intro τ
      have := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab
      simpa using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FN
