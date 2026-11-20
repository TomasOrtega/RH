import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceIntegralOfPreservedLattice
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatTrace.trace_isIntegral_of_preserves_lattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceIntegralOfPreservedLattice.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.trace_integral_of_preserved_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, A *ᵥ x ∈ Λ) → IsIntegral ℤ A.trace := by
  first | exact @GlobalTheory.LatTrace.trace_isIntegral_of_preserves_lattice | exact GlobalTheory.LatTrace.trace_isIntegral_of_preserves_lattice | (intros; apply GlobalTheory.LatTrace.trace_isIntegral_of_preserves_lattice <;> assumption)
