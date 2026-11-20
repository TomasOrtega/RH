import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemStabilizerSpanIffUnitriangularIntegral
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemStabilizerSpanIffUnitriangularIntegral.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  first | exact @GlobalTheory.HL.unistab_iff | exact GlobalTheory.HL.unistab_iff | (intros; apply GlobalTheory.HL.unistab_iff <;> assumption)
