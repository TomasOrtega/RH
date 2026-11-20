import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactUnitaryOfSplitPlaceLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftInt.mem_Umax_of_isLift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemMaximalCompactUnitaryOfSplitPlaceLift.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.mem_maximalCompactUnitary_of_splitPlaceLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  first | exact @GlobalTheory.LiftInt.mem_Umax_of_isLift | exact GlobalTheory.LiftInt.mem_Umax_of_isLift | (intros; apply GlobalTheory.LiftInt.mem_Umax_of_isLift <;> assumption)
