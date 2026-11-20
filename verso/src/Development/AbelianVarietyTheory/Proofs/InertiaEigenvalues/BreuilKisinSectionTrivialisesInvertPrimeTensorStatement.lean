import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinSectionTrivialisesInvertPrimeTensor.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  first | exact @GlobalTheory.BK.xi_trivialises_invL_S | exact GlobalTheory.BK.xi_trivialises_invL_S | (intros; apply GlobalTheory.BK.xi_trivialises_invL_S <;> assumption)
