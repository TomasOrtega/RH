import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWittFrameUnipotentRadicalClosedFundDomainMassOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  first | exact @GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | exact GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | (intros; apply GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one <;> assumption)
