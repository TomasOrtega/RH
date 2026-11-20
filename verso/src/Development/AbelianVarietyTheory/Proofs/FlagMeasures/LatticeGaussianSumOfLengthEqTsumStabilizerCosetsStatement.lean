import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLatticeGaussianSumOfLengthEqTsumStabilizerCosets.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  first | exact @GlobalTheory.StabCosets.gaussSum_cosets | exact GlobalTheory.StabCosets.gaussSum_cosets | (intros; apply GlobalTheory.StabCosets.gaussSum_cosets <;> assumption)
