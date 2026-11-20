import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIndexStandardInfSkewThetaLatticeEqAbsNormPow.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  first | exact @GlobalTheory.SkewIndex.index_inter_skew | exact GlobalTheory.SkewIndex.index_inter_skew | (intros; apply GlobalTheory.SkewIndex.index_inter_skew <;> assumption)
