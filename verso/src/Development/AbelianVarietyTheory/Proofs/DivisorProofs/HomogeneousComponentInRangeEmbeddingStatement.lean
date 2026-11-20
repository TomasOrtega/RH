import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomogeneousComponentInRangeEmbedding.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.homogeneous_component_in_range_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ), homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  first | exact @GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | exact GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem | (intros; apply GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem <;> assumption)
