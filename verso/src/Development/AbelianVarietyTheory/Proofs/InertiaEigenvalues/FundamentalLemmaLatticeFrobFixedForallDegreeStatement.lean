import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFundamentalLemmaLatticeFrobFixedForallDegree.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree : ∀ r : ℕ, FLAt r := by
  first | exact @GlobalTheory.PMon.flAt_all | exact GlobalTheory.PMon.flAt_all | (intros; apply GlobalTheory.PMon.flAt_all <;> assumption)
