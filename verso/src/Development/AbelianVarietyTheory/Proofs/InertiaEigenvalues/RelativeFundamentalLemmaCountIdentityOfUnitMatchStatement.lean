import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRelativeFundamentalLemmaCountIdentityOfUnitMatch.lean&line=328#L328)
-/
theorem _root_.GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → CountIdentity := by
  first | exact @GlobalTheory.CountId.countIdentity_of_unitMatch | exact GlobalTheory.CountId.countIdentity_of_unitMatch | (intros; apply GlobalTheory.CountId.countIdentity_of_unitMatch <;> assumption)
