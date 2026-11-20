import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LzExist.exists_lz_serEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFiniteGroupDataSeriesIdempotentsLabelSums.lean&line=224#L224)
-/
theorem _root_.GlobalTheory.T.exists_finiteGroupData_seriesIdempotentsLabelSums : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  first | exact @GlobalTheory.LzExist.exists_lz_serEq | exact GlobalTheory.LzExist.exists_lz_serEq | (intros; apply GlobalTheory.LzExist.exists_lz_serEq <;> assumption)
