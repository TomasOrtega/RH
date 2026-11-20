import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfIsRootDistinguishedWittPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RootLt.norm_lt_one_of_isRoot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormLtOneOfIsRootDistinguishedWittPolynomial.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.norm_lt_one_of_isRoot_distinguished_witt_polynomial : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  first | exact @GlobalTheory.RootLt.norm_lt_one_of_isRoot | exact GlobalTheory.RootLt.norm_lt_one_of_isRoot | (intros; apply GlobalTheory.RootLt.norm_lt_one_of_isRoot <;> assumption)
