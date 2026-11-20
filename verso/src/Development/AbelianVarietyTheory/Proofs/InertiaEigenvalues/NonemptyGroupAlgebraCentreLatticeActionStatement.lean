import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CenOAct.cenO_nonempty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNonemptyGroupAlgebraCentreLatticeAction.lean&line=279#L279)
-/
theorem _root_.GlobalTheory.T.nonempty_groupAlgebraCentreLatticeAction : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → ZLStable D → CenInt D → OnMtPreservesTypeV D → Nonempty (CenO D) := by
  first | exact @GlobalTheory.CenOAct.cenO_nonempty | exact GlobalTheory.CenOAct.cenO_nonempty | (intros; apply GlobalTheory.CenOAct.cenO_nonempty <;> assumption)
