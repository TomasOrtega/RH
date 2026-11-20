import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.LabelCompat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem labCompat : ∀ (D : D7) (i : D.nd.Loc), LabCompat D.nd D.naut i := by
  intro D i σ Sig hσ
  have key : ∀ k, D.nd.lab k σ = fun v =>
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
    intro k
    funext v
    rw [D.naut.lab_loc i k σ v, hσ.2.2 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [key k]

end GlobalTheory.LabelCompat
