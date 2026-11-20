import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.PointEigen

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

The claim follows by propositional logic.
-/
theorem genAt_iff_splitOut (D : D7) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.nd.l i) (D.nd.Q i) v k ↔ (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.nd.l i) := by
    rw [D.nd.S_def]; rfl
  unfold SplitOut GenAt
  rw [hS]
  tauto

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ptSys_mem_eigSet : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i),
    ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  intro D M A i x
  refine ⟨fun v k h => ?_, ?_⟩
  · simp only [ptSys, if_neg h]
  · obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hw, k1, k2⟩ := (genAt_iff_splitOut D i v k).1 hg
    simp only [ptSys, if_pos hg]
    exact (A.ptV i P x).1 hP v k s ϖ hw hc hu k1 k2 y hy

end GlobalTheory.PointEigen
