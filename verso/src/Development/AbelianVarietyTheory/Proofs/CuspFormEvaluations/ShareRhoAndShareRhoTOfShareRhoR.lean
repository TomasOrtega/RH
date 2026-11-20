import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem shareRho_and_shareRhoT_of_shareRhoR :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
      (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) (Gc : ℝ), ShareRhoR G S T d → G.TiedZ S T Gc →
      (∀ la, InContainZ G la S T) →
      ShareRho (D := D) (j := j) T G.rz d ∧ ShareRhoT (D := D) (j := j) T G.rz G.rq d := by
  intro D B P j X ka wL wF G S T d Gc hR hT hZ
  obtain ⟨la0⟩ := Formalism.MainNotions.Gaps.EtaleWeightGaps.exists_prime B.KO
  have hr : Module.finrank (Kp X la0 G.N) ↥(Submodule.span (Kp X la0 G.N) (zAll G la0 S T)) = G.rz :=
    rz_eq_finrank G S T Gc la0 hT (hZ la0)
  have h := hR la0
  rw [hr] at h
  refine ⟨h, ?_⟩
  unfold ShareRhoT
  have h0 : (0 : ℝ) ≤ (G.rq : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalTheory
