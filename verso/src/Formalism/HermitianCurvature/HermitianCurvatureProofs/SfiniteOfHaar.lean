import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieJ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jfScale : Formalism.FourierDecayAlt.P.PTie.JFScale := by
  intro k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'
  have hW := Bs.haarW
  have hW' := Bs.haarW'
  rw [hz] at hW
  rw [hz'] at hW'
  obtain ⟨a, ha⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW
  obtain ⟨a', ha'⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'
  obtain ⟨b, hb⟩ := haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN
  have := sfinite_of_haar Bs'.haarW
  have := sfinite_of_haar Bs'.haarW'
  have := sfinite_of_haar Bs'.haarN
  refine ⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩
  funext g
  simp only [B.JF, Pi.smul_apply]
  rw [hz, hz', hπ, hπ', ha, ha', hb]
  unfold besselJ
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [integral_smul_measure, Complex.coe_smul]
  congr 2
  ring

end Formalism.FourierDecayAlt.P.PTieJ

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
