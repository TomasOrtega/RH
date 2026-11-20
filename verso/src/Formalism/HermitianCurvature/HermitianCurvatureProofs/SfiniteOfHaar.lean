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
Take `⟨c, hc⟩` from `Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact`. Conclude with `⟨c, by rw [hc, ENNReal.smul_def]⟩`.
-/
theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts μ` using `⟨h.finite_compact⟩`. Use `infer_instance`.
-/
theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'`. Establish `hW` using `Bs.haarW`. Establish `hW'` using `Bs.haarW'`. Rewrite `hW` using `[hz]`. Rewrite `hW'` using `[hz']`.

Take `⟨a, ha⟩` from `haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW`. Take `⟨a', ha'⟩` from `haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'`. Take `⟨b, hb⟩` from `haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN`. Use `sfinite_of_haar Bs'.haarW` as an intermediate fact. Use `sfinite_of_haar Bs'.haarW'` as an intermediate fact.

Use `sfinite_of_haar Bs'.haarN` as an intermediate fact. Use `⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `only [B.JF, Pi.smul_apply]`. Rewrite using `[hz, hz', hπ, hπ', ha, ha', hb]`.

Unfold `besselJ`. Simplify using `only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]`. Rewrite using `[integral_smul_measure, Complex.coe_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
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
The claim follows from `PTieJ.jfScale`.
-/
theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
