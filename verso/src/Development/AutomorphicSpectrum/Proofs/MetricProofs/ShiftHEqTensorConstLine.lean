import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem shiftH_eq_tensor_constLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (A : HermLine ι) (t : ℝ) :
    shiftH A t = A.tensor (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (-t)) := by
  unfold shiftH ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor ReciprocityTheory.ChartRestriction.G.AI.I2.constLine
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight
  congr 1
  · exact (add_zero _).symm
  · funext z
    show Real.exp t * A.h z = A.h z * Real.exp (-(-t))
    rw [neg_neg, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem selfInt_shiftH : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (t : ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar P (D + 1) →
    IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => shiftH A t) =
      II K ι P (D + 1) (fun _ => A) + ((D : ℝ) + 1) * t * geomDeg P A D := by
  intro K _ ι _ P D A t II hII hP hA
  have h := GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof K ι P D A (-t) II hII hP hA
  rw [shiftH_eq_tensor_constLine, h]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Small
