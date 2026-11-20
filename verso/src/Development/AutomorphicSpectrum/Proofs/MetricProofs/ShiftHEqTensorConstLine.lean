import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

/- English proof (translation)
Unfold `shiftH ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor ReciprocityTheory.ChartRestriction.G.AI.I2.constLine ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight`. Use `congr 1`. Conclude with `(add_zero _).symm`. Use function extensionality and compare the values at `z show Real.exp t * A.h z = A.h z * Real.exp (-(-t))`. Rewrite using `[neg_neg, mul_comm]`.
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
Introduce `K _ ι _ P D A t II hII hP hA`. Establish `h` using `GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof K ι P D A (-t) II hII hP hA`. Rewrite using `[shiftH_eq_tensor_constLine, h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
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
