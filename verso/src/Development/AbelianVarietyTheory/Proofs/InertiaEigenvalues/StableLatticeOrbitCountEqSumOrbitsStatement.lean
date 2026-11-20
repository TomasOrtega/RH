import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticeOrbitCountEqSumOrbits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.countGL_eq_sum_orbits` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FStableLatticeOrbitCountEqSumOrbits.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A), countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g), ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  first | exact @GlobalTheory.UnitLemma.countGL_eq_sum_orbits | exact GlobalTheory.UnitLemma.countGL_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.countGL_eq_sum_orbits <;> assumption)
