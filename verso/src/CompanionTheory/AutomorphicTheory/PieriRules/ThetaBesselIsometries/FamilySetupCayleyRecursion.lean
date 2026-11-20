import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyMomentStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Moment

/- English proof (translation)
Establish `h1 : (∑ i, ((Pi.single s (1 : ℤ) : Fin n → ℤ) i).natAbs) = 1`. Rewrite using `[Finset.sum_eq_single s]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Simplify using the standard rewrite rules. Unfold `n1`. Rewrite using `[← h1, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Conclude with `Int.natAbs_sub_le _ _`.
-/
theorem n1_sub_single_one_le_add_one {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : (∑ i, ((Pi.single s (1 : ℤ) : Fin n → ℤ) i).natAbs) = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Int.natAbs_sub_le _ _

/- English proof (translation)
Introduce `H k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q`. Establish `hT : 0 < Formalism.QuantumDeterminants.Tz k r z` using `hS.2.2.1.2.1`. Establish `hC : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)))`. Establish `h6 : 0 ≤ (6 * bv) ^ (2 * (2 * r + 2))` using `by rw [pow_mul]; positivity`. Check the signs of the components of the expression.

Proceed by induction on `q with`. Consider the case `zero`. Introduce `ν hν j _ w _`. Apply the tactic sequence `have := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν (by omega)).1 w w.2`. Simplify using `using this`.

Consider the case `succ q ih`. Introduce `ν hν j hj w hw`. Use `GlobalTheory.T.family_setup_cayley_moment H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν (by omega) j q _ (by omega) (pow_nonneg hC q) (fun s y hy => ih (ν - Pi.single s 1) (by have := n1_sub_single_one_le_add_one ν s; omega) (j + 2) (by omega) y hy) w hw` as an intermediate fact. Rewrite using `[pow_succ' _ q]`. Conclude with `this`.
-/
theorem moment_first_length : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  intro H k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hS.2.2.1.2.1
  have hC : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have h6 : 0 ≤ (6 * bv) ^ (2 * (2 * r + 2)) := by rw [pow_mul]; positivity
    positivity
  induction q with
  | zero =>
    intro ν hν j _ w _
    have := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν (by omega)).1 w w.2
    simpa using this
  | succ q ih =>
    intro ν hν j hj w hw
    have := GlobalTheory.T.family_setup_cayley_moment H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν (by omega) j q _
      (by omega) (pow_nonneg hC q)
      (fun s y hy => ih (ν - Pi.single s 1) (by have := n1_sub_single_one_le_add_one ν s; omega) (j + 2) (by omega) y hy) w hw
    rw [pow_succ' _ q]
    exact this

end GlobalTheory.Moment
