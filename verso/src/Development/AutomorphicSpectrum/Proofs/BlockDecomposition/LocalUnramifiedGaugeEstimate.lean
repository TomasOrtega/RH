import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LUGauge

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `h1 : normalizedValuation F x ≤ normalizedValuation F 1`. Rewrite using `[map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `normalizedValuation_le_iff.1 h1`. Rewrite `h2` using `[map_one]`.

Conclude with `h2`.
-/
theorem mem_integers_of_ord_nonneg {x : F} (hx : x ≠ 0) (h : 0 ≤ ord x) : x ∈ 𝒪[F] := by
  have h1 : normalizedValuation F x ≤ normalizedValuation F 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact h2

/- English proof (translation)
Rewrite using `[modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]`.
-/
theorem modulus_coe (a : Fˣ) :
    ((modulus (a : F) : NNReal) : ℝ) = (residueCard F : ℝ) ^ (-ord (a : F)) := by
  rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]

end

end GlobalTheory.CompanionTheory.LUGauge
