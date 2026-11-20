import Mathlib

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ ν _ h k hk`. Establish `e : h * (k * h) = k` using `by rw [hk, mul_inv_cancel_left]`. Establish `e2` using `congrArg Measure.modularCharacterFun e`. Rewrite `e2` using `[Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul]`. Establish `hk0 : (0 : ℝ) < Measure.modularCharacterFun k` using `Measure.modularCharacterFun_pos k`.

Establish `hh0 : (0 : ℝ) < Measure.modularCharacterFun h` using `Measure.modularCharacterFun_pos h`. Establish `e3 : (Measure.modularCharacterFun h : ℝ) * ((Measure.modularCharacterFun k : ℝ) * Measure.modularCharacterFun h) = Measure.modularCharacterFun k` using `by exact_mod_cast e2`. Establish `e4 : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h = 1`. Apply `mul_left_cancel₀ hk0.ne'` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e5 : (Measure.modularCharacterFun h : ℝ) = 1` using `by nlinarith`. Establish `e6 : Measure.modularCharacterFun h = 1` using `by exact_mod_cast e5`. Establish `hm : ν.map (fun g => g * h) = Measure.modularCharacterFun h • ν`. Rewrite using `[Measure.modularCharacterFun_eq_haarScalarFactor ν h]`. Conclude with `Measure.isMulLeftInvariant_eq_smul _ ν`.

Rewrite using `[hm, e6, one_smul]`.
-/
theorem haar_map_mul_right_of_conj_inv :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) := by
  intro G _ _ _ _ _ _ _ _ ν _ h k hk
  have e : h * (k * h) = k := by rw [hk, mul_inv_cancel_left]
  have e2 := congrArg Measure.modularCharacterFun e
  rw [Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul] at e2
  have hk0 : (0 : ℝ) < Measure.modularCharacterFun k := Measure.modularCharacterFun_pos k
  have hh0 : (0 : ℝ) < Measure.modularCharacterFun h := Measure.modularCharacterFun_pos h
  have e3 : (Measure.modularCharacterFun h : ℝ) *
      ((Measure.modularCharacterFun k : ℝ) * Measure.modularCharacterFun h) =
      Measure.modularCharacterFun k := by exact_mod_cast e2
  have e4 : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h = 1 := by
    apply mul_left_cancel₀ hk0.ne'
    linarith
  have e5 : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  have e6 : Measure.modularCharacterFun h = 1 := by exact_mod_cast e5
  have hm : ν.map (fun g => g * h) = Measure.modularCharacterFun h • ν := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν h]
    exact Measure.isMulLeftInvariant_eq_smul _ ν
  rw [hm, e6, one_smul]

end GlobalTheory
