import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

/- English proof (translation)
Take `⟨z, rfl⟩` from `ha`. Take `⟨n, rfl⟩` from `hb`. Establish `: z < n`. Establish `: (z : ℚ) < n` using `by linarith`. Conclude with `this` after adjusting the coercions.

Establish `: (z : ℚ) + 1 ≤ n` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_lt_int {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : z < n := by
    have : (z : ℚ) < n := by linarith
    exact_mod_cast this
  have : (z : ℚ) + 1 ≤ n := by exact_mod_cast this
  linarith

/- English proof (translation)
Take `⟨z, rfl⟩` from `ha`. Take `⟨n, rfl⟩` from `hb`. Establish `: n ≤ z`. Establish `: (n : ℚ) < z + 1` using `by linarith`. Establish `: n < z + 1` using `by exact_mod_cast this`.

Use linear arithmetic over natural numbers and integers. Establish `: (n : ℚ) ≤ z` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem int_lt_half {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : n ≤ z := by
    have : (n : ℚ) < z + 1 := by linarith
    have : n < z + 1 := by exact_mod_cast this
    omega
  have : (n : ℚ) ≤ z := by exact_mod_cast this
  linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
