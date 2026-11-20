import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaTrivialSB
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Module PhiModule

namespace PhiModule.UnitOrd

variable {R : Type*} [CommRing R] {φ : R →+* R} (v : UnitOrd R φ)

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_zpow (a : Rˣ) (k : ℤ) : v.ord (a ^ k) = k * v.ord a := by
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, v.map_pow]
  · rw [zpow_negSucc, v.map_inv, v.map_pow, Int.negSucc_eq]; push_cast; ring

end PhiModule.UnitOrd

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}
  [CompleteSpace L]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem πTilde_ne_zero : T.πTilde ≠ 0 := by
  intro h
  have := T.ofRad_πExt ⟨1 / 2, by norm_num, by norm_num⟩
  rw [h] at this
  have h1 := T.πExt_mul_πInvExt ⟨1 / 2, by norm_num, by norm_num⟩
  have h2 := congrArg (T.ofRad ⟨1 / 2, by norm_num, by norm_num⟩) h1
  rw [map_mul, this, zero_mul, map_one] at h2
  exact zero_ne_one h2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem isUnit_πTilde : IsUnit T.πTilde := by
  rw [T.isUnit_iff]
  exact ⟨πTilde_ne_zero, ⟨TeichFrob.πEdag T, rfl⟩⟩

variable (T) in

def πUnit : T.RobbaTildeˣ := (isUnit_πTilde (T := T)).unit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coe_πUnit : ((πUnit T : T.RobbaTildeˣ) : T.RobbaTilde) = T.πTilde := IsUnit.unit_spec _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tildeOrd_πUnit : T.tildeOrd (πUnit T) = 1 := by
  rw [T.tildeOrd_eq (b := TeichFrob.πEdag T) (by rw [coe_πUnit]; rfl)]
  show T.ordB (algebraMap Γ T.B T.π) = 1
  have h1 : algebraMap Γ T.B T.π = ((T.piB ^ (1 : ℤ) : T.Bˣ) : T.B) * algebraMap Γ T.B 1 := by
    rw [map_one, mul_one, zpow_one, piB_val]
  rw [h1]
  exact T.ordB_piB_zpow_mul _ (by rw [map_one]; exact one_ne_zero)

namespace TeichFrob

variable (F : T.TeichFrob)

variable [IsAlgClosed L]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
