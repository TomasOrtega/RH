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
Break down `k with n | n` into its components or cases. Rewrite using `[Int.ofNat_eq_natCast, zpow_natCast, v.map_pow]`. Rewrite using `[zpow_negSucc, v.map_inv, v.map_pow, Int.negSucc_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `h`. Use `T.ofRad_πExt ⟨1 / 2, by norm_num, by norm_num⟩` as an intermediate fact. Rewrite `this` using `[h]`. Establish `h1` using `T.πExt_mul_πInvExt ⟨1 / 2, by norm_num, by norm_num⟩`. Establish `h2` using `congrArg (T.ofRad ⟨1 / 2, by norm_num, by norm_num⟩) h1`.

Rewrite `h2` using `[map_mul, this, zero_mul, map_one]`. Conclude with `zero_ne_one h2`.
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
Rewrite using `[T.isUnit_iff]`. Conclude with `⟨πTilde_ne_zero, ⟨TeichFrob.πEdag T, rfl⟩⟩`.
-/
theorem isUnit_πTilde : IsUnit T.πTilde := by
  rw [T.isUnit_iff]
  exact ⟨πTilde_ne_zero, ⟨TeichFrob.πEdag T, rfl⟩⟩

variable (T) in

def πUnit : T.RobbaTildeˣ := (isUnit_πTilde (T := T)).unit

/- English proof (translation)
The claim follows from `IsUnit.unit_spec _`.
-/
theorem coe_πUnit : ((πUnit T : T.RobbaTildeˣ) : T.RobbaTilde) = T.πTilde := IsUnit.unit_spec _

/- English proof (translation)
Rewrite using `[T.tildeOrd_eq (b := TeichFrob.πEdag T) (by rw [coe_πUnit]; rfl)]`. Use `show T.ordB (algebraMap Γ T.B T.π) = 1`. Establish `h1 : algebraMap Γ T.B T.π = ((T.piB ^ (1 : ℤ) : T.Bˣ) : T.B) * algebraMap Γ T.B 1`. Rewrite using `[map_one, mul_one, zpow_one, piB_val]`. Rewrite using `[h1]`.

Conclude with `T.ordB_piB_zpow_mul _ (by rw [map_one]; exact one_ne_zero)`.
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
