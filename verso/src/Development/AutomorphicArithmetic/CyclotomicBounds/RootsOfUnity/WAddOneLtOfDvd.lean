import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuRecord

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Establish `hw : Units.torsionOrder H.E ∣ H.QS` using `w_dvd_QS H`. Establish `hwle : Units.torsionOrder H.E ≤ H.QS` using `Nat.le_of_dvd H.QS_pos hw`. Establish `hq` using `H.q_prime.two_le`. Establish `hd` using `H.d_prime.two_le`. Establish `hle : H.QS * H.q * H.d ≤ p - 1` using `Nat.le_of_dvd (by omega) h`.

Establish `h4 : H.QS * 4 ≤ H.QS * H.q * H.d`. Rewrite using `[mul_assoc]`. Conclude with `Nat.mul_le_mul_left _ (by nlinarith)`. Establish `hQ` using `H.QS_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem w_add_one_lt_of_dvd {p : ℕ} (hp : 1 < p) (h : H.QS * H.q * H.d ∣ p - 1) : Units.torsionOrder H.E + 1 < p := by
  have hw : Units.torsionOrder H.E ∣ H.QS := w_dvd_QS H
  have hwle : Units.torsionOrder H.E ≤ H.QS := Nat.le_of_dvd H.QS_pos hw
  have hq := H.q_prime.two_le
  have hd := H.d_prime.two_le
  have hle : H.QS * H.q * H.d ≤ p - 1 := Nat.le_of_dvd (by omega) h
  have h4 : H.QS * 4 ≤ H.QS * H.q * H.d := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have hQ := H.QS_pos
  omega

/- English proof (translation)
Apply `w_add_one_lt_of_dvd H hp` to reduce the goal to its premises. Establish `h1` using `Nat.dvd_sub_mod (n := r * (H.QS * H.q * H.d)) p`. Rewrite `h1` using `[h]`. Conclude with `dvd_trans (Dvd.intro_left r rfl) h1`.
-/
theorem w_add_one_lt {p : ℕ} (hp : 1 < p) (r : ℕ) (h : p % (r * (H.QS * H.q * H.d)) = 1) :
    Units.torsionOrder H.E + 1 < p := by
  apply w_add_one_lt_of_dvd H hp
  have h1 := Nat.dvd_sub_mod (n := r * (H.QS * H.q * H.d)) p
  rw [h] at h1
  exact dvd_trans (Dvd.intro_left r rfl) h1

end UpperTheory.Mu
