import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul

/- English proof (translation)
Establish `h1 : up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B)) = fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit Q)`. Use function extensionality and compare the values at `j`. Simplify using `[up]`. Establish `h2 : formalLog (1 + X () : MvPowerSeries Unit Q) = (PowerSeries.log Q : MvPowerSeries Unit Q)`. Rewrite using `[formalLog, add_sub_cancel_left, PowerSeries.subst]`.

Conclude with `congrFun MvPowerSeries.subst_self _`. Establish `h3` using `formalLog_pow m (g := (1 + X () : MvPowerSeries Unit Q)) (by simp)`. Rewrite `h3` using `[h2]`. Rewrite using `[h1, Nat.cast_smul_eq_nsmul, ← h3]`. Both sides reduce to the same expression.
-/
theorem subst_pow_log (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ) :
    subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B)))
      (PowerSeries.log Q : MvPowerSeries Unit Q)
      = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  have h1 : up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))
      = fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit Q) := by
    funext j
    simp [up]
  have h2 : formalLog (1 + X () : MvPowerSeries Unit Q)
      = (PowerSeries.log Q : MvPowerSeries Unit Q) := by
    rw [formalLog, add_sub_cancel_left, PowerSeries.subst]
    exact congrFun MvPowerSeries.subst_self _
  have h3 := formalLog_pow m (g := (1 + X () : MvPowerSeries Unit Q)) (by simp)
  rw [h2] at h3
  rw [h1, Nat.cast_smul_eq_nsmul, ← h3]
  rfl

end GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul
