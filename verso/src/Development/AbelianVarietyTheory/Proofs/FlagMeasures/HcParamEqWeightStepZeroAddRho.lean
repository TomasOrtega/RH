import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions

namespace GlobalTheory

/- English proof (translation)
Introduce `D u τ i`. Rewrite using `[Formalism.L2.Forms.lamT_zero]`. Establish `h0` using `(D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)`. Rewrite `h0` using `[dif_pos (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)]`. Establish `hq : ((D.hcW u τ).u i : ℚ) = (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i`.

Rewrite using `[h0, hcToWeightQ]`. Simplify using the standard rewrite rules. Rewrite using `[hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hcParam_eq_weight_step_zero_add_rho : ∀ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), (((D.hcW u τ).u i : ℚ) : ℝ) = ((Formalism.L2.Forms.lamT u 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℝ) + ((rhoVec D.R.k i : ℚ) : ℝ) := by
  intro D u τ i
  rw [Formalism.L2.Forms.lamT_zero]
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)
  rw [dif_pos (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)] at h0
  have hq : ((D.hcW u τ).u i : ℚ) =
      (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i := by
    rw [h0, hcToWeightQ]
    simp
  rw [hq]
  push_cast
  ring

end GlobalTheory
