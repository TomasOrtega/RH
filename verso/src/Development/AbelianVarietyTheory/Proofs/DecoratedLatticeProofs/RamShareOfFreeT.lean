import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeLineRamifiedFormula
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Establish `h` using `Formalism.MainNotions.product_first_zeroth_parts.rank_nat W`. Establish `hT2 : 2 ≤ (D.mem u).A.T` using `((D.mem u).A.T_prime).two_le`. Unfold `RamShare dU`. Rewrite using `[d0_eq]`. Establish `h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f = (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f`.

Establish `e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2` using `by omega`. Rewrite `h` using `[e2]`. Use `congrArg (fun n : ℕ => (n : ℝ)) h` as an intermediate fact. Simplify using `only [Nat.cast_mul, Nat.cast_pow] at this`. Rewrite `this` using `[Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2]`.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1`. Establish `: (2 : ℝ) ≤ ((D.mem u).A.T : ℝ)` using `by exact_mod_cast hT2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1)` using `by field_simp; ring`. Rewrite using `[e, div_pow]`. Establish `hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0` using `pow_ne_zero _ hpos.ne'`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[h']`.
-/
theorem ramShare_of_freeT {D : D7} {u : D.what₂.Word} (W : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) : RamShare D u := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.rank_nat W
  have hT2 : 2 ≤ (D.mem u).A.T := ((D.mem u).A.T_prime).two_le
  unfold RamShare dU
  rw [d0_eq]
  have h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f =
      (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f := by
    have e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2 := by omega
    rw [e2] at h
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2] at this
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
    linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1) := by
    field_simp; ring
  rw [e, div_pow]
  have hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp
  linarith [h']

/- English proof (translation)
The claim follows from `TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u) (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u`.
-/
theorem ramShare_of_trueD (D : D7) (u : D.what₂.Word) (hD : TrueD D) : RamShare D u :=
  TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u)
    (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u

end GlobalTheory.Core.Rk
