import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Both sides reduce to the same expression. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Split into cases according to the possible forms of the given data.

Treat this case separately. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
