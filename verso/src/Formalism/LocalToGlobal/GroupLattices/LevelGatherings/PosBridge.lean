import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.HermitianColumns.StarConj

noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cc_sq (e : Formalism.HC.Frame) : e.cc * e.cc = 1 := by
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem cc_pow (e : Formalism.HC.Frame) (s : ℕ) : e.cc ^ s = if s % 2 = 1 then e.cc else 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [if_neg (by omega), one_mul, if_pos (by omega)]
    · rw [if_pos h, cc_sq, if_neg (by omega)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem embLL_mem_alg (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic z).algHom D.what₂.embLL.toRatAlgHom

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem emb_conj_pow (D : D7) (g : D.R.GG) (s : ℕ) (x : D.host.E) :
    D.host.emb (g * D.R.cc ^ s) x = D.host.emb g (if s % 2 = 1 then D.host.conj x else x) := by
  rw [emb_mul, cc_pow]
  split_ifs
  · rfl
  · simp [Formalism.BasicNotions.Host.sigmaOf]

end Formalism.L2.G
