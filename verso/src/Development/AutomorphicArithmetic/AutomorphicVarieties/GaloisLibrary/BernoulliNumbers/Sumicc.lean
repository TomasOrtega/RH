import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `M _ N _ G`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Use `Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun x : ZMod N => if x.val = 0 then N else x.val) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`. Conclude with `Finset.mem_univ _`.

Introduce `x _`. Establish `hx` using `ZMod.val_lt x`. Use `Finset.mem_Icc.2 ?_` and prove the remaining obligations. Use `split_ifs with h0`. Conclude with `⟨hN, le_rfl⟩`.

Conclude with `⟨Nat.pos_of_ne_zero h0, hx.le⟩`. Introduce `a ha`. Establish `ha'` using `Finset.mem_Icc.1 ha`. Simplify using `only [ZMod.val_natCast]`. Break down `Nat.lt_or_ge a N with h | h` into its components or cases.

Rewrite using `[Nat.mod_eq_of_lt h, if_neg (by omega)]`. Establish `hEq : a = N` using `by omega`. Substitute `hEq` using the available equality. Simplify using the standard rewrite rules. Introduce `x _ split_ifs with h0`.

Rewrite using `[ZMod.natCast_self]`. Conclude with `((ZMod.val_eq_zero x).1 h0).symm`. Conclude with `ZMod.natCast_zmod_val x`. Introduce `a _`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Bern.b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M), ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  intro M _ N _ G
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun x : ZMod N => if x.val = 0 then N else x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro x _
    have hx := ZMod.val_lt x
    refine Finset.mem_Icc.2 ?_
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hx.le⟩
  · intro a ha
    have ha' := Finset.mem_Icc.1 ha
    simp only [ZMod.val_natCast]
    rcases Nat.lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    · have hEq : a = N := by omega
      subst hEq
      simp
  · intro x _
    split_ifs with h0
    · rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero x).1 h0).symm
    · exact ZMod.natCast_zmod_val x
  · intro a _
    rfl
