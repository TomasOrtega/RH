import Mathlib
import Formalism.SharpRestriction.Divisibility.JumpSets
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExponentLogLeOfCut

open Formalism.BasicNotions Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace UpperTheory.ExcSet

/- English proof (translation)
Establish `hq : D.host.q.Prime` using `D.host.hyp.1`. Establish `hd : D.host.d.Prime` using `D.host.hyp.2.1`. Unfold `Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.HC.HostRaw.small`. Break down `(Nat.Prime.dvd_mul hl).1 h with h2 | h2` into its components or cases. Break down `(Nat.Prime.dvd_mul hl).1 h2 with h3 | h3` into its components or cases.

Conclude with `Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hl, h3, D.host.QS_pos.ne'⟩)`. Simplify using `[(Nat.prime_dvd_prime_iff_eq hl hq).1 h3]`. Simplify using `[(Nat.prime_dvd_prime_iff_eq hl hd).1 h2]`.
-/
theorem mem_ramSet_of_dvd (D : D7) {l : ℕ} (hl : l.Prime) (h : l ∣ D.host.condN) : l ∈ Formalism.MainNotions.JumpSetsAlt.ramSet D := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.HC.HostRaw.small
  rcases (Nat.Prime.dvd_mul hl).1 h with h2 | h2
  · rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
    · exact Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hl, h3, D.host.QS_pos.ne'⟩)
    · simp [(Nat.prime_dvd_prime_iff_eq hl hq).1 h3]
  · simp [(Nat.prime_dvd_prime_iff_eq hl hd).1 h2]

/- English proof (translation)
Unfold `Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.MainNotions.JumpSetsAlt.excSet`. Use `Finset.union_subset_union_right fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢`. The claim follows by propositional logic.
-/
theorem ramSet_subset_excSet (D : D7) : Formalism.MainNotions.JumpSetsAlt.ramSet D ⊆ Formalism.MainNotions.JumpSetsAlt.excSet D := by
  unfold Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.MainNotions.JumpSetsAlt.excSet
  refine Finset.union_subset_union_right fun x hx => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/- English proof (translation)
Introduce `h` and use `hS (ramSet_subset_excSet D (mem_ramSet_of_dvd D hl (D.host.der.discr_primes.1 l hl h)))`.
-/
theorem not_dvd_discr (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E := fun h =>
  hS (ramSet_subset_excSet D (mem_ramSet_of_dvd D hl (D.host.der.discr_primes.1 l hl h)))

/- English proof (translation)
Establish `h1 : l ≤ D.host.QS` using `Nat.le_of_mem_primeFactors hl`. Establish `h2` using `D.host.QS_le`. Establish `h3 : D.R.f = 2 * D.R.n` using `rfl`. Establish `h4` using `hH.t_ge`. Establish `h5` using `hH.f_pos`.

Establish `h6 : l ≤ P.k * P.t`. Establish `: D.R.n ^ 2 ≤ P.k * P.t`. Rewrite using `[sq]; exact Nat.mul_le_mul (by omega) (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `h7 : (l : ℝ) ≤ (P.k : ℝ) * (P.t : ℝ)` using `by exact_mod_cast h6`.

Establish `hk : (0 : ℝ) < P.k` using `by exact_mod_cast (by omega : 0 < P.k)`. Establish `ht : (0 : ℝ) < P.t` using `by exact_mod_cast (by omega : 0 < P.t)`. Establish `hc` using `(Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLJ_holds P hH hL).1`. Establish `hb` using `hL.b_gt`. Use `h7.trans (le_trans ?_ hc)` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ (by positivity)]`. Use polynomial arithmetic with `[mul_pos hk ht, sq_nonneg ((P.k : ℝ) * P.t)]`.
-/
theorem small_le_lJ (D : D7) (P : Par) (hH : P.Hyp) (hL : P.Large) (hf : P.f = D.R.f) (hfk : P.f ≤ P.k)
    {l : ℕ} (hl : l ∈ D.host.small) : (l : ℝ) ≤ P.lJ := by
  have h1 : l ≤ D.host.QS := Nat.le_of_mem_primeFactors hl
  have h2 := D.host.QS_le
  have h3 : D.R.f = 2 * D.R.n := rfl
  have h4 := hH.t_ge
  have h5 := hH.f_pos
  have h6 : l ≤ P.k * P.t := by
    have : D.R.n ^ 2 ≤ P.k * P.t := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have h7 : (l : ℝ) ≤ (P.k : ℝ) * (P.t : ℝ) := by exact_mod_cast h6
  have hk : (0 : ℝ) < P.k := by exact_mod_cast (by omega : 0 < P.k)
  have ht : (0 : ℝ) < P.t := by exact_mod_cast (by omega : 0 < P.t)
  have hc := (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLJ_holds P hH hL).1
  have hb := hL.b_gt
  refine h7.trans (le_trans ?_ hc)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hk ht, sq_nonneg ((P.k : ℝ) * P.t)]

/- English proof (translation)
Set `S : Finset ℕ` to `{D.host.q, D.host.d, D.host.pde, D.host.pde'}`. Set `W' : Wts ι` to `{ W with Sp := S }`. Establish `hW' : W'.Ok P` using `⟨hW.anti, hW.what₂, hW.block, hW.centre, hW.window, hW.cloud, hW.low, hW.thick, hW.other⟩`. Establish `hS : W'.Sp.card ≤ 5` using `(Finset.card_le_four).trans (by norm_num)`. Establish `hJ : ∀ l, W'.Jrec7 P l = W.Jrec7 P l`.

Introduce `l`. Establish `e : ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W'.Sp) ↔ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp)`. Rewrite using `[hSp]`. Use `show (_ ∨ _ ∨ l ∈ S) ↔ (_ ∨ _ ∨ l ∈ D.host.small ∪ S)`. Rewrite using `[Finset.mem_union]`.

Use `fun h => small_le_lJ D P hH hL hf hR.f_le (l := l) h` as an intermediate fact. The claim follows by propositional logic. Unfold `Wts.Jrec7`. Distinguish the cases in `hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp`. Rewrite using `[if_pos hc, if_pos (e.2 hc)]`.

Both sides reduce to the same expression. Rewrite using `[if_neg hc, if_neg (fun h => hc (e.1 h))]`. Both sides reduce to the same expression. Establish `h` using `GlobalTheory.sum_exponent_log_le_of_cut hC P X' A hH hL hR hB ι W' hW' hcard hS T hT Q hQ`. Simplify `h` using `only [hJ]`.
-/
theorem sum_exponent_log_le (hC : Formalism.CohomologicalDescent.E.ExCut) (D : D7) (P : Par) (X' A : ℝ) (hH : P.Hyp) (hL : P.Large)
    (hR : LargeParameterEstimates.Rows P X' A) (hB : LargeParameterEstimates.Big P.L P.x X' A) (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι) (hW : W.Ok P)
    (hcard : Fintype.card ι = P.f) (hf : P.f = D.R.f) (hSp : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D)
    (T : ℕ) (hT : W.T2.card ≤ T) (Q : Finset ℕ) (hQ : ∀ l ∈ Q, l.Prime) :
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  let S : Finset ℕ := {D.host.q, D.host.d, D.host.pde, D.host.pde'}
  let W' : Wts ι := { W with Sp := S }
  have hW' : W'.Ok P := ⟨hW.anti, hW.what₂, hW.block, hW.centre, hW.window, hW.cloud, hW.low, hW.thick, hW.other⟩
  have hS : W'.Sp.card ≤ 5 := (Finset.card_le_four).trans (by norm_num)
  have hJ : ∀ l, W'.Jrec7 P l = W.Jrec7 P l := by
    intro l
    have e : ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W'.Sp) ↔ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rw [hSp]
      show (_ ∨ _ ∨ l ∈ S) ↔ (_ ∨ _ ∨ l ∈ D.host.small ∪ S)
      rw [Finset.mem_union]
      have := fun h => small_le_lJ D P hH hL hf hR.f_le (l := l) h
      tauto
    unfold Wts.Jrec7
    by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [if_pos hc, if_pos (e.2 hc)]; rfl
    · rw [if_neg hc, if_neg (fun h => hc (e.1 h))]; rfl
  have h := GlobalTheory.sum_exponent_log_le_of_cut hC P X' A hH hL hR hB ι W' hW' hcard hS T hT Q hQ
  simpa only [hJ] using h

end UpperTheory.ExcSet
