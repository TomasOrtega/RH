import Mathlib

namespace Bl.general_b_fact_second_last

/- English proof (translation)
Introduce `B S`. Proceed by induction on `S with`. Consider the case `zero => intro c _ _ m`. Conclude with `m.elim0`. Consider the case `succ n ih`.

Introduce `c hc hs m`. Establish `hB : 0 < B` using `lt_of_le_of_lt (abs_nonneg _) (hc 0)`. Rewrite `hs` using `[Fin.sum_univ_succ]`. Establish `h2 : ∑ i : Fin n, c i.succ * B ^ (i.succ).val = B * ∑ i : Fin n, c i.succ * B ^ i.val`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hs` using `[h2, Fin.val_zero, pow_zero, mul_one]`. Establish `hd : B ∣ c 0` using `⟨-(∑ i : Fin n, c i.succ * B ^ i.val), by rw [mul_neg]; linarith⟩`.

Establish `h0 : c 0 = 0` using `Int.eq_zero_of_abs_lt_dvd hd (hc 0)`. Rewrite `hs` using `[h0, zero_add]`. Establish `hT : ∑ i : Fin n, c i.succ * B ^ i.val = 0`. Break down `mul_eq_zero.mp hs with h | h` into its components or cases. Conclude with `absurd h hB.ne'`.

Conclude with `h`. Establish `ih'` using `ih (fun i => c i.succ) (fun i => hc _) hT`. Conclude with `Fin.cases h0 (fun i => ih' i) m`.
-/
theorem goal1 :
  ∀ (B : Int) {S : Nat} (c : Fin S → Int),
  (∀ (m : Fin S), LT.lt.{0} (abs.{0} (c m)) B) →
    Eq.{1} (Finset.sum.{0, 0} Finset.univ.{0} fun (m : Fin S) ↦ HMul.hMul.{0, 0, 0} (c m) (HPow.hPow.{0, 0, 0} B m.val))
        0 →
      ∀ (m : Fin S), Eq.{1} (c m) 0 := by
  intro B S
  induction S with
  | zero => intro c _ _ m; exact m.elim0
  | succ n ih =>
    intro c hc hs m
    have hB : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hc 0)
    rw [Fin.sum_univ_succ] at hs
    have h2 : ∑ i : Fin n, c i.succ * B ^ (i.succ).val = B * ∑ i : Fin n, c i.succ * B ^ i.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [h2, Fin.val_zero, pow_zero, mul_one] at hs
    have hd : B ∣ c 0 := ⟨-(∑ i : Fin n, c i.succ * B ^ i.val), by rw [mul_neg]; linarith⟩
    have h0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (hc 0)
    rw [h0, zero_add] at hs
    have hT : ∑ i : Fin n, c i.succ * B ^ i.val = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hB.ne'
      · exact h
    have ih' := ih (fun i => c i.succ) (fun i => hc _) hT
    exact Fin.cases h0 (fun i => ih' i) m

end Bl.general_b_fact_second_last
