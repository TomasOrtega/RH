import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestRoom
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

/- English proof (translation)
Establish `hp5 : (5 : ℝ) ≤ X.p` using `by exact_mod_cast St.p5`. Establish `hp : (0 : ℝ) < X.p` using `by linarith`. Establish `hN1 : (1 : ℝ) ≤ X.N1` using `by exact_mod_cast St.N1pos`. Establish `hk : (1 : ℝ) ≤ X.k` using `by have := St.N1k; linarith`. Establish `hk0 : (0 : ℝ) < X.k` using `by linarith`.

Establish `hQ : (1 : ℝ) ≤ X.Q` using `one_le_pow₀ (by linarith)`. Establish `hcr : (1 : ℝ) ≤ X.c` using `by exact_mod_cast hc`. Establish `hLa : (0 : ℝ) ≤ X.La C0` using `by have := St.La1; linarith`. Establish `ha : (0 : ℝ) ≤ X.a` using `Nat.cast_nonneg _`. Establish `hb : (0 : ℝ) ≤ X.b'` using `St.bpos.le`.

Establish `A1 : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2` using `by positivity`. Establish `B1 : 0 ≤ X.b' / (X.p : ℝ)` using `by positivity`. Establish `L0 : 0 ≤ X.La C0 * X.a / (X.p * X.k)` using `by positivity`. Establish `L2 : 0 ≤ X.La C0 * X.b' / X.k` using `by positivity`. Establish `e1 : X.La C0 * X.N1 * X.a / (X.p * X.k) = X.N1 * (X.La C0 * X.a / (X.p * X.k))` using `by ring`.

Establish `hL1 : X.La C0 * X.a / (X.p * X.k) ≤ X.La C0 * X.N1 * X.a / (X.p * X.k)`. Rewrite using `[e1]`. Conclude with `le_mul_of_one_le_left L0 hN1`. Establish `e2 : X.La C0 / X.k * (4 * (X.a : ℝ) / X.p) = 4 * (X.La C0 * X.a / (X.p * X.k))`. Clear the denominators using the available nonvanishing facts.

Establish `e3 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) = (X.a : ℝ) / (X.p : ℝ) ^ 2 * (16 / X.p)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h16 : 16 / (X.p : ℝ) ≤ 4`. Rewrite using `[div_le_iff₀ hp]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) ≤ 4 * ((X.a : ℝ) / (X.p : ℝ) ^ 2)`. Rewrite using `[e3, mul_comm 4]`. Conclude with `mul_le_mul_of_nonneg_left h16 A1`. Establish `e5 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 * X.b' / X.k)` using `by ring`.

Establish `e6 : 3 * X.b' / (X.p : ℝ) = 3 * (X.b' / X.p)` using `by ring`. Establish `hO : localOrderCap C0 X ≤ 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) + 4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k)`. Unfold `localOrderCap`. Rewrite using `[add_mul, e2, e5, e6]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `L1 : 0 ≤ X.La C0 * X.N1 * X.a / (X.p * X.k)` using `le_trans L0 hL1`. Establish `hfirst : 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) + 4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) ≤ CE1 * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k)`. Establish `hs : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k`. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_right h1 hs` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkQ : 1 ≤ X.k * X.Q` using `one_le_mul_of_one_le_of_one_le hk hQ`. Establish `hT : 0 ≤ X.k * X.N1 * X.Q * X.c` using `by positivity`. Establish `t1 : X.k * X.N1 * X.Q * X.c ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c`. Establish `: X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = (X.k * X.Q) * (X.k * X.N1 * X.Q * X.c)` using `by ring`.

Rewrite using `[this]`. Conclude with `le_mul_of_one_le_left hT hkQ`. Establish `t2 : (X.N1 : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c`. Establish `h0 : 0 ≤ (X.N1 : ℝ) * (X.k * X.Q)` using `by positivity`. Establish `: X.k * X.N1 * X.Q * X.c = (X.N1 * (X.k * X.Q)) * X.c` using `by ring`.

Rewrite using `[this]`. Conclude with `le_mul_of_one_le_right h0 hcr`. Establish `t3 : (X.c : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c`. Establish `h0 : 0 ≤ (X.c : ℝ) * (X.k * X.Q)` using `by positivity`. Establish `: X.k * X.N1 * X.Q * X.c = (X.c * (X.k * X.Q)) * X.N1` using `by ring`.

Rewrite using `[this]`. Conclude with `le_mul_of_one_le_right h0 hN1`. Establish `t4 : (X.c : ℝ) * ka1 X = 13 * (X.k * X.N1 * X.Q * X.c)` using `by unfold ka1; ring`. Establish `hT2 : 0 ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c` using `le_trans hT t1`. Establish `hsecond : (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c`.

Establish `: CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = CE2 * (X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c)` using `by ring`. Rewrite using `[this, t4]`. Use `mul_le_mul_of_nonneg_right h2 hT2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Loc.E0 errorTermBound`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem error_exponent_lower_bound {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2) (hc : 1 ≤ X.c) :
    localOrderCap C0 X + (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ X.E0 C0 CE1 CE2 := by
  have hp5 : (5 : ℝ) ≤ X.p := by exact_mod_cast St.p5
  have hp : (0 : ℝ) < X.p := by linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk : (1 : ℝ) ≤ X.k := by have := St.N1k; linarith
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hQ : (1 : ℝ) ≤ X.Q := one_le_pow₀ (by linarith)
  have hcr : (1 : ℝ) ≤ X.c := by exact_mod_cast hc
  have hLa : (0 : ℝ) ≤ X.La C0 := by have := St.La1; linarith
  have ha : (0 : ℝ) ≤ X.a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ X.b' := St.bpos.le
  have A1 : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 := by positivity
  have B1 : 0 ≤ X.b' / (X.p : ℝ) := by positivity
  have L0 : 0 ≤ X.La C0 * X.a / (X.p * X.k) := by positivity
  have L2 : 0 ≤ X.La C0 * X.b' / X.k := by positivity
  have e1 : X.La C0 * X.N1 * X.a / (X.p * X.k) = X.N1 * (X.La C0 * X.a / (X.p * X.k)) := by ring
  have hL1 : X.La C0 * X.a / (X.p * X.k) ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := by
    rw [e1]; exact le_mul_of_one_le_left L0 hN1
  have e2 : X.La C0 / X.k * (4 * (X.a : ℝ) / X.p) = 4 * (X.La C0 * X.a / (X.p * X.k)) := by
    field_simp
  have e3 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) = (X.a : ℝ) / (X.p : ℝ) ^ 2 * (16 / X.p) := by
    field_simp
    ring
  have h16 : 16 / (X.p : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hp]; linarith
  have e4 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) ≤ 4 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) := by
    rw [e3, mul_comm 4]; exact mul_le_mul_of_nonneg_left h16 A1
  have e5 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 * X.b' / X.k) := by ring
  have e6 : 3 * X.b' / (X.p : ℝ) = 3 * (X.b' / X.p) := by ring
  have hO : localOrderCap C0 X ≤ 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) := by
    unfold localOrderCap
    rw [add_mul, e2, e5, e6]
    linarith
  have L1 : 0 ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := le_trans L0 hL1
  have hfirst : 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) ≤
      CE1 * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k) := by
    have hs : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k := by
      linarith
    have := mul_le_mul_of_nonneg_right h1 hs
    linarith
  have hkQ : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le hk hQ
  have hT : 0 ≤ X.k * X.N1 * X.Q * X.c := by positivity
  have t1 : X.k * X.N1 * X.Q * X.c ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = (X.k * X.Q) * (X.k * X.N1 * X.Q * X.c) := by ring
    rw [this]; exact le_mul_of_one_le_left hT hkQ
  have t2 : (X.N1 : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.N1 : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.N1 * (X.k * X.Q)) * X.c := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hcr
  have t3 : (X.c : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.c : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.c * (X.k * X.Q)) * X.N1 := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hN1
  have t4 : (X.c : ℝ) * ka1 X = 13 * (X.k * X.N1 * X.Q * X.c) := by unfold ka1; ring
  have hT2 : 0 ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := le_trans hT t1
  have hsecond : (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = CE2 * (X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c) := by ring
    rw [this, t4]
    have := mul_le_mul_of_nonneg_right h2 hT2
    linarith
  unfold Loc.E0 errorTermBound
  linarith

/- English proof (translation)
Use `set j' := rot _ j with hj'`. Establish `hp0 : 0 < X.p` using `St.pP.pos`. Establish `hqG : X.p ^ segG X.TT j' ≤ X.p ^ X.G'` using `Nat.pow_le_pow_right hp0 (St.segB j').1`. Establish `hq1 : 1 ≤ X.p ^ segG X.TT j'` using `Nat.one_le_pow _ _ hp0`. Establish `hN2 : (∑ i : Fin (segS X.TT j'), X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)) ≤ X.N1 * ((X.m + 1) * X.p ^ X.G')`.

Establish `hi : ∀ i ∈ (Finset.univ : Finset (Fin (segS X.TT j'))), X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0) ≤ (X.m + 1) * X.p ^ X.G'`. Introduce `i _`. Establish `hd` using `(hβ j').1.1 i`. Establish `s1 : (∑ c : Fin X.m, (β j').rz i c.succ) ≤ X.m * (X.seg C0 CE1 CE2 j').P X.p i`. Use `Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin X.m)) (fun c => (β j').rz i c.succ) ((X.seg C0 CE1 CE2 j').P X.p i) (fun c _ => (hd c.succ).1.le)` as an intermediate fact.

Simplify using `using this`. Establish `s2 : (β j').ry i 0 ≤ (X.seg C0 CE1 CE2 j').P X.p i` using `(hd 0).2.le`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_card_nsmul _ _ _ hi` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Conclude with `this.trans (Nat.mul_le_mul_right _ (St.segB j').2)`. Establish `hN3 : X.c * (X.m * (X.p ^ segG X.TT j' - 1)) + (if j' = j0 then X.c else 0) ≤ X.c * ((X.m + 1) * X.p ^ X.G')`. Take `⟨q', hq'⟩ : ∃ q', X.p ^ segG X.TT j' = q' + 1` from `⟨X.p ^ segG X.TT j' - 1, by omega⟩`. Apply the tactic sequence `have hite : (if j' = j0 then X.c else 0) ≤ X.c := by split_ifs <;> omega`. Establish `e : X.p ^ segG X.TT j' - 1 = q'` using `by omega`.

Rewrite using `[e]`. Establish `h3 : X.m * q' + 1 ≤ (X.m + 1) * X.p ^ X.G'`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hnat : usedX X β a0 j0 j' ≤ (X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) + X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G')`.

Unfold `usedX`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∑ i : Fin (segS X.TT j'), (if (i : ℕ) < (X.seg C0 CE1 CE2 j').sigma then ((β j').sg i : ℤ) else 0) = ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[((hβ j').2.1 i (not_lt.1 h)).2.2.2]`. Both sides reduce to the same expression. Establish `hA` using `ha0 j'`.

Rewrite `hA` using `[hsum]`. Establish `hAr : ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ)`. Conclude with `hA` after adjusting the coercions. Establish `hfl : ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j' : ℕ) : ℝ)` using `Int.floor_le _`. Establish `hqr : (0 : ℝ) < ((X.p ^ segG X.TT j' : ℕ) : ℝ)` using `by exact_mod_cast hq1`.

Establish `hN1 : ((X.p ^ segG X.TT j' : ℕ) : ℝ) * ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ (X.a : ℝ) - X.E0 C0 CE1 CE2`. Use `(le_div_iff₀ hqr).1 (hAr.trans hfl)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc1 : 1 ≤ X.c` using `le_trans hn1 hnc`. Establish `hka : 0 ≤ ka1 X`.

Unfold `ka1`. Establish `hk : (0 : ℝ) ≤ X.k` using `by have := St.N1k; have : (0 : ℝ) ≤ X.N1 := Nat.cast_nonneg _; linarith`. Establish `hQ : (0 : ℝ) ≤ X.Q` using `by unfold Loc.Q; positivity`. Check the signs of the components of the expression. Establish `hoP : ((β j).oPlus : ℝ) ≤ localOrderCap C0 X + (X.c : ℝ) * ka1 X`.

Establish `h` using `(hβ j).2.2.2.2`. Establish `hcn : ((X.c - n : ℕ) : ℝ) ≤ (X.c : ℝ)` using `by exact_mod_cast Nat.sub_le _ _`. Use `mul_le_mul_of_nonneg_right hcn hka` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ)` using `(St.winA _ (next_mem X.TT j).1).1`.

Establish `hE` using `error_exponent_lower_bound St h1 h2 hc1`. Establish `hreal : ((usedX X β a0 j0 j' + (β j).oPlus : ℕ) : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ)`. Establish `hcast : ((usedX X β a0 j0 j' : ℕ) : ℝ) ≤ (((X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) + X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') : ℕ) : ℝ)` using `by exact_mod_cast hnat`. Establish `hk : X.k = (X.m : ℝ) + 1` using `rfl`. Establish `hQ : X.Q = (X.p : ℝ) ^ X.G'` using `rfl`.

Move the coercions through the operations in `at hcast hN1 ⊢`. Rewrite `hE` using `[hk, hQ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: usedX X β a0 j0 j' + (β j).oPlus ≤ segAPlus X.TT X.aT j` using `by exact_mod_cast hreal`. Use linear arithmetic over natural numbers and integers.
-/
theorem room_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2)
    (n : ℕ) (hn1 : 1 ≤ n) (hnc : n ≤ X.c) (β : GlobalTheory X)
    (hβ : ∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) (a0 : Fin (numSeg X.TT) → ℕ)
    (ha0 : ∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p)
    (j0 j : Fin (numSeg X.TT)) :
    usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus := by
  classical
  set j' := rot _ j with hj'
  have hp0 : 0 < X.p := St.pP.pos
  have hqG : X.p ^ segG X.TT j' ≤ X.p ^ X.G' := Nat.pow_le_pow_right hp0 (St.segB j').1
  have hq1 : 1 ≤ X.p ^ segG X.TT j' := Nat.one_le_pow _ _ hp0

  have hN2 : (∑ i : Fin (segS X.TT j'), X.p ^ (segDists X.TT j').get i *
      ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)) ≤ X.N1 * ((X.m + 1) * X.p ^ X.G') := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin (segS X.TT j'))), X.p ^ (segDists X.TT j').get i *
        ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0) ≤ (X.m + 1) * X.p ^ X.G' := by
      intro i _
      have hd := (hβ j').1.1 i
      have s1 : (∑ c : Fin X.m, (β j').rz i c.succ) ≤ X.m * (X.seg C0 CE1 CE2 j').P X.p i := by
        have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin X.m)) (fun c => (β j').rz i c.succ)
          ((X.seg C0 CE1 CE2 j').P X.p i) (fun c _ => (hd c.succ).1.le)
        simpa using this
      have s2 : (β j').ry i 0 ≤ (X.seg C0 CE1 CE2 j').P X.p i := (hd 0).2.le
      calc X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)
          ≤ X.p ^ (segDists X.TT j').get i * ((X.m + 1) * (X.seg C0 CE1 CE2 j').P X.p i) :=
            Nat.mul_le_mul_left _ (by linarith)
        _ = (X.m + 1) * (X.p ^ (segDists X.TT j').get i * (X.seg C0 CE1 CE2 j').P X.p i) := by ring
        _ = (X.m + 1) * X.p ^ segG X.TT j' := by rw [pd_mul_P]
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ hqG
    have := Finset.sum_le_card_nsmul _ _ _ hi
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (St.segB j').2)

  have hN3 : X.c * (X.m * (X.p ^ segG X.TT j' - 1)) + (if j' = j0 then X.c else 0) ≤ X.c * ((X.m + 1) * X.p ^ X.G') := by
    obtain ⟨q', hq'⟩ : ∃ q', X.p ^ segG X.TT j' = q' + 1 := ⟨X.p ^ segG X.TT j' - 1, by omega⟩
    have hite : (if j' = j0 then X.c else 0) ≤ X.c := by split_ifs <;> omega
    have e : X.p ^ segG X.TT j' - 1 = q' := by omega
    rw [e]
    have h3 : X.m * q' + 1 ≤ (X.m + 1) * X.p ^ X.G' := by
      calc X.m * q' + 1 ≤ (X.m + 1) * (q' + 1) := by nlinarith
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ (hq' ▸ hqG)
    calc X.c * (X.m * q') + (if j' = j0 then X.c else 0) ≤ X.c * (X.m * q') + X.c := by omega
      _ = X.c * (X.m * q' + 1) := by ring
      _ ≤ X.c * ((X.m + 1) * X.p ^ X.G') := Nat.mul_le_mul_left _ h3
  have hnat : usedX X β a0 j0 j' ≤ (X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') := by
    unfold usedX
    linarith

  have hsum : ∑ i : Fin (segS X.TT j'), (if (i : ℕ) < (X.seg C0 CE1 CE2 j').sigma then ((β j').sg i : ℤ) else 0) =
      ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · rw [((hβ j').2.1 i (not_lt.1 h)).2.2.2]; rfl
  have hA := ha0 j'
  rw [hsum] at hA
  have hAr : ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) := by
    exact_mod_cast hA
  have hfl : ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j' : ℕ) : ℝ) := Int.floor_le _
  have hqr : (0 : ℝ) < ((X.p ^ segG X.TT j' : ℕ) : ℝ) := by exact_mod_cast hq1
  have hN1 : ((X.p ^ segG X.TT j' : ℕ) : ℝ) * ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤
      (X.a : ℝ) - X.E0 C0 CE1 CE2 := by
    have := (le_div_iff₀ hqr).1 (hAr.trans hfl)
    linarith

  have hc1 : 1 ≤ X.c := le_trans hn1 hnc
  have hka : 0 ≤ ka1 X := by
    unfold ka1
    have hk : (0 : ℝ) ≤ X.k := by have := St.N1k; have : (0 : ℝ) ≤ X.N1 := Nat.cast_nonneg _; linarith
    have hQ : (0 : ℝ) ≤ X.Q := by unfold Loc.Q; positivity
    positivity
  have hoP : ((β j).oPlus : ℝ) ≤ localOrderCap C0 X + (X.c : ℝ) * ka1 X := by
    have h := (hβ j).2.2.2.2
    have hcn : ((X.c - n : ℕ) : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have := mul_le_mul_of_nonneg_right hcn hka
    linarith
  have haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := (St.winA _ (next_mem X.TT j).1).1
  have hE := error_exponent_lower_bound St h1 h2 hc1
  have hreal : ((usedX X β a0 j0 j' + (β j).oPlus : ℕ) : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := by
    have hcast : ((usedX X β a0 j0 j' : ℕ) : ℝ) ≤
        (((X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') : ℕ) : ℝ) := by exact_mod_cast hnat
    have hk : X.k = (X.m : ℝ) + 1 := rfl
    have hQ : X.Q = (X.p : ℝ) ^ X.G' := rfl
    push_cast at hcast hN1 ⊢
    rw [hk, hQ] at hE
    linarith
  have : usedX X β a0 j0 j' + (β j).oPlus ≤ segAPlus X.TT X.aT j := by exact_mod_cast hreal
  omega

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ a1 a2 _ _ _ _ _ _ t1 t2 t3 t4 t5 => ⟨⟨a1, a2⟩, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩`.
-/
theorem threshold_standard_seventeen : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => (17 ≤ CE1 ∧ 17 ≤ CE2) ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ a1 a2 _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨⟨a1, a2⟩, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

/- English proof (translation)
The claim follows from `TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc n hn1 hnc β hβ a0 ha0 j0 j => room_of_std (h.2 X hD hH hc) h.1.1 h.1.2 n hn1 hnc β hβ a0 ha0 j0 j) threshold_standard_seventeen`.
-/
theorem restRoom : RestRoom :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc n hn1 hnc β hβ a0 ha0 j0 j =>
    room_of_std (h.2 X hD hH hc) h.1.1 h.1.2 n hn1 hnc β hβ a0 ha0 j0 j) threshold_standard_seventeen

end Formalism.MainNotions.ColumnSystems.Pf
