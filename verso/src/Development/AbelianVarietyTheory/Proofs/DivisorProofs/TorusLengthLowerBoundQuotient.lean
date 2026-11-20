import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.DividedNum

section Point

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

/- English proof (translation)
Establish `m2` using `D.R.two_le_m`. Establish `k3` using `D.R.m_add_three_le_k`. Establish `f8` using `h.f8`. Establish `hDd : (1 : ℝ) ≤ dimFlag (dat p i)`. Rewrite using `[hw.dim]`.

Conclude with `Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))` after adjusting the coercions. Establish `hm : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by omega : 0 < D.R.m)`. Establish `hkm : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : D.R.m ≤ D.R.k)`. Establish `hL : (0 : ℝ) ≤ L.sc.L` using `by linarith [h.big.2.1]`. Establish `hZ : 0 ≤ zBase L` using `by unfold zBase; positivity`.

Establish `hP : zBase L ^ 24 ≤ PP ^ 2`. Rewrite using `[show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]`. Conclude with `pow_le_pow_left₀ (by positivity) h.ppLow 2`. Establish `hPP : 0 ≤ PP ^ 2` using `sq_nonneg _`. Establish `h1 : PP ^ 2 ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)`.

Rewrite using `[le_div_iff₀ hm]`. Establish `a : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2` using `one_le_pow₀ hDd`. Establish `b : PP ^ 2 * D.R.m ≤ PP ^ 2 * D.R.k` using `mul_le_mul_of_nonneg_left hkm hPP`. Establish `c : PP ^ 2 * D.R.k ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k` using `mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hPP a) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hP.trans (h1.trans (Nat.le_ceil _))`.
-/
theorem zBase_pow_le_lenT {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) := by
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hL : (0 : ℝ) ≤ L.sc.L := by linarith [h.big.2.1]
  have hZ : 0 ≤ zBase L := by unfold zBase; positivity
  have hP : zBase L ^ 24 ≤ PP ^ 2 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h.ppLow 2
  have hPP : 0 ≤ PP ^ 2 := sq_nonneg _
  have h1 : PP ^ 2 ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]
    have a : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
    have b : PP ^ 2 * D.R.m ≤ PP ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm hPP
    have c : PP ^ 2 * D.R.k ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hPP a) (by linarith)
    linarith
  exact hP.trans (h1.trans (Nat.le_ceil _))

/- English proof (translation)
Use `⟨zBase_pow_le_lenT p i h hw, fun u1 hq => ?_⟩` and prove the remaining obligations. Take `⟨h0, S, eta, hS, he, hP, h4, hh, hH⟩` from `hw.hyp hi`. Establish `hW` using `hH u1`. Establish `hD` using `(quo_iff p i PP h0 S eta u1).1 hq`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨hp1, hp2⟩` from `GlobalTheory.CovHt.BudgetPf.pp_bounds h`. Establish `m2` using `D.R.two_le_m`. Establish `k3` using `D.R.m_add_three_le_k`. Establish `f8` using `h.f8`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by omega : 1 ≤ D.R.f)`.

Establish `hr : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f` using `by rw [← hw.card, Nat.card_eq_fintype_card]`. Establish `hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r` using `by rw [hw.sig.2.2]`.

Establish `hT : (0 : ℝ) ≤ lenT p i PP` using `Nat.cast_nonneg _`. Establish `fr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP`. Use `le_trans ?_ hp1` and prove the remaining obligations. Establish `f2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2` using `le_self_pow₀ hf (by norm_num)`. Establish `r2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 5` using `pow_le_pow_right₀ hr (by norm_num)`.

Use `gcongr`. Establish `rr : (D.R.r : ℝ) ^ 2 ≤ PP` using `le_trans (le_mul_of_one_le_left (by positivity) hf) fr`. Establish `r1 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 2` using `le_self_pow₀ hr (by norm_num)`. Establish `hPP : 1 ≤ PP` using `by nlinarith`. Take `⟨a1, -, -⟩` from `GlobalTheory.MeanTop.divided_weight_size _ _ _ hW hD`.

Establish `a3` using `GlobalTheory.CovHt.BudgetPf.l1_u_le _ hW hS`. Establish `e1 : (dat p i).p + (dat p i).q - (wtsAt p i PP h0 S eta u1).kc = D.R.m` using `by show (dat p i).p + (dat p i).q - (D.R.k - 1) = _`. Rewrite using `[hw.sig.2.2]`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.

Rewrite `a3` using `[e1, hcard, hN]`. Rewrite `a1` using `[hcard, hN]`. Express the relevant statement in the definitionally equal form `_ ≤ D.R.f * (D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) at a3`. Express the relevant statement in the definitionally equal form `(lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ _ + D.R.f * D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) at a1`. Establish `c1 : ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4`.

Conclude with `(cZero_spec D ((i : ℕ) + 1)).2.2` after adjusting the coercions. Establish `c2 : (D.R.r : ℝ) * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) ≤ 26 * L.sc.b`. Use `mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ D.R.r)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Choose the witnesses or unpack the hypotheses as in `⟨τ⟩ : Nonempty (Psi p.T.Q.H) := by`.

Rewrite using `[← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hw.card]`. Use linear arithmetic over natural numbers and integers. Establish `w1 : L.sc.w'' D.R.n ≤ 8 * L.sc.b`. Establish `h1` using `hw.low τ`. Establish `h2 : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 4 * L.sc.b`.

Unfold `anchor`. Use `split_ifs`. Conclude with `(le_abs_self _).trans (hw.up τ _)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `s1 : (D.R.r : ℝ) * S ≤ 800 * L.sc.b`. Establish `h1 : (D.R.r : ℝ) * S ≤ PP * S` using `mul_le_mul_of_nonneg_right (by linarith) hS`. Use polynomial arithmetic with `[mul_nonneg (by linarith : 0 ≤ PP) he]`. Establish `bm : L.sc.b ≤ D.R.m * L.sc.b` using `le_mul_of_one_le_left hb.le hm`.

Establish `t2 : (D.R.f : ℝ) * ((D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) + D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r)) ≤ D.R.f * (834 * (D.R.m * L.sc.b))` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `t3 : (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * (D.R.f * D.R.m * L.sc.b)` using `by nlinarith`. Establish `u0 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ unitE p`. Rewrite using `[hw.unit]`. Establish `hL` using `h.big.2.1`.

Establish `hll` using `h.big.2.2.2`. Establish `a0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b` using `by positivity`. Establish `a1 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ D.R.f * D.R.m * L.sc.b * L.sc.L` using `le_mul_of_one_le_right a0 (by linarith)`. Establish `a2 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L` using `le_trans a0 a1`. Conclude with `a1.trans (le_mul_of_one_le_right a2 hll)`.

Use `show (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * unitE p`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `τ a b hab`. Take `⟨g1, g2, -⟩` from `GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab`. Establish `hT1 : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP` using `hW.h1`.

Express the relevant statement in the definitionally equal form `((b : ℕ) ≠ (dat p i).p → (lenT p i PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ) ≤ u1 τ a - u1 τ b) at g1`. Express the relevant statement in the definitionally equal form `((b : ℕ) = (dat p i).p → h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) ∧ _) at g2`. Distinguish the cases in `hb : (b : ℕ) = (dat p i).p`. Establish `k` using `(g2 hb).1`. Establish `hT0 : (1 : ℤ) ≤ lenT p i PP` using `by exact_mod_cast (by omega : 1 ≤ lenT p i PP)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `k` using `g1 hb`. Establish `: (0 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem at_point {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) ∧ ∀ u1, Quo p i PP u1 →
      lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ 834 * unitE p ∧
      ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := by
  refine ⟨zBase_pow_le_lenT p i h hw, fun u1 hq => ?_⟩
  obtain ⟨h0, S, eta, hS, he, hP, h4, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  refine ⟨?_, ?_⟩
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.CovHt.BudgetPf.pp_bounds h
    have m2 := D.R.two_le_m
    have k3 := D.R.m_add_three_le_k
    have f8 := h.f8
    have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
    have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hb : 0 < L.sc.b := Real.exp_pos _
    have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
    have hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hw.sig.2.2]
    have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have fr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP := by
      refine le_trans ?_ hp1
      have f2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ hf (by norm_num)
      have r2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 5 := pow_le_pow_right₀ hr (by norm_num)
      gcongr
    have rr : (D.R.r : ℝ) ^ 2 ≤ PP := le_trans (le_mul_of_one_le_left (by positivity) hf) fr
    have r1 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 2 := le_self_pow₀ hr (by norm_num)
    have hPP : 1 ≤ PP := by nlinarith
    obtain ⟨a1, -, -⟩ := GlobalTheory.MeanTop.divided_weight_size _ _ _ hW hD
    have a3 := GlobalTheory.CovHt.BudgetPf.l1_u_le _ hW hS
    have e1 : (dat p i).p + (dat p i).q - (wtsAt p i PP h0 S eta u1).kc = D.R.m := by
      show (dat p i).p + (dat p i).q - (D.R.k - 1) = _
      rw [hw.sig.2.2]; unfold Ranks.r; omega
    rw [e1, hcard, hN] at a3
    rw [hcard, hN] at a1
    change _ ≤ D.R.f * (D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) at a3
    change (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ _ + D.R.f * D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) at a1
    have c1 : ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by
      exact_mod_cast (cZero_spec D ((i : ℕ) + 1)).2.2
    have c2 : (D.R.r : ℝ) * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) ≤ 26 * L.sc.b := by
      have := mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ D.R.r)
      nlinarith
    obtain ⟨τ⟩ : Nonempty (Psi p.T.Q.H) := by
      rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hw.card]; omega
    have w1 : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
      have h1 := hw.low τ
      have h2 : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 4 * L.sc.b := by
        unfold anchor
        split_ifs
        · exact (le_abs_self _).trans (hw.up τ _)
        · push_cast; linarith
      linarith
    have s1 : (D.R.r : ℝ) * S ≤ 800 * L.sc.b := by
      have h1 : (D.R.r : ℝ) * S ≤ PP * S := mul_le_mul_of_nonneg_right (by linarith) hS
      nlinarith [mul_nonneg (by linarith : 0 ≤ PP) he]
    have bm : L.sc.b ≤ D.R.m * L.sc.b := le_mul_of_one_le_left hb.le hm
    have t2 : (D.R.f : ℝ) * ((D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) + D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r)) ≤
        D.R.f * (834 * (D.R.m * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have t3 : (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * (D.R.f * D.R.m * L.sc.b) := by nlinarith
    have u0 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ unitE p := by
      rw [hw.unit]
      have hL := h.big.2.1
      have hll := h.big.2.2.2
      have a0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b := by positivity
      have a1 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ D.R.f * D.R.m * L.sc.b * L.sc.L :=
        le_mul_of_one_le_right a0 (by linarith)
      have a2 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := le_trans a0 a1
      exact a1.trans (le_mul_of_one_le_right a2 hll)
    show (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * unitE p
    linarith
  · intro τ a b hab
    obtain ⟨g1, g2, -⟩ := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab
    have hT1 : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    change ((b : ℕ) ≠ (dat p i).p → (lenT p i PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ) ≤ u1 τ a - u1 τ b) at g1
    change ((b : ℕ) = (dat p i).p → h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) ∧ _) at g2
    by_cases hb : (b : ℕ) = (dat p i).p
    · have k := (g2 hb).1
      have hT0 : (1 : ℤ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
      nlinarith
    · have k := g1 hb
      have : (0 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
      linarith

end Point

/- English proof (translation)
Introduce `_` and use `Closed.imp (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.CovTop.WtShape.wtN) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by obtain ⟨x0, h⟩ := h1.and h2 exact ⟨834, by norm_num, x0, fun x hx hle ι p hp i hi => at_point p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 …`.
-/
theorem dividedWeight : Size → Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    zBase (Fm.L x ι) ^ 24 ≤ lenT p i PP ∧ ∀ u1, Quo p i PP u1 → lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ C * unitE p ∧
      ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := fun _ =>
  Closed.imp (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.CovTop.WtShape.wtN) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by
    obtain ⟨x0, h⟩ := h1.and h2
    exact ⟨834, by norm_num, x0, fun x hx hle ι p hp i hi =>
      at_point p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) hi⟩

end GlobalTheory.CovHt.DividedNum
