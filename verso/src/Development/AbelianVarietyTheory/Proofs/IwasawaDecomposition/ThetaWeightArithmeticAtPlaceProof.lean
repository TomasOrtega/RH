import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes Formalism.L2.NTheta

namespace GlobalTheory.PairWeightArith

/- English proof (translation)
Take `⟨z, rfl⟩` from `hz`. Establish `hz : 0 ≤ z` using `by exact_mod_cast h0`. Rewrite using `[Int.floor_intCast]`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hz`. Simplify using the standard rewrite rules.
-/
lemma toNat_floor_cast {x : ℚ} (hz : ∃ z : ℤ, x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hz
  have hz : 0 ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hc` using `c.2`. Unfold `lamAt`. Rewrite using `[dif_neg (by omega), dif_pos (by omega)]`. Use `congr 2`.

Conclude with `Fin.ext (by simp only; omega)`.
-/
lemma lamAt_tail {R : Ranks} (h : HCParam R) (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) :
    lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Use `lamAt_add_add_le h d a hb` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma lamAt_anti {R : Ranks} (h : HCParam R) {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) :
    lamAt h b + b ≤ lamAt h a + a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := lamAt_add_add_le h d a hb
  push_cast
  linarith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

/- English proof (translation)
Establish `h` using `D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _`. Rewrite using `[h]`. Simplify using `[Ranks.sigW]`.

Use `show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
lemma sig_eq : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1) := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨?_, ?_⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `sig_eq D i τ`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hi` using `i.2`. Rewrite using `[h1, h2]`. Unfold `Ranks.r`.

Use linear arithmetic over natural numbers and integers.
-/
lemma pq_eq : pS D i τ + qS D i τ = D.R.r := by
  obtain ⟨h1, h2⟩ := sig_eq D i τ
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  rw [h1, h2]; unfold Ranks.r; omega

/- English proof (translation)
Take `⟨s, hs⟩` from `D.R.t_odd`. Conclude with `⟨s, by exact_mod_cast hs⟩`.
-/
lemma t_half : ∃ s : ℕ, (D.R.t : ℚ) = 2 * s + 1 := by
  obtain ⟨s, hs⟩ := D.R.t_odd
  exact ⟨s, by exact_mod_cast hs⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `t_half D`. Take `⟨z, hz⟩` from `lamAt_int (D.hc τ) a`. Take `⟨e, he⟩` from `(D.hc τ).e_int i`. Use `⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩` and prove the remaining obligations. Simplify using `only [aPlusQ, centred, eS, hs, hz, he]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aPlusQ_int (a : ℕ) : ∃ z : ℤ, aPlusQ D i τ a = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) a
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩
  simp only [aPlusQ, centred, eS, hs, hz, he]
  push_cast; ring

/- English proof (translation)
Take `⟨s, hs⟩` from `t_half D`. Take `⟨z, hz⟩` from `lamAt_int (D.hc τ) (pS D i τ + c)`. Take `⟨e, he⟩` from `(D.hc τ).e_int i`. Use `⟨-(z + e + c + 1 + s), ?_⟩` and prove the remaining obligations. Simplify using `only [dRowQ, centred, eS, hs, hz, he]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma neg_dRowQ_int (c : ℕ) : ∃ z : ℤ, -dRowQ D i τ c = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) (pS D i τ + c)
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨-(z + e + c + 1 + s), ?_⟩
  simp only [dRowQ, centred, eS, hs, hz, he]
  push_cast; ring

/- English proof (translation)
Establish `h` using `pq_eq D i τ`. Use `lamAt_anti (D.hc τ) hab (by omega)` as an intermediate fact. Simplify using `only [aPlusQ, centred]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma aPlusQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < pS D i τ) : aPlusQ D i τ b ≤ aPlusQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) hab (by omega)
  simp only [aPlusQ, centred]
  linarith

/- English proof (translation)
Establish `h` using `pq_eq D i τ`. Use `lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)` as an intermediate fact. Simplify using `only [dRowQ, centred]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma dRowQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < qS D i τ) : dRowQ D i τ b ≤ dRowQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)
  simp only [dRowQ, centred]
  push_cast at this
  linarith

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, pS D i τ = n + 1` from `⟨pS D i τ - 1, by omega⟩`. Use `le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))` and prove the remaining obligations. Establish `h1` using `lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)`. Establish `g` using `(D.hc τ).gap_be i`. Establish `hn' : (pS D i τ : ℚ) = n + 1` using `by exact_mod_cast hn`.

Simplify using `only [aPlusQ, centred, eS, h1, hn']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_aPlusQ {a : ℕ} (ha : a < pS D i τ) : 1 ≤ aPlusQ D i τ a := by
  obtain ⟨n, hn⟩ : ∃ n, pS D i τ = n + 1 := ⟨pS D i τ - 1, by omega⟩
  refine le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))
  have h1 := lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)
  have g := (D.hc τ).gap_be i
  have hn' : (pS D i τ : ℚ) = n + 1 := by exact_mod_cast hn
  simp only [aPlusQ, centred, eS, h1, hn']
  linarith

/- English proof (translation)
Take `⟨hp, hq⟩` from `sig_eq D i τ`. Establish `h0` using `dRowQ_anti D i τ (Nat.zero_le c) hc`. Establish `hi : (i : ℕ) + 1 < D.R.m` using `by omega`. Establish `h1` using `lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)`. Establish `g` using `(D.hc τ).gap_eb i hi`.

Establish `: dRowQ D i τ 0 ≤ -1`. Simplify using `only [dRowQ, centred, eS, h1]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_neg_dRowQ {c : ℕ} (hc : c < qS D i τ) : 1 ≤ -dRowQ D i τ c := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have h0 := dRowQ_anti D i τ (Nat.zero_le c) hc
  have hi : (i : ℕ) + 1 < D.R.m := by omega
  have h1 := lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)
  have g := (D.hc τ).gap_eb i hi
  have : dRowQ D i τ 0 ≤ -1 := by
    simp only [dRowQ, centred, eS, h1]
    push_cast
    linarith
  linarith

/- English proof (translation)
Unfold `aP aPl`. Rewrite using `[if_pos ha]`. Conclude with `toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))`.
-/
lemma cast_aPlus {a : ℕ} (ha : a < pS D i τ) : (aP D i τ a : ℚ) = aPlusQ D i τ a := by
  unfold aP aPl
  rw [if_pos ha]
  exact toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))

/- English proof (translation)
Unfold `aM aMi`. Establish `e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1` using `by omega`. Rewrite using `[if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]`. Establish `e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) = -dRowQ D i τ c`. Simplify using `only [dRowQ, centred, eS]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))`.
-/
lemma aM_cast {c : ℕ} (hc : c < qS D i τ) : (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c := by
  unfold aM aMi
  have e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1 := by omega
  rw [if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]
  have e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)
      = -dRowQ D i τ c := by
    simp only [dRowQ, centred, eS]; push_cast; ring
  rw [e2]
  exact toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))

/- English proof (translation)
Rewrite using `[← aM_cast D i τ (by omega)]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
lemma aM_cast' {a : ℕ} (ha : a < qS D i τ) : (aM D i τ a : ℚ) = -dRowQ D i τ (qS D i τ - 1 - a) := by
  rw [← aM_cast D i τ (by omega)]
  congr 2
  omega

/- English proof (translation)
Take `⟨hk, -, -, -, -, hv, hb⟩` from `hw`. Establish `hk3` using `D.R.m_add_three_le_k`. Unfold `Ranks.r at ha`. Unfold `IndefiniteWeightData.WeightData.lam`. Rewrite using `[hk]`.

Distinguish the cases in `h : a < D.R.k - 1`. Rewrite using `[if_pos (by omega)]`. Unfold `lamAt`. Rewrite using `[dif_pos h]`. Conclude with `hv ⟨a, h⟩`.

Rewrite using `[if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega), ← hb, Int.cast_neg]`. Use `congr 3`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
lemma lam_eq {w : IndefiniteWeightData.WeightData} (hw : IsDataOf D i τ w) {a : ℕ} (ha : a < D.R.r) :
    (w.lam (a + 1) : ℚ) = lamAt (D.hc τ) a := by
  obtain ⟨hk, -, -, -, -, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold IndefiniteWeightData.WeightData.lam
  rw [hk]
  by_cases h : a < D.R.k - 1
  · rw [if_pos (by omega)]
    unfold lamAt
    rw [dif_pos h]
    exact hv ⟨a, h⟩
  · rw [if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega),
      ← hb, Int.cast_neg]
    congr 3
    simp only; omega

/- English proof (translation)
Take `⟨hp, hq⟩` from `sig_eq D i τ`. Establish `hr` using `pq_eq D i τ`. Establish `hl` using `fun a ha => lam_eq D i τ (a := a) hw ha`. Take `⟨hk, hm, ht, hj, he, hv, hb⟩` from `hw`. Establish `hk3` using `D.R.m_add_three_le_k`.

Establish `wp : w.p = pS D i τ` using `by unfold IndefiniteWeightData.WeightData.p; omega`. Establish `wq : w.q = qS D i τ` using `by unfold IndefiniteWeightData.WeightData.q; omega`. Establish `wn : w.nV = pS D i τ + qS D i τ + D.R.t`. Unfold `IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r`. Unfold `Ranks.r at hr`.

Use linear arithmetic over natural numbers and integers. Unfold `IndefiniteWeightData.WeightData.lamPrime`. Use `congr 1`. Unfold `IndefiniteWeightData.WeightData.thetaWt thetaWt`. Rewrite using `[wp, wq, ht]`.

Distinguish the cases in `h1 : a < pS D i τ`. Rewrite using `[if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]`. Unfold `IndefiniteWeightData.WeightData.aPlus`. Rewrite using `[hl a (by omega), wn, wp, wq, he]`. Simplify using `only [aPlusQ, centred]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (by omega), if_neg h1]`. Distinguish the cases in `h2 : a < pS D i τ + D.R.t`. Rewrite using `[if_pos (by omega), if_pos h2]; simp`.

Rewrite using `[if_neg (by omega), if_neg h2]`. Take `⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c` from `⟨a - (pS D i τ + D.R.t), by omega⟩`. Establish `hc : c < qS D i τ` using `by omega`. Rewrite using `[Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]`. Unfold `IndefiniteWeightData.WeightData.aMinus`.

Establish `e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1`. Use linear arithmetic over natural numbers and integers. Establish `hi : (i : ℕ) + c + 1 < D.R.m` using `by omega`. Establish `e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩`. Rewrite using `[← hb]`.

Use `congr 2`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2, he, ht]`. Simplify using `only [dRowQ, centred]`.

Rewrite using `[lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `IndefiniteWeightData.WeightData.dTau dShift`. Rewrite using `[wp, wq, he]`.
-/
lemma lamPrime_eq (w : IndefiniteWeightData.WeightData) (hw : IsDataOf D i τ w) (a : ℕ) (ha : a < D.R.r + D.R.t) :
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have hr := pq_eq D i τ
  have hl := fun a ha => lam_eq D i τ (a := a) hw ha
  obtain ⟨hk, hm, ht, hj, he, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  have wp : w.p = pS D i τ := by unfold IndefiniteWeightData.WeightData.p; omega
  have wq : w.q = qS D i τ := by unfold IndefiniteWeightData.WeightData.q; omega
  have wn : w.nV = pS D i τ + qS D i τ + D.R.t := by
    unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; unfold Ranks.r at hr; omega
  unfold IndefiniteWeightData.WeightData.lamPrime
  congr 1
  · unfold IndefiniteWeightData.WeightData.thetaWt thetaWt
    rw [wp, wq, ht]
    by_cases h1 : a < pS D i τ
    · rw [if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]
      unfold IndefiniteWeightData.WeightData.aPlus
      rw [hl a (by omega), wn, wp, wq, he]
      simp only [aPlusQ, centred]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : a < pS D i τ + D.R.t
      · rw [if_pos (by omega), if_pos h2]; simp
      · rw [if_neg (by omega), if_neg h2]
        obtain ⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
        have hc : c < qS D i τ := by omega
        rw [Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]
        unfold IndefiniteWeightData.WeightData.aMinus
        have e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1 := by
          omega
        have hi : (i : ℕ) + c + 1 < D.R.m := by omega
        have e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩ := by
          rw [← hb]; congr 2; simp only; omega
        rw [e1, e2, he, ht]
        simp only [dRowQ, centred]
        rw [lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]
        push_cast; ring
  · unfold IndefiniteWeightData.WeightData.dTau dShift
    rw [wp, wq, he]

/- English proof (translation)
Introduce `D i τ`. Establish `hr` using `pq_eq D i τ`. Establish `hV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ)` using `by exact_mod_cast hr.symm`. Establish `ho : Odd (pS D i τ + qS D i τ)` using `hr ▸ odd_r D.R`.

Establish `hL` using `GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ`. Use `⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc, fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_, lamPrime_eq D i τ, hL, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]`. Conclude with `aPlusQ_anti D i τ hab hb`. Rewrite using `[← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]`.

Conclude with `dRowQ_anti D i τ (by omega) (by omega)`. Rewrite using `[← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]`. Conclude with `one_le_aPlusQ D i τ ha`. Rewrite using `[← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]`. Conclude with `one_le_neg_dRowQ D i τ (by omega)`.

Rewrite using `[kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]`. Simplify using `only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[kapW_cast _ _ _ ho, aM_cast D i τ c.2]`. Simplify using `only [kapQ, Sum.elim_inr, dRowQ, centred, hr']`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs⟩` from `ho`. Establish `hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ`. Establish `: (pS D i τ : ℚ) + qS D i τ = 2 * s + 1` using `by exact_mod_cast hs`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨e, he⟩` from `(D.hc τ).e_int i`. Use `⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩` and prove the remaining obligations. Simplify using `only [dShift, eS, he, hs']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩` from `hL`. Rewrite using `[hw a]`. Conclude with `lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)`.
-/
theorem arithAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ := by
  intro D i τ
  have hr := pq_eq D i τ
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast hr.symm
  have ho : Odd (pS D i τ + qS D i τ) := hr ▸ odd_r D.R
  have hL := GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ
  refine ⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc,
    fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_,
    lamPrime_eq D i τ, hL, fun a => ?_⟩
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]
    exact aPlusQ_anti D i τ hab hb
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]
    exact dRowQ_anti D i τ (by omega) (by omega)
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]
    exact one_le_aPlusQ D i τ ha
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]
    exact one_le_neg_dRowQ D i τ (by omega)
  · rw [kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]
    simp only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']; ring
  · rw [kapW_cast _ _ _ ho, aM_cast D i τ c.2]
    simp only [kapQ, Sum.elim_inr, dRowQ, centred, hr']; ring
  · obtain ⟨s, hs⟩ := ho
    have hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ := by
      have : (pS D i τ : ℚ) + qS D i τ = 2 * s + 1 := by exact_mod_cast hs
      linarith
    obtain ⟨e, he⟩ := (D.hc τ).e_int i
    refine ⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩
    simp only [dShift, eS, he, hs']
    push_cast; ring
  · obtain ⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩ := hL
    rw [hw a]
    exact lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)

end GlobalTheory.PairWeightArith
