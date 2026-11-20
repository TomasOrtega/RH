import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaRoot
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

/- English proof (translation)
Use `show ‖T.coeff (T.ptElt hc : Γ) 0‖ = ‖c‖`. Rewrite using `[coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg]`.
-/
theorem ptRad_ptElt {c : L} (hc : ‖c‖ ≤ 1) : T.ptRad (T.ptElt hc) = ‖c‖ := by
  show ‖T.coeff (T.ptElt hc : Γ) 0‖ = ‖c‖
  rw [coeff_zero, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg]

/- English proof (translation)
Use `set hξ := T.isPrimOne_ptElt hc0 hc1`. Establish `h0` using `T.ptE_ξ hξ`. Rewrite `h0` using `[coe_ptElt, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_π _) (T.convergesAt_zcoeff_neg (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ) (T.convergesAt_teich c _)), T.ptE_neg hξ (T.convergesAt_teich c _), ptE_π, ptE_teich]`. Conclude with `add_neg_eq_zero.1 h0`.
-/
theorem ptPi_ptElt {c : L} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    T.ptPi (T.isPrimOne_ptElt hc0 hc1) = T.ptSharp (T.isPrimOne_ptElt hc0 hc1) c := by
  set hξ := T.isPrimOne_ptElt hc0 hc1
  have h0 := T.ptE_ξ hξ
  rw [coe_ptElt, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_π _)
    (T.convergesAt_zcoeff_neg (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ) (T.convergesAt_teich c _)),
    T.ptE_neg hξ (T.convergesAt_teich c _), ptE_π, ptE_teich] at h0
  exact add_neg_eq_zero.1 h0

/- English proof (translation)
Use `squeeze_zero (fun n => by positivity) (fun n => ?_) ha` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le`.
-/
theorem convergesAt_of_norm_le_seq {a a' : ℤ → L} {ρ : ℝ} (ha : ConvergesAt a ρ)
    (h : ∀ n, ‖a' n‖ ≤ ‖a n‖) (hρ : 0 < ρ) : ConvergesAt a' ρ := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) ha
  exact mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1}

/- English proof (translation)
Use `set rr : Set.Ioc (0 : ℝ) ρ0 := ⟨r, h.1, h.2.le⟩`. Use `set b := T.approx hx h`. Establish `hb : T.extNorm ρ0 rr (x - b) < T.extNorm ρ0 rr x` using `T.approx_spec hx h rr le_rfl (mid_rad h).2.2.le`. Use `set N := T.extNorm ρ0 rr x with hNdef`. Establish `hNpos : 0 < N` using `T.extNorm_pos hx rr`.

Use `set a : ℤ → L := T.coeffB b with hadef`. Establish `ha : ConvergesAt a r` using `T.convergesAt_rad ρ0 b rr`. Establish `hgn : Laurent.gaussNorm a r = N`. Establish `e1` using `T.extNorm_eq_of_lt hb`. Rewrite `e1` using `[extNorm_coe]`.

Conclude with `e1`. Establish `ha0 : a ≠ 0`. Introduce `h0`. Rewrite `hgn` using `[h0]`. Simplify using `[Laurent.gaussNorm] at hgn`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set lo := lowIndex a r`. Use `set hi := highIndex a r`. Establish `hlo` using `T.lowIdx_eq_approx hx h`. Establish `hhi` using `T.highIdx_eq_approx hx h`.

Establish `hmult : T.mult x r = hi - lo` using `by rw [mult, hlo, hhi]`. Establish `hwlo : ‖a lo‖ * r ^ lo = N`. Use `lowIndex_mem h.1 ha ha0` as an intermediate fact. Simplify using `only [domSet, Set.mem_setOf_eq] at this`. Rewrite using `[this, hgn]`.

Establish `hwhi : ‖a hi‖ * r ^ hi = N`. Use `highIndex_mem h.1 ha ha0` as an intermediate fact. Simplify using `only [domSet, Set.mem_setOf_eq] at this`. Rewrite using `[this, hgn]`. Establish `hwle : ∀ n, ‖a n‖ * r ^ n ≤ N` using `fun n => hgn ▸ ha.le_gaussNorm n`.

Use `set m : ℕ := (hi - lo).toNat`. Establish `hm' : (m : ℤ) = hi - lo` using `Int.toNat_of_nonneg (by omega)`. Establish `hm1 : 1 ≤ m` using `by omega`. Establish `hhi' : hi = lo + m` using `by omega`. Use `set P : Polynomial L := ∑ i ∈ Finset.range (m + 1), Polynomial.C (a (lo + i)) * Polynomial.X ^ i with hPdef`.

Establish `hcoeff : ∀ k, P.coeff k = if k < m + 1 then a (lo + k) else 0` using `fun k => by`. Rewrite using `[hPdef, Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq (Finset.range (m + 1)) k (fun i => a (lo + i))]`. Simplify using `[Finset.mem_range]`.

Establish `hlo0 : a lo ≠ 0`. Introduce `h0`. Rewrite `hwlo` using `[h0, norm_zero, zero_mul]`. Conclude with `hNpos.ne hwlo`. Establish `hhi0 : a hi ≠ 0`.

Introduce `h0`. Rewrite `hwhi` using `[h0, norm_zero, zero_mul]`. Conclude with `hNpos.ne hwhi`. Establish `hdeg : P.natDegree = m`. Use `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff, if_pos (by omega), ← hhi']; exact hhi0)` and prove the remaining obligations.

Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi' => ?_` and prove the remaining obligations. Use `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hP0 : P.coeff 0 ≠ 0` using `by rw [hcoeff, if_pos (by omega)]; simpa using hlo0`.

Take `⟨c, hroot, hcj⟩` from `exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < P.natDegree) hP0`. Establish `hcoeff0 : P.coeff 0 = a lo` using `by rw [hcoeff, if_pos (by omega)]; simp`. Establish `hrel : ‖a lo‖ = ‖a hi‖ * r ^ m`. Establish `e1 : r ^ hi = r ^ lo * r ^ m`. Rewrite using `[hhi', zpow_add₀ h.1.ne', zpow_natCast]`.

Use `hwlo.trans hwhi.symm` as an intermediate fact. Rewrite `this` using `[e1]`. Establish `hlp` using `zpow_pos h.1 lo`. Clear denominators, using `at this` for the nonvanishing conditions. Use polynomial arithmetic with `[this]`.

Establish `hcle : ‖c‖ ≤ r`. Use `hcj m` as an intermediate fact. Rewrite `this` using `[hcoeff, if_pos (by omega), ← hhi', hcoeff0, hrel]`. Establish `hn : 0 < ‖a hi‖` using `norm_pos_iff.2 hhi0`. Establish `: ‖c‖ ^ m ≤ r ^ m` using `by nlinarith`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) h.1.le (by omega)).1 this`. Establish `hcge : r ≤ ‖c‖`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hbound : ∀ i ∈ Finset.range m, ‖a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖`.

Introduce `i _`. Rewrite using `[norm_mul, norm_pow]`. Establish `hw` using `hwle (lo + (i + 1))`. Rewrite `hw` using `[← hwlo, zpow_add₀ h.1.ne']`. Establish `hz : r ^ ((i : ℤ) + 1) = r ^ (i + 1)` using `by rw [← zpow_natCast]; push_cast; rfl`.

Rewrite `hw` using `[hz]`. Establish `hlp` using `zpow_pos h.1 lo`. Establish `h1 : ‖a (lo + (i + 1))‖ * r ^ (i + 1) ≤ ‖a lo‖`. Establish `: (‖a (lo + (i + 1))‖ * r ^ (i + 1)) * r ^ lo ≤ ‖a lo‖ * r ^ lo` using `by nlinarith`. Conclude with `le_of_mul_le_mul_right this hlp`.

Establish `hcpow : ‖c‖ ^ (i + 1) < r ^ (i + 1)` using `pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega)`. Break down `(norm_nonneg (a (lo + (i + 1)))).lt_or_eq with hpos | heq` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← heq, zero_mul]`. Conclude with `norm_pos_iff.2 hlo0`.

Take `⟨i0, hi0mem, hi0max⟩` from `(Finset.range m).exists_max_image (fun i => ‖a (lo + (i + 1)) * c ^ (i + 1)‖) ⟨0, Finset.mem_range.2 (by omega)⟩`. Establish `hrest : ‖∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖` using `(norm_finset_sum_le_ultra _ _ (norm_nonneg _) fun i hi' => hi0max i hi').trans_lt (hbound i0 hi0mem)`. Establish `hPc : P.eval c = a lo + ∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)`. Rewrite using `[hPdef, Polynomial.eval_finset_sum, Finset.sum_range_succ']`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_zero, mul_one, Nat.cast_zero, add_zero]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: P.eval c ≠ 0`. Rewrite using `[hPc]`. Introduce `h0`.

Use `ultra_norm_sub_eq_left (a := a lo) (b := -∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)) (by rw [norm_neg]; exact hrest)` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, h0, norm_zero]`. Conclude with `hlo0 (norm_eq_zero.1 this.symm)`. Conclude with `this hroot`. Establish `hcr : ‖c‖ = r` using `le_antisymm hcle hcge`.

Establish `hc0 : c ≠ 0` using `by intro h0; rw [h0, norm_zero] at hcr; exact h.1.ne hcr`. Establish `hc1 : ‖c‖ < 1` using `hcr ▸ (h.2.trans ρ0.2.2)`. Establish `hrad : T.ptRad (T.ptElt hc1.le) = r` using `(T.ptRad_ptElt hc1.le).trans hcr`. Use `⟨c, hc0, hc1, hrad, ?_⟩` and prove the remaining obligations. Use `set hξ0 := T.isPrimOne_ptElt hc0 hc1`.

Use `set hr0 := hrad.trans_le h.2.le`. Establish `hIoc : T.ptRadIoc hξ0 hr0 = rr` using `Subtype.ext hrad`. Establish `har : ConvergesAt a (T.ptRad (T.ptElt hc1.le))` using `by rw [hrad]; exact ha`. Establish `hvb : T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0) = T.ptEvalSeq hξ0 a`. Rewrite using `[ptEval_coe]`.

Both sides reduce to the same expression. Establish `hterm : ∀ n, T.ptTerm hξ0 a n = T.ptSharp hξ0 (c ^ n * a n)`. Introduce `n`. Rewrite using `[ptTerm, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]`. Use `set S : Finset ℤ := (Finset.range (m + 1)).image (fun i : ℕ => lo + i)`.

Establish `hSmem : ∀ n, n ∈ S ↔ lo ≤ n ∧ n ≤ hi`. Introduce `n`. Simplify using `only [S, Finset.mem_image, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi', rfl⟩`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h1, h2⟩; exact ⟨(n - lo).toNat, by omega, by omega⟩`. Use `set ablock : ℤ → L := fun n => if n ∈ S then a n else 0`. Use `set arest : ℤ → L := fun n => if n ∈ S then 0 else a n`. Apply the tactic sequence `have hcb : ConvergesAt ablock (T.ptRad (T.ptElt hc1.le)) := convergesAt_of_norm_le_seq har (fun n => by simp only [ablock]; split_ifs <;> simp) (T.ptRad_pos' hξ0)`.

Apply the tactic sequence `have hcr' : ConvergesAt arest (T.ptRad (T.ptElt hc1.le)) := convergesAt_of_norm_le_seq har (fun n => by simp only [arest]; split_ifs <;> simp) (T.ptRad_pos' hξ0)`. Establish `hsplit : T.ptEvalSeq hξ0 a = T.ptEvalSeq hξ0 ablock + T.ptEvalSeq hξ0 arest`. Rewrite using `[ptEvalSeq, ptEvalSeq, ptEvalSeq, ← (T.summable_ptTerm hξ0 hcb).tsum_add (T.summable_ptTerm hξ0 hcr')]`. Use `congr 1`. Use function extensionality and compare the values at `n`.

Simplify using `only [ptTerm, ablock, arest]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hblock : T.ptEvalSeq hξ0 ablock = ∑ i ∈ Finset.range (m + 1), T.ptSharp hξ0 (c ^ (lo + i) * a (lo + i))`. Rewrite using `[ptEvalSeq, tsum_eq_sum (s := S) (fun n hn => by simp [ptTerm, ablock, hn]), Finset.sum_image (fun i _ j _ hij => by simpa using hij)]`. Use `Finset.sum_congr rfl fun i hi' => ?_` and prove the remaining obligations.

Establish `hin : lo + (i : ℤ) ∈ S` using `Finset.mem_image_of_mem _ hi'`. Simplify using `only [ptTerm, ablock, if_pos hin, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]`. Establish `hsum0 : ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = 0`. Establish `hev : P.eval c = ∑ i ∈ Finset.range (m + 1), a (lo + i) * c ^ i`. Rewrite using `[hPdef, Polynomial.eval_finset_sum]`.

Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Establish `: ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = c ^ lo * P.eval c`. Rewrite using `[hev, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_add₀ hc0, zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hroot.eq_zero, mul_zero]`. Establish `hA : ‖T.ptEvalSeq hξ0 ablock‖ ≤ r * N`. Rewrite using `[hblock]`. Use `T.norm_sum_sharp_sub_le hξ0 (Finset.range (m + 1)) (fun i => c ^ (lo + i) * a (lo + i)) hNpos.le fun i _ => by` as an intermediate fact.

Rewrite using `[norm_mul, norm_zpow, hcr, mul_comm]`. Conclude with `hwle _`. Rewrite `this` using `[hsum0, map_zero, sub_zero, hrad]`. Then use the resulting hypothesis. Establish `hB : ‖T.ptEvalSeq hξ0 arest‖ < N`. Use `(T.norm_ptEvalSeq_le hξ0 hcr').trans_lt ?_` and prove the remaining obligations.

Rewrite using `[hrad]`. Distinguish the cases in `h0 : arest = 0`. Rewrite using `[h0]`. Simplify using `[Laurent.gaussNorm]`. Conclude with `hNpos`.

Establish `hcr'' : ConvergesAt arest r` using `hrad ▸ hcr'`. Establish `hmem` using `lowIndex_mem h.1 hcr'' h0`. Establish `hne` using `ne_zero_of_mem_domSet h.1 hcr'' h0 hmem`. Simplify using `only [domSet, Set.mem_setOf_eq] at hmem`. Rewrite using `[← hmem]`.

Use `set n1 := lowIndex arest r`. Establish `hn1S : n1 ∉ S`. Introduce `hS`. Apply `hne` to reduce the goal to its premises. Simplify using `[arest, hS]`.

Establish `hn1 : arest n1 = a n1` using `by simp [arest, hn1S]`. Rewrite using `[hn1, ← hgn]`. Rewrite `hn1S` using `[hSmem]`. Break down `(not_and_or.1 hn1S) with h1 | h1` into its components or cases. Conclude with `weight_lt_of_lt_lowIndex h.1 ha ha0 (by omega)`.

Conclude with `weight_lt_of_highIndex_lt h.1 ha ha0 (by omega)`. Establish `hbval : ‖T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0)‖ < N`. Rewrite using `[hvb, hsplit]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hB)` and prove the remaining obligations. Conclude with `hA.trans_lt (by nlinarith [h.2.trans ρ0.2.2])`.

Establish `hxb : ‖T.ptEval hξ0 hr0 (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0))‖ < N`. Use `(T.norm_ptEval_le hξ0 hr0 _).trans_lt ?_` and prove the remaining obligations. Rewrite using `[hIoc]`. Conclude with `hb`. Establish `e : x = ((b : T.Econ ρ0) : T.RobbaExt ρ0) + (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0))` using `by ring`.

Rewrite using `[e, map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hbval hxb)`.
-/
theorem exists_start_point {x : T.RobbaExt ρ0} (hx : x ≠ 0) {r : ℝ} (h : 0 < r ∧ r < ρ0)
    (hm : 1 ≤ T.mult x r) :
    ∃ (c : L) (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) (hrad : T.ptRad (T.ptElt hc1.le) = r),
      ‖T.ptEval (T.isPrimOne_ptElt hc0 hc1) (hrad.trans_le h.2.le) x‖ <
        T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x := by
  classical
  set rr : Set.Ioc (0 : ℝ) ρ0 := ⟨r, h.1, h.2.le⟩
  set b := T.approx hx h
  have hb : T.extNorm ρ0 rr (x - b) < T.extNorm ρ0 rr x :=
    T.approx_spec hx h rr le_rfl (mid_rad h).2.2.le
  set N := T.extNorm ρ0 rr x with hNdef
  have hNpos : 0 < N := T.extNorm_pos hx rr
  set a : ℤ → L := T.coeffB b with hadef
  have ha : ConvergesAt a r := T.convergesAt_rad ρ0 b rr
  have hgn : Laurent.gaussNorm a r = N := by
    have e1 := T.extNorm_eq_of_lt hb
    rw [extNorm_coe] at e1
    exact e1
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0] at hgn; simp [Laurent.gaussNorm] at hgn; linarith
  set lo := lowIndex a r
  set hi := highIndex a r
  have hlo := T.lowIdx_eq_approx hx h
  have hhi := T.highIdx_eq_approx hx h
  have hmult : T.mult x r = hi - lo := by rw [mult, hlo, hhi]
  have hwlo : ‖a lo‖ * r ^ lo = N := by
    have := lowIndex_mem h.1 ha ha0; simp only [domSet, Set.mem_setOf_eq] at this; rw [this, hgn]
  have hwhi : ‖a hi‖ * r ^ hi = N := by
    have := highIndex_mem h.1 ha ha0; simp only [domSet, Set.mem_setOf_eq] at this; rw [this, hgn]
  have hwle : ∀ n, ‖a n‖ * r ^ n ≤ N := fun n => hgn ▸ ha.le_gaussNorm n
  set m : ℕ := (hi - lo).toNat
  have hm' : (m : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  have hhi' : hi = lo + m := by omega

  set P : Polynomial L := ∑ i ∈ Finset.range (m + 1), Polynomial.C (a (lo + i)) * Polynomial.X ^ i
    with hPdef
  have hcoeff : ∀ k, P.coeff k = if k < m + 1 then a (lo + k) else 0 := fun k => by
    rw [hPdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (m + 1)) k (fun i => a (lo + i))]
    simp [Finset.mem_range]
  have hlo0 : a lo ≠ 0 := by
    intro h0; rw [h0, norm_zero, zero_mul] at hwlo; exact hNpos.ne hwlo
  have hhi0 : a hi ≠ 0 := by
    intro h0; rw [h0, norm_zero, zero_mul] at hwhi; exact hNpos.ne hwhi
  have hdeg : P.natDegree = m := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_
      (by rw [hcoeff, if_pos (by omega), ← hhi']; exact hhi0)
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi' => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.1 hi'; omega
  have hP0 : P.coeff 0 ≠ 0 := by rw [hcoeff, if_pos (by omega)]; simpa using hlo0
  obtain ⟨c, hroot, hcj⟩ := exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < P.natDegree) hP0
  have hcoeff0 : P.coeff 0 = a lo := by rw [hcoeff, if_pos (by omega)]; simp
  have hrel : ‖a lo‖ = ‖a hi‖ * r ^ m := by
    have e1 : r ^ hi = r ^ lo * r ^ m := by
      rw [hhi', zpow_add₀ h.1.ne', zpow_natCast]
    have := hwlo.trans hwhi.symm
    rw [e1] at this
    have hlp := zpow_pos h.1 lo
    field_simp at this
    nlinarith [this]

  have hcle : ‖c‖ ≤ r := by
    have := hcj m
    rw [hcoeff, if_pos (by omega), ← hhi', hcoeff0, hrel] at this
    have hn : 0 < ‖a hi‖ := norm_pos_iff.2 hhi0
    have : ‖c‖ ^ m ≤ r ^ m := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h.1.le (by omega)).1 this
  have hcge : r ≤ ‖c‖ := by
    by_contra hlt
    push_neg at hlt
    have hbound : ∀ i ∈ Finset.range m, ‖a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖ := by
      intro i _
      rw [norm_mul, norm_pow]
      have hw := hwle (lo + (i + 1))
      rw [← hwlo, zpow_add₀ h.1.ne'] at hw
      have hz : r ^ ((i : ℤ) + 1) = r ^ (i + 1) := by rw [← zpow_natCast]; push_cast; rfl
      rw [hz] at hw
      have hlp := zpow_pos h.1 lo
      have h1 : ‖a (lo + (i + 1))‖ * r ^ (i + 1) ≤ ‖a lo‖ := by
        have : (‖a (lo + (i + 1))‖ * r ^ (i + 1)) * r ^ lo ≤ ‖a lo‖ * r ^ lo := by nlinarith
        exact le_of_mul_le_mul_right this hlp
      have hcpow : ‖c‖ ^ (i + 1) < r ^ (i + 1) :=
        pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega)
      rcases (norm_nonneg (a (lo + (i + 1)))).lt_or_eq with hpos | heq
      · calc ‖a (lo + (i + 1))‖ * ‖c‖ ^ (i + 1) < ‖a (lo + (i + 1))‖ * r ^ (i + 1) :=
              mul_lt_mul_of_pos_left hcpow hpos
          _ ≤ ‖a lo‖ := h1
      · rw [← heq, zero_mul]; exact norm_pos_iff.2 hlo0
    obtain ⟨i0, hi0mem, hi0max⟩ := (Finset.range m).exists_max_image
      (fun i => ‖a (lo + (i + 1)) * c ^ (i + 1)‖) ⟨0, Finset.mem_range.2 (by omega)⟩
    have hrest : ‖∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)‖ < ‖a lo‖ :=
      (norm_finset_sum_le_ultra _ _ (norm_nonneg _) fun i hi' => hi0max i hi').trans_lt
        (hbound i0 hi0mem)
    have hPc : P.eval c = a lo + ∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1) := by
      rw [hPdef, Polynomial.eval_finset_sum, Finset.sum_range_succ']
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        pow_zero, mul_one, Nat.cast_zero, add_zero]
      push_cast
      ring
    have : P.eval c ≠ 0 := by
      rw [hPc]
      intro h0
      have := ultra_norm_sub_eq_left (a := a lo)
        (b := -∑ i ∈ Finset.range m, a (lo + (i + 1)) * c ^ (i + 1)) (by rw [norm_neg]; exact hrest)
      rw [sub_neg_eq_add, h0, norm_zero] at this
      exact hlo0 (norm_eq_zero.1 this.symm)
    exact this hroot
  have hcr : ‖c‖ = r := le_antisymm hcle hcge
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hcr; exact h.1.ne hcr
  have hc1 : ‖c‖ < 1 := hcr ▸ (h.2.trans ρ0.2.2)
  have hrad : T.ptRad (T.ptElt hc1.le) = r := (T.ptRad_ptElt hc1.le).trans hcr
  refine ⟨c, hc0, hc1, hrad, ?_⟩
  set hξ0 := T.isPrimOne_ptElt hc0 hc1
  set hr0 := hrad.trans_le h.2.le
  have hIoc : T.ptRadIoc hξ0 hr0 = rr := Subtype.ext hrad
  have har : ConvergesAt a (T.ptRad (T.ptElt hc1.le)) := by rw [hrad]; exact ha
  have hvb : T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0) = T.ptEvalSeq hξ0 a := by
    rw [ptEval_coe]; rfl
  have hterm : ∀ n, T.ptTerm hξ0 a n = T.ptSharp hξ0 (c ^ n * a n) := by
    intro n; rw [ptTerm, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]
  set S : Finset ℤ := (Finset.range (m + 1)).image (fun i : ℕ => lo + i)
  have hSmem : ∀ n, n ∈ S ↔ lo ≤ n ∧ n ≤ hi := by
    intro n
    simp only [S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi', rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨(n - lo).toNat, by omega, by omega⟩
  set ablock : ℤ → L := fun n => if n ∈ S then a n else 0
  set arest : ℤ → L := fun n => if n ∈ S then 0 else a n
  have hcb : ConvergesAt ablock (T.ptRad (T.ptElt hc1.le)) :=
    convergesAt_of_norm_le_seq har (fun n => by simp only [ablock]; split_ifs <;> simp)
      (T.ptRad_pos' hξ0)
  have hcr' : ConvergesAt arest (T.ptRad (T.ptElt hc1.le)) :=
    convergesAt_of_norm_le_seq har (fun n => by simp only [arest]; split_ifs <;> simp)
      (T.ptRad_pos' hξ0)
  have hsplit : T.ptEvalSeq hξ0 a = T.ptEvalSeq hξ0 ablock + T.ptEvalSeq hξ0 arest := by
    rw [ptEvalSeq, ptEvalSeq, ptEvalSeq, ← (T.summable_ptTerm hξ0 hcb).tsum_add
      (T.summable_ptTerm hξ0 hcr')]
    congr 1
    funext n
    simp only [ptTerm, ablock, arest]
    split_ifs <;> simp
  have hblock : T.ptEvalSeq hξ0 ablock =
      ∑ i ∈ Finset.range (m + 1), T.ptSharp hξ0 (c ^ (lo + i) * a (lo + i)) := by
    rw [ptEvalSeq, tsum_eq_sum (s := S) (fun n hn => by simp [ptTerm, ablock, hn]),
      Finset.sum_image (fun i _ j _ hij => by simpa using hij)]
    refine Finset.sum_congr rfl fun i hi' => ?_
    have hin : lo + (i : ℤ) ∈ S := Finset.mem_image_of_mem _ hi'
    simp only [ptTerm, ablock, if_pos hin, T.ptPi_ptElt hc0 hc1, map_mul, map_zpow₀]
  have hsum0 : ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = 0 := by
    have hev : P.eval c = ∑ i ∈ Finset.range (m + 1), a (lo + i) * c ^ i := by
      rw [hPdef, Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have : ∑ i ∈ Finset.range (m + 1), c ^ (lo + i) * a (lo + i) = c ^ lo * P.eval c := by
      rw [hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zpow_add₀ hc0, zpow_natCast]; ring
    rw [this, hroot.eq_zero, mul_zero]
  have hA : ‖T.ptEvalSeq hξ0 ablock‖ ≤ r * N := by
    rw [hblock]
    have := T.norm_sum_sharp_sub_le hξ0 (Finset.range (m + 1))
      (fun i => c ^ (lo + i) * a (lo + i)) hNpos.le fun i _ => by
        rw [norm_mul, norm_zpow, hcr, mul_comm]; exact hwle _
    rwa [hsum0, map_zero, sub_zero, hrad] at this
  have hB : ‖T.ptEvalSeq hξ0 arest‖ < N := by
    refine (T.norm_ptEvalSeq_le hξ0 hcr').trans_lt ?_
    rw [hrad]
    by_cases h0 : arest = 0
    · rw [h0]; simp [Laurent.gaussNorm]; exact hNpos
    have hcr'' : ConvergesAt arest r := hrad ▸ hcr'
    have hmem := lowIndex_mem h.1 hcr'' h0
    have hne := ne_zero_of_mem_domSet h.1 hcr'' h0 hmem
    simp only [domSet, Set.mem_setOf_eq] at hmem
    rw [← hmem]
    set n1 := lowIndex arest r
    have hn1S : n1 ∉ S := by
      intro hS; apply hne; simp [arest, hS]
    have hn1 : arest n1 = a n1 := by simp [arest, hn1S]
    rw [hn1, ← hgn]
    rw [hSmem] at hn1S
    rcases (not_and_or.1 hn1S) with h1 | h1
    · exact weight_lt_of_lt_lowIndex h.1 ha ha0 (by omega)
    · exact weight_lt_of_highIndex_lt h.1 ha ha0 (by omega)
  have hbval : ‖T.ptEval hξ0 hr0 ((b : T.Econ ρ0) : T.RobbaExt ρ0)‖ < N := by
    rw [hvb, hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hB)
    exact hA.trans_lt (by nlinarith [h.2.trans ρ0.2.2])
  have hxb : ‖T.ptEval hξ0 hr0 (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0))‖ < N := by
    refine (T.norm_ptEval_le hξ0 hr0 _).trans_lt ?_
    rw [hIoc]; exact hb
  have e : x = ((b : T.Econ ρ0) : T.RobbaExt ρ0) + (x - ((b : T.Econ ρ0) : T.RobbaExt ρ0)) := by ring
  rw [e, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hbval hxb)

section Iterate

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} {r : ℝ}

omit [IsAlgClosed L] in
/- English proof (translation)
Rewrite using `[coe_movePt, T.teich_zero, sub_zero]`.
-/
theorem movePt_zero {ξ : T.int} (hξ : T.IsPrimOne ξ) (h0 : ‖(0 : L)‖ < T.ptRad ξ) :
    (T.movePt hξ h0 : Γ) = ξ := by
  rw [coe_movePt, T.teich_zero, sub_zero]

structure GoodPt (x : T.RobbaExt ρ0) (r : ℝ) (h : 0 < r ∧ r < ρ0) where

  η : T.int
  hη : T.IsPrimOne η
  hrad : T.ptRad η = r
  hlt : ‖T.ptEval hη (hrad.trans_le h.2.le) x‖ < T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x

variable (h : 0 < r ∧ r < ρ0)

/- English proof (translation)
Take `⟨η, hη, hrad, hlt⟩` from `P`. Substitute `hrad` using the available equality. Establish `hNpos : 0 < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x` using `T.extNorm_pos hx _`. Distinguish the cases in `hε : T.ptEval hη h.2.le x = 0`. Establish `h0 : ‖(0 : L)‖ < T.ptRad η` using `by rw [norm_zero]; exact T.ptRad_pos' hη`.

Establish `hη'` using `T.isPrimOne_movePt hη h0`. Establish `hrad' : T.ptRad (T.movePt hη h0) = T.ptRad η` using `T.ptRad_movePt hη h0`. Take `⟨y, hy⟩` from `(T.ptEval_eq_zero_iff hη h.2.le x).1 hε`. Establish `hval : T.ptEval hη' (hrad'.trans_le h.2.le) x = 0`. Rewrite using `[hy, map_mul, T.ptEval_ξExt_movePt hη h0, map_zero, zero_mul]`.

Establish `hJpart : ∃ J : ℕ, 1 ≤ J ∧ (J : ℤ) ≤ T.mult x (T.ptRad η) ∧ (‖(0 : L)‖ / T.ptRad η) ^ J ≤ ‖T.ptEval hη h.2.le x‖ / T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x`. Use `⟨1, le_rfl, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_zero, zero_div, zero_pow one_ne_zero]`. Conclude with `div_nonneg (norm_nonneg _) hNpos.le`. Establish `hlt' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x`.

Rewrite using `[hval, norm_zero]`. Conclude with `hNpos`. Establish `hle' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ ≤ ‖T.ptEval hη h.2.le x‖ * max (T.ptRad η) (‖(0 : L)‖ / T.ptRad η)`. Rewrite using `[hval, norm_zero]`. Conclude with `mul_nonneg (norm_nonneg _) (le_max_of_le_left h.1.le)`.

Use `⟨0, ⟨T.movePt hη h0, hη', hrad', hlt'⟩, ?_, by rw [norm_zero]; exact h.1, hJpart, hle'⟩` and prove the remaining obligations. Use `show (T.movePt hη h0 : Γ) = η - T.teich 0`. Rewrite using `[coe_movePt]`. Establish `hεN : ‖T.ptEval hη h.2.le x‖ < T.extNorm ρ0 (T.ptRadIoc hη h.2.le) x` using `hlt`. Take `⟨s, hs, J, hJ1, hJm, hratio, hnew⟩` from `T.step_estimate hη h.2 hx hε hεN`.

Establish `hrad' : T.ptRad (T.movePt hη hs) = T.ptRad η` using `T.ptRad_movePt hη hs`. Establish `hfac : max (T.ptRad η) (‖s‖ / T.ptRad η) < 1` using `max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 hs)`. Establish `hεpos : 0 < ‖T.ptEval hη h.2.le x‖` using `norm_pos_iff.2 hε`. Use `⟨s, ⟨T.movePt hη hs, T.isPrimOne_movePt hη hs, hrad', ?_⟩, rfl, hs, ⟨J, hJ1, hJm, hratio⟩, hnew⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_next (hx : x ≠ 0) (hm : 1 ≤ T.mult x r) (P : T.GoodPt x r h) :
    ∃ (s : L) (P' : T.GoodPt x r h), (P'.η : Γ) = P.η - T.teich s ∧ ‖s‖ < r ∧
      (∃ J : ℕ, 1 ≤ J ∧ (J : ℤ) ≤ T.mult x r ∧
        (‖s‖ / r) ^ J ≤ ‖T.ptEval P.hη (P.hrad.trans_le h.2.le) x‖ /
          T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x) ∧
      ‖T.ptEval P'.hη (P'.hrad.trans_le h.2.le) x‖ ≤
        ‖T.ptEval P.hη (P.hrad.trans_le h.2.le) x‖ * max r (‖s‖ / r) := by
  obtain ⟨η, hη, hrad, hlt⟩ := P
  subst hrad
  have hNpos : 0 < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := T.extNorm_pos hx _
  by_cases hε : T.ptEval hη h.2.le x = 0
  ·
    have h0 : ‖(0 : L)‖ < T.ptRad η := by rw [norm_zero]; exact T.ptRad_pos' hη
    have hη' := T.isPrimOne_movePt hη h0
    have hrad' : T.ptRad (T.movePt hη h0) = T.ptRad η := T.ptRad_movePt hη h0
    obtain ⟨y, hy⟩ := (T.ptEval_eq_zero_iff hη h.2.le x).1 hε
    have hval : T.ptEval hη' (hrad'.trans_le h.2.le) x = 0 := by
      rw [hy, map_mul, T.ptEval_ξExt_movePt hη h0, map_zero, zero_mul]
    have hJpart : ∃ J : ℕ, 1 ≤ J ∧ (J : ℤ) ≤ T.mult x (T.ptRad η) ∧
        (‖(0 : L)‖ / T.ptRad η) ^ J ≤ ‖T.ptEval hη h.2.le x‖ /
          T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := by
      refine ⟨1, le_rfl, hm, ?_⟩
      rw [norm_zero, zero_div, zero_pow one_ne_zero]
      exact div_nonneg (norm_nonneg _) hNpos.le
    have hlt' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ < T.extNorm ρ0 ⟨T.ptRad η, h.1, h.2.le⟩ x := by
      rw [hval, norm_zero]; exact hNpos
    have hle' : ‖T.ptEval hη' (hrad'.trans_le h.2.le) x‖ ≤
        ‖T.ptEval hη h.2.le x‖ * max (T.ptRad η) (‖(0 : L)‖ / T.ptRad η) := by
      rw [hval, norm_zero]
      exact mul_nonneg (norm_nonneg _) (le_max_of_le_left h.1.le)
    refine ⟨0, ⟨T.movePt hη h0, hη', hrad', hlt'⟩, ?_, by rw [norm_zero]; exact h.1, hJpart, hle'⟩
    show (T.movePt hη h0 : Γ) = η - T.teich 0
    rw [coe_movePt]
  · have hεN : ‖T.ptEval hη h.2.le x‖ < T.extNorm ρ0 (T.ptRadIoc hη h.2.le) x := hlt
    obtain ⟨s, hs, J, hJ1, hJm, hratio, hnew⟩ := T.step_estimate hη h.2 hx hε hεN
    have hrad' : T.ptRad (T.movePt hη hs) = T.ptRad η := T.ptRad_movePt hη hs
    have hfac : max (T.ptRad η) (‖s‖ / T.ptRad η) < 1 :=
      max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 hs)
    have hεpos : 0 < ‖T.ptEval hη h.2.le x‖ := norm_pos_iff.2 hε
    refine ⟨s, ⟨T.movePt hη hs, T.isPrimOne_movePt hη hs, hrad', ?_⟩, rfl, hs,
      ⟨J, hJ1, hJm, hratio⟩, hnew⟩
    calc ‖T.ptEval (T.isPrimOne_movePt hη hs) (hrad'.trans_le h.2.le) x‖
        ≤ ‖T.ptEval hη h.2.le x‖ * max (T.ptRad η) (‖s‖ / T.ptRad η) := hnew
      _ < ‖T.ptEval hη h.2.le x‖ * 1 := mul_lt_mul_of_pos_left hfac hεpos
      _ = _ := mul_one _
      _ < _ := hlt

end Iterate

section Limit

/- English proof (translation)
Establish `hr1` using `T.ptRad_lt_one' hξ`. Establish `hδ1 : δ < 1` using `hδ.trans hr1`. Establish `hrad : T.ptRad (ξ - Y) = T.ptRad ξ` using `by show ‖T.coeff ((ξ - Y : T.int) : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖`. Rewrite using `[show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl, coeff_zero, coeff_zero, map_sub]`. Use `ultra_norm_sub_eq_left ?_` and prove the remaining obligations.

Rewrite using `[← coeff_zero]`. Conclude with `(hY 0 (Nat.zero_le _)).trans_lt hδ`. Use `⟨⟨?_, ?_, ?_⟩, hrad⟩` and prove the remaining obligations. Introduce `h0`. Use `hrad` as an intermediate fact.

Rewrite `this` using `[ptRad, h0, norm_zero]`. Conclude with `(T.ptRad_pos' hξ).ne this`. Use `hrad` as an intermediate fact. Rewrite `this` using `[ptRad]`. Rewrite using `[this]`.

Conclude with `hr1`. Establish `hx : T.PrefixLe (ξ : Γ) 1 1` using `fun m _ => T.mem_int_iff.1 ξ.2 m`. Establish `hy : T.PrefixLe (-(Y : Γ)) 1 δ` using `T.prefixLe_neg hY`. Establish `hh` using `T.norm_coeff_add_sub_le 1 hδ0 hδ1.le hx hy 1 le_rfl`. Rewrite `hh` using `[Real.one_rpow, one_mul, ← sub_eq_add_neg]`.

Take `⟨ht0, -⟩` from `coeffHolderExp_pos_le_one (p := p) 1`. Establish `hlt : δ ^ coeffHolderExp p 1 < 1` using `Real.rpow_lt_one hδ0 hδ1 ht0`. Establish `e1 : ‖T.coeff (ξ : Γ) 1‖ = 1` using `hξ.norm_coeff_one`. Rewrite using `[show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl]`. Use `ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1) (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - Y) 1) (by` as an intermediate fact.

Rewrite using `[norm_sub_rev, e1]`. Conclude with `hh.trans_lt hlt)`. Rewrite `this` using `[sub_sub_cancel, e1]`. Conclude with `this`.
-/
theorem isPrimOne_sub_of_prefix {ξ : T.int} (hξ : T.IsPrimOne ξ) {Y : T.int} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < T.ptRad ξ) (hY : T.PrefixLe (Y : Γ) 1 δ) :
    T.IsPrimOne (ξ - Y) ∧ T.ptRad (ξ - Y) = T.ptRad ξ := by
  have hr1 := T.ptRad_lt_one' hξ
  have hδ1 : δ < 1 := hδ.trans hr1
  have hrad : T.ptRad (ξ - Y) = T.ptRad ξ := by
    show ‖T.coeff ((ξ - Y : T.int) : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖
    rw [show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl, coeff_zero, coeff_zero, map_sub]
    refine ultra_norm_sub_eq_left ?_
    rw [← coeff_zero]
    exact (hY 0 (Nat.zero_le _)).trans_lt hδ
  refine ⟨⟨?_, ?_, ?_⟩, hrad⟩
  · intro h0
    have := hrad
    rw [ptRad, h0, norm_zero] at this
    exact (T.ptRad_pos' hξ).ne this
  · have := hrad; rw [ptRad] at this; rw [this]; exact hr1
  · have hx : T.PrefixLe (ξ : Γ) 1 1 := fun m _ => T.mem_int_iff.1 ξ.2 m
    have hy : T.PrefixLe (-(Y : Γ)) 1 δ := T.prefixLe_neg hY
    have hh := T.norm_coeff_add_sub_le 1 hδ0 hδ1.le hx hy 1 le_rfl
    rw [Real.one_rpow, one_mul, ← sub_eq_add_neg] at hh
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) 1
    have hlt : δ ^ coeffHolderExp p 1 < 1 := Real.rpow_lt_one hδ0 hδ1 ht0
    have e1 : ‖T.coeff (ξ : Γ) 1‖ = 1 := hξ.norm_coeff_one
    rw [show ((ξ - Y : T.int) : Γ) = (ξ : Γ) - Y from rfl]
    have := ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1)
      (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - Y) 1) (by
        rw [norm_sub_rev, e1]; exact hh.trans_lt hlt)
    rw [sub_sub_cancel, e1] at this
    exact this

variable [IsAlgClosed L] [CompleteSpace L] {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} {r : ℝ}
  (h : 0 < r ∧ r < ρ0)

/- English proof (translation)
Use `choose sF PF hrel hsr hJ hdec using T.exists_next h hx hm`. Use `set pts : ℕ → T.GoodPt x r h := fun k => PF^[k] P0 with hpts`. Establish `hpts_succ : ∀ k, pts (k + 1) = PF (pts k)` using `fun k => Function.iterate_succ_apply' PF k P0`. Use `set s : ℕ → L := fun k => sF (pts k)`. Use `set N := T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x with hNdef`.

Establish `hNpos : 0 < N` using `T.extNorm_pos hx _`. Use `set ε : ℕ → ℝ := fun k => ‖T.ptEval (pts k).hη ((pts k).hrad.trans_le h.2.le) x‖`. Establish `hεnn : ∀ k, 0 ≤ ε k` using `fun k => norm_nonneg _`. Establish `hεN : ∀ k, ε k < N` using `fun k => (pts k).hlt`. Establish `hsr' : ∀ k, ‖s k‖ < r` using `fun k => hsr (pts k)`.

Establish `hdec' : ∀ k, ε (k + 1) ≤ ε k * max r (‖s k‖ / r)` using `fun k => by show ‖T.ptEval (pts (k + 1)).hη _ x‖ ≤ _`. Use `hdec (pts k)` as an intermediate fact. Rewrite `this` using `[← hpts_succ]`. Conclude with `this`. Establish `hmax : ∀ k, max r (‖s k‖ / r) < 1` using `fun k => max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 (hsr' k))`.

Establish `hεmono : ∀ k, ε (k + 1) ≤ ε k` using `fun k => (hdec' k).trans (mul_le_of_le_one_right (hεnn k) (hmax k).le)`. Establish `hεle0 : ∀ k, ε k ≤ ε 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact le_rfl`.

Consider the case `succ k ih => exact (hεmono k).trans ih`. Use `set M : ℕ := (T.mult x r).toNat`. Establish `hM : (M : ℤ) = T.mult x r` using `Int.toNat_of_nonneg (T.mult_nonneg x r)`. Establish `hM1 : 1 ≤ M` using `by omega`. Use `set q := ε 0 / N`.

Establish `hq0 : 0 ≤ q` using `div_nonneg (hεnn 0) hNpos.le`. Establish `hq1 : q < 1` using `(div_lt_one hNpos).2 (hεN 0)`. Take `⟨lam0, hl0, hl1, hql⟩ : ∃ l : ℝ, 0 < l ∧ l < 1 ∧ q < l ^ M` from `by set t := q ^ ((M : ℝ)⁻¹) with htdef`. Establish `ht0 : 0 ≤ t` using `Real.rpow_nonneg hq0 _`. Establish `ht1 : t < 1` using `Real.rpow_lt_one hq0 hq1 (inv_pos.2 (by exact_mod_cast hM1))`.

Use `⟨(t + 1) / 2, by linarith, by linarith, ?_⟩` and prove the remaining obligations. Establish `htM : t ^ M = q` using `Real.rpow_inv_natCast_pow hq0 (by omega)`. Rewrite using `[← htM]`. Conclude with `pow_lt_pow_left₀ (by linarith) ht0 (by omega)`. Establish `ht_le : ∀ k, ‖s k‖ / r ≤ lam0`.

Introduce `k`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨J, hJ1, hJM, hJr⟩` from `hJ (pts k)`. Establish `hJM' : J ≤ M` using `by omega`.

Establish `ht1 : ‖s k‖ / r ≤ 1` using `((div_lt_one h.1).2 (hsr' k)).le`. Establish `h1 : (‖s k‖ / r) ^ M ≤ (‖s k‖ / r) ^ J` using `pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) h.1.le) ht1 hJM'`. Establish `h2 : lam0 ^ M < (‖s k‖ / r) ^ M` using `pow_lt_pow_left₀ hcon hl0.le (by omega)`. Establish `h3 : ε k / N ≤ q` using `div_le_div_of_nonneg_right (hεle0 k) hNpos.le`. Use `hJr` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(‖s k‖ / r) ^ J ≤ ε k / N at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set lam := max r lam0`. Establish `hlam1 : lam < 1` using `max_lt (h.2.trans ρ0.2.2) hl1`. Establish `hlam0 : 0 ≤ lam` using `le_max_of_le_left h.1.le`.

Establish `hεgeom : ∀ k, ε k ≤ lam ^ k * ε 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Combine the equalities or inequalities in the displayed calculation. Use `set mu := lam ^ ((M : ℝ)⁻¹)`. Establish `hmu0 : 0 ≤ mu` using `Real.rpow_nonneg hlam0 _`. Establish `hmu1 : mu < 1` using `Real.rpow_lt_one hlam0 hlam1 (inv_pos.2 (by exact_mod_cast hM1))`. Establish `hmuM : mu ^ M = lam` using `Real.rpow_inv_natCast_pow hlam0 (by omega)`.

Establish `hs_geom : ∀ k, ‖s k‖ ≤ mu ^ k`. Introduce `k`. Take `⟨J, hJ1, hJM, hJr⟩` from `hJ (pts k)`. Establish `hJM' : J ≤ M` using `by omega`. Express the relevant statement in the definitionally equal form `(‖s k‖ / r) ^ J ≤ ε k / N at hJr`.

Establish `ht1 : ‖s k‖ / r ≤ 1` using `((div_lt_one h.1).2 (hsr' k)).le`. Establish `h1 : (‖s k‖ / r) ^ M ≤ lam ^ k`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖s k‖ / r ≤ mu ^ k`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Use `pow_lt_pow_left₀ hcon (pow_nonneg hmu0 k) (by omega : M ≠ 0)` as an intermediate fact. Rewrite `this` using `[← pow_mul, mul_comm, pow_mul, hmuM]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Use `set S : ℕ → Γ := fun k => ∑ i ∈ Finset.range k, T.teich (s i) with hSdef`. Establish `hs1 : ∀ k, ‖s k‖ ≤ 1` using `fun k => ((hsr' k).trans (h.2.trans ρ0.2.2)).le`. Establish `hSint : ∀ k, S k ∈ T.int` using `fun k => Subring.sum_mem _ fun i _ => T.teich_mem_int (hs1 i)`. Establish `hSsucc : ∀ k, S (k + 1) = S k + T.teich (s k)` using `fun k => by`. Simplify using `only [S, Finset.sum_range_succ]`.

Establish `hSpts : ∀ k, ((pts k).η : Γ) = P0.η - S k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [S, pts]`. Consider the case `succ k ih`.

Rewrite using `[hpts_succ, hrel (pts k), ih, hSsucc]`. Simplify using `only [s]`. Expand and normalize the polynomial expressions, which then agree. Establish `hstep : ∀ n k, ‖T.coeff (S (k + 1)) n - T.coeff (S k) n‖ ≤ (mu ^ coeffHolderExp p n) ^ k`. Introduce `n k`.

Establish `hxp : T.PrefixLe (S k) n 1` using `fun m _ => T.mem_int_iff.1 (hSint k) m`. Establish `hyp : T.PrefixLe (T.teich (s k)) n ‖s k‖` using `T.prefixLe_teich' (s k) n le_rfl`. Use `T.norm_coeff_add_sub_le n (norm_nonneg _) (hs1 k) hxp hyp n le_rfl` as an intermediate fact. Rewrite `this` using `[Real.one_rpow, one_mul]`. Rewrite using `[hSsucc]`.

Use `this.trans ?_` and prove the remaining obligations. Take `⟨ht0, -⟩` from `coeffHolderExp_pos_le_one (p := p) n`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hmu0, ← Real.rpow_mul hmu0, mul_comm]`. Establish `hcauchy : ∀ n, CauchySeq (fun k => T.coeff (S k) n)` using `fun n => by`.

Take `⟨ht0, -⟩` from `coeffHolderExp_pos_le_one (p := p) n`. Use `cauchySeq_of_le_geometric (mu ^ coeffHolderExp p n) 1 (Real.rpow_lt_one hmu0 hmu1 ht0) fun k => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, norm_sub_rev, one_mul]`. Conclude with `hstep n k`. Use `choose a ha using fun n => cauchySeq_tendsto_of_complete (hcauchy n)`.

Establish `ha1 : ∀ n, ‖a n‖ ≤ 1` using `fun n => le_of_tendsto ((continuous_norm.tendsto _).comp (ha n)) (Filter.Eventually.of_forall fun k => T.mem_int_iff.1 (hSint k) n)`. Use `set X := T.ofCoeff a with hXdef`. Establish `hXc : ∀ n, T.coeff X n = a n` using `fun n => by rw [hXdef, coeff_ofCoeff]`. Establish `hXint : X ∈ T.int` using `T.mem_int_iff.2 fun n => by rw [hXc]; exact ha1 n`. Use `set δ := r * lam0`.

Establish `hsδ : ∀ i, ‖s i‖ ≤ δ` using `fun i => by`. Use `ht_le i` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ h.1]`. Use `show ‖s i‖ ≤ r * lam0`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hδ0 : 0 ≤ δ` using `mul_nonneg h.1.le hl0.le`. Establish `hSpre : ∀ k, T.PrefixLe (S k) 1 δ` using `fun k => T.prefixLe_sum _ _ hδ0 fun i _ => T.prefixLe_teich' (s i) 1 (hsδ i)`. Establish `hXpre : T.PrefixLe X 1 δ` using `fun m hm => by`. Rewrite using `[hXc]`. Conclude with `le_of_tendsto ((continuous_norm.tendsto _).comp (ha m)) (Filter.Eventually.of_forall fun k => hSpre k m hm)`.

Establish `hδr : δ < T.ptRad P0.η`. Rewrite using `[P0.hrad]`. Use `show r * lam0 < r`. Use polynomial arithmetic with `[h.1]`. Take `⟨hξi, hradi'⟩` from `T.isPrimOne_sub_of_prefix P0.hη (Y := ⟨X, hXint⟩) hδ0 hδr hXpre`.

Use `set ξi : T.int := P0.η - ⟨X, hXint⟩ with hξidef`. Establish `hradi : T.ptRad ξi = r` using `hradi'.trans P0.hrad`. Establish `hri : T.ptRad ξi ≤ ρ0` using `hradi.trans_le h.2.le`. Establish `hIoci : T.ptRadIoc hξi hri = ⟨r, h.1, h.2.le⟩` using `Subtype.ext hradi`. Establish `hr1 : r < 1` using `h.2.trans ρ0.2.2`.

Establish `hDint : ∀ k, X - S k ∈ T.int` using `fun k => sub_mem hXint (hSint k)`. Use `set G : ℕ → ℝ := fun k => gaussNorm (T.zcoeff (X - S k)) r`. Establish `hG : Tendsto G atTop (𝓝 0)`. Rewrite using `[Metric.tendsto_atTop]`. Introduce `e he`.

Use `set e' := min e 1 / 2 with he'`. Establish `he'0 : 0 < e'` using `by positivity`. Establish `he'1 : e' < 1`. Use `min_le_right e 1` as an intermediate fact. Rewrite using `[he']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `he'e : e' < e`. Use `min_le_left e 1` as an intermediate fact. Rewrite using `[he']`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨n0, hn0⟩` from `exists_pow_lt_of_lt_one he'0 hr1`. Use `set tol := e' ^ (p ^ n0 : ℕ)`. Establish `htol0 : 0 < tol` using `by positivity`. Establish `htol1 : tol ≤ 1` using `pow_le_one₀ he'0.le he'1.le`. Establish `htole : tol ^ ((p ^ n0 : ℕ) : ℝ)⁻¹ = e'` using `Real.pow_rpow_inv_natCast he'0.le (pow_ne_zero _ hp.out.ne_zero)`.

Establish `hev : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (n0 + 1), ‖a i - T.coeff (S k) i‖ < tol`. Use `(Finset.eventually_all _).2 fun i _ => ?_` and prove the remaining obligations. Use `(ha i).eventually (Metric.ball_mem_nhds (a i) htol0)` as an intermediate fact. Use `filter_upwards [this] with k hk`. Rewrite `hk` using `[dist_eq_norm, norm_sub_rev]`.

Conclude with `hk`. Take `⟨K, hK⟩` from `Filter.eventually_atTop.1 hev`. Use `⟨K, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg h.1)]`. Establish `hpre` using `T.prefixLe_sub_of_coeff_close (u := X) (v := S k) (n := n0) htol0.le htol1 (fun i _ => by rw [hXc]; exact ha1 i) (fun i _ => T.mem_int_iff.1 (hSint k) i) (fun i hi => by rw [hXc]; exact (hK k hk i (Finset.mem_range.2 (by omega))).le)`.

Rewrite `hpre` using `[Real.one_rpow, one_mul, htole]`. Use `lt_of_le_of_lt (gaussNorm_le fun n => ?_) he'e` and prove the remaining obligations. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ hn, norm_zero, zero_mul]`. Conclude with `he'0.le`.

Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`. Rewrite using `[T.zcoeff_natCast, zpow_natCast]`. Distinguish the cases in `hmn : m ≤ n0`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : ‖T.coeff (X - S k) m‖ ≤ 1` using `T.mem_int_iff.1 (hDint k) m`.

Combine the equalities or inequalities in the displayed calculation. Establish `hbound : ∀ k, ‖T.ptEval hξi hri x‖ ≤ max (ε k) (G k * (N / r))`. Introduce `k`. Establish `hrk : T.ptRad (pts k).η ≤ ρ0` using `(pts k).hrad.trans_le h.2.le`. Use `set D := T.divStep (pts k).hη hrk x`.

Establish `h1 : ‖T.ptEval hξi hri (T.liftExt ρ0 D.z D.hV)‖ ≤ ε k`. Use `(T.norm_ptEval_le hξi hri _).trans ?_` and prove the remaining obligations. Rewrite using `[T.extNorm_liftExt _ _ D.hred, D.hz]`. Establish `h2 : ‖T.ptEval hξi hri (T.ξExt (pts k).η ρ0)‖ ≤ G k`. Rewrite using `[ξExt, T.ptEval_coe_algebraMap hξi hri]`.

Establish `hr0'` using `T.ptRad_pos' hξi`. Establish `hr1'` using `T.ptRad_lt_one' hξi`. Establish `hdiff : ((pts k).η : Γ) = (ξi : Γ) + (X - S k)`. Rewrite using `[hSpts k, hξidef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdiff, T.ptE_add hξi (T.convergesAt_of_mem_int ξi.2 hr0' hr1') (T.convergesAt_of_mem_int (hDint k) hr0' hr1'), T.ptE_ξ hξi, zero_add]`. Use `(T.norm_ptE_le hξi (T.convergesAt_of_mem_int (hDint k) hr0' hr1')).trans ?_` and prove the remaining obligations. Rewrite using `[hradi]`. Establish `h3 : ‖T.ptEval hξi hri D.next‖ ≤ N / r`.

Use `(T.norm_ptEval_le hξi hri _).trans ?_` and prove the remaining obligations. Rewrite using `[hIoci]`. Use `T.extNorm_next_le (hξ := (pts k).hη) (hr := hrk) x` as an intermediate fact. Establish `hIock : T.ptRadIoc (pts k).hη hrk = ⟨r, h.1, h.2.le⟩` using `Subtype.ext (pts k).hrad`. Rewrite `this` using `[hIock, (pts k).hrad]`.

Rewrite using `[le_div_iff₀ h.1, mul_comm]`. Conclude with `this`. Establish `e` using `D.eq`. Rewrite using `[e, map_add, map_mul]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul h2 h3 (norm_nonneg _) (gaussNorm_nonneg h.1)`. Establish `hεlim : Tendsto ε atTop (𝓝 0)`. Use `(tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (ε 0)` as an intermediate fact. Rewrite `this` using `[zero_mul]`.

Conclude with `squeeze_zero hεnn hεgeom this`. Establish `hmaxlim : Tendsto (fun k => max (ε k) (G k * (N / r))) atTop (𝓝 0)`. Use `hεlim.max (hG.mul_const (N / r))` as an intermediate fact. Rewrite `this` using `[zero_mul, max_self]`. Then use the resulting hypothesis. Establish `hz : ‖T.ptEval hξi hri x‖ = 0` using `le_antisymm (ge_of_tendsto' hmaxlim hbound) (norm_nonneg _)`.

Conclude with `⟨ξi, hξi, hradi, norm_eq_zero.1 hz⟩`.
-/
theorem exists_zero_of_goodPt (hx : x ≠ 0) (hm : 1 ≤ T.mult x r) (P0 : T.GoodPt x r h) :
    ∃ (η : T.int) (hη : T.IsPrimOne η) (hrad : T.ptRad η = r),
      T.ptEval hη (hrad.trans_le h.2.le) x = 0 := by
  classical
  choose sF PF hrel hsr hJ hdec using T.exists_next h hx hm
  set pts : ℕ → T.GoodPt x r h := fun k => PF^[k] P0 with hpts
  have hpts_succ : ∀ k, pts (k + 1) = PF (pts k) := fun k =>
    Function.iterate_succ_apply' PF k P0
  set s : ℕ → L := fun k => sF (pts k)
  set N := T.extNorm ρ0 ⟨r, h.1, h.2.le⟩ x with hNdef
  have hNpos : 0 < N := T.extNorm_pos hx _
  set ε : ℕ → ℝ := fun k => ‖T.ptEval (pts k).hη ((pts k).hrad.trans_le h.2.le) x‖
  have hεnn : ∀ k, 0 ≤ ε k := fun k => norm_nonneg _
  have hεN : ∀ k, ε k < N := fun k => (pts k).hlt
  have hsr' : ∀ k, ‖s k‖ < r := fun k => hsr (pts k)
  have hdec' : ∀ k, ε (k + 1) ≤ ε k * max r (‖s k‖ / r) := fun k => by
    show ‖T.ptEval (pts (k + 1)).hη _ x‖ ≤ _
    have := hdec (pts k)
    rw [← hpts_succ] at this
    exact this
  have hmax : ∀ k, max r (‖s k‖ / r) < 1 := fun k =>
    max_lt (h.2.trans ρ0.2.2) ((div_lt_one h.1).2 (hsr' k))
  have hεmono : ∀ k, ε (k + 1) ≤ ε k := fun k =>
    (hdec' k).trans (mul_le_of_le_one_right (hεnn k) (hmax k).le)
  have hεle0 : ∀ k, ε k ≤ ε 0 := by
    intro k; induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hεmono k).trans ih

  set M : ℕ := (T.mult x r).toNat
  have hM : (M : ℤ) = T.mult x r := Int.toNat_of_nonneg (T.mult_nonneg x r)
  have hM1 : 1 ≤ M := by omega
  set q := ε 0 / N
  have hq0 : 0 ≤ q := div_nonneg (hεnn 0) hNpos.le
  have hq1 : q < 1 := (div_lt_one hNpos).2 (hεN 0)
  obtain ⟨lam0, hl0, hl1, hql⟩ : ∃ l : ℝ, 0 < l ∧ l < 1 ∧ q < l ^ M := by
    set t := q ^ ((M : ℝ)⁻¹) with htdef
    have ht0 : 0 ≤ t := Real.rpow_nonneg hq0 _
    have ht1 : t < 1 := Real.rpow_lt_one hq0 hq1 (inv_pos.2 (by exact_mod_cast hM1))
    refine ⟨(t + 1) / 2, by linarith, by linarith, ?_⟩
    have htM : t ^ M = q := Real.rpow_inv_natCast_pow hq0 (by omega)
    rw [← htM]
    exact pow_lt_pow_left₀ (by linarith) ht0 (by omega)
  have ht_le : ∀ k, ‖s k‖ / r ≤ lam0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    obtain ⟨J, hJ1, hJM, hJr⟩ := hJ (pts k)
    have hJM' : J ≤ M := by omega
    have ht1 : ‖s k‖ / r ≤ 1 := ((div_lt_one h.1).2 (hsr' k)).le
    have h1 : (‖s k‖ / r) ^ M ≤ (‖s k‖ / r) ^ J :=
      pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) h.1.le) ht1 hJM'
    have h2 : lam0 ^ M < (‖s k‖ / r) ^ M := pow_lt_pow_left₀ hcon hl0.le (by omega)
    have h3 : ε k / N ≤ q := div_le_div_of_nonneg_right (hεle0 k) hNpos.le
    have := hJr
    change (‖s k‖ / r) ^ J ≤ ε k / N at this
    linarith
  set lam := max r lam0
  have hlam1 : lam < 1 := max_lt (h.2.trans ρ0.2.2) hl1
  have hlam0 : 0 ≤ lam := le_max_of_le_left h.1.le
  have hεgeom : ∀ k, ε k ≤ lam ^ k * ε 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      calc ε (k + 1) ≤ ε k * max r (‖s k‖ / r) := hdec' k
        _ ≤ ε k * lam := mul_le_mul_of_nonneg_left (max_le_max le_rfl (ht_le k)) (hεnn k)
        _ ≤ lam ^ k * ε 0 * lam := mul_le_mul_of_nonneg_right ih hlam0
        _ = lam ^ (k + 1) * ε 0 := by ring
  set mu := lam ^ ((M : ℝ)⁻¹)
  have hmu0 : 0 ≤ mu := Real.rpow_nonneg hlam0 _
  have hmu1 : mu < 1 := Real.rpow_lt_one hlam0 hlam1 (inv_pos.2 (by exact_mod_cast hM1))
  have hmuM : mu ^ M = lam := Real.rpow_inv_natCast_pow hlam0 (by omega)
  have hs_geom : ∀ k, ‖s k‖ ≤ mu ^ k := by
    intro k
    obtain ⟨J, hJ1, hJM, hJr⟩ := hJ (pts k)
    have hJM' : J ≤ M := by omega
    change (‖s k‖ / r) ^ J ≤ ε k / N at hJr
    have ht1 : ‖s k‖ / r ≤ 1 := ((div_lt_one h.1).2 (hsr' k)).le
    have h1 : (‖s k‖ / r) ^ M ≤ lam ^ k := by
      calc (‖s k‖ / r) ^ M ≤ (‖s k‖ / r) ^ J := pow_le_pow_of_le_one (div_nonneg (norm_nonneg _) h.1.le) ht1 hJM'
        _ ≤ ε k / N := hJr
        _ ≤ lam ^ k * ε 0 / N := div_le_div_of_nonneg_right (hεgeom k) hNpos.le
        _ = lam ^ k * q := by rw [mul_div_assoc]
        _ ≤ lam ^ k * 1 := mul_le_mul_of_nonneg_left hq1.le (pow_nonneg hlam0 k)
        _ = lam ^ k := mul_one _
    have h2 : ‖s k‖ / r ≤ mu ^ k := by
      by_contra hcon
      push_neg at hcon
      have := pow_lt_pow_left₀ hcon (pow_nonneg hmu0 k) (by omega : M ≠ 0)
      rw [← pow_mul, mul_comm, pow_mul, hmuM] at this
      linarith
    calc ‖s k‖ ≤ ‖s k‖ / r := le_div_self (norm_nonneg _) h.1 (h.2.trans ρ0.2.2).le
      _ ≤ mu ^ k := h2

  set S : ℕ → Γ := fun k => ∑ i ∈ Finset.range k, T.teich (s i) with hSdef
  have hs1 : ∀ k, ‖s k‖ ≤ 1 := fun k => ((hsr' k).trans (h.2.trans ρ0.2.2)).le
  have hSint : ∀ k, S k ∈ T.int := fun k =>
    Subring.sum_mem _ fun i _ => T.teich_mem_int (hs1 i)
  have hSsucc : ∀ k, S (k + 1) = S k + T.teich (s k) := fun k => by
    simp only [S, Finset.sum_range_succ]
  have hSpts : ∀ k, ((pts k).η : Γ) = P0.η - S k := by
    intro k
    induction k with
    | zero => simp [S, pts]
    | succ k ih =>
      rw [hpts_succ, hrel (pts k), ih, hSsucc]
      simp only [s]
      ring

  have hstep : ∀ n k, ‖T.coeff (S (k + 1)) n - T.coeff (S k) n‖ ≤
      (mu ^ coeffHolderExp p n) ^ k := by
    intro n k
    have hxp : T.PrefixLe (S k) n 1 := fun m _ => T.mem_int_iff.1 (hSint k) m
    have hyp : T.PrefixLe (T.teich (s k)) n ‖s k‖ := T.prefixLe_teich' (s k) n le_rfl
    have := T.norm_coeff_add_sub_le n (norm_nonneg _) (hs1 k) hxp hyp n le_rfl
    rw [Real.one_rpow, one_mul] at this
    rw [hSsucc]
    refine this.trans ?_
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) n
    calc ‖s k‖ ^ coeffHolderExp p n ≤ (mu ^ k) ^ coeffHolderExp p n :=
          Real.rpow_le_rpow (norm_nonneg _) (hs_geom k) ht0.le
      _ = (mu ^ coeffHolderExp p n) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hmu0, ← Real.rpow_mul hmu0,
            mul_comm]
  have hcauchy : ∀ n, CauchySeq (fun k => T.coeff (S k) n) := fun n => by
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) n
    refine cauchySeq_of_le_geometric (mu ^ coeffHolderExp p n) 1
      (Real.rpow_lt_one hmu0 hmu1 ht0) fun k => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul]
    exact hstep n k
  choose a ha using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (ha n))
      (Filter.Eventually.of_forall fun k => T.mem_int_iff.1 (hSint k) n)
  set X := T.ofCoeff a with hXdef
  have hXc : ∀ n, T.coeff X n = a n := fun n => by rw [hXdef, coeff_ofCoeff]
  have hXint : X ∈ T.int := T.mem_int_iff.2 fun n => by rw [hXc]; exact ha1 n

  set δ := r * lam0
  have hsδ : ∀ i, ‖s i‖ ≤ δ := fun i => by
    have := ht_le i
    rw [div_le_iff₀ h.1] at this
    show ‖s i‖ ≤ r * lam0
    linarith
  have hδ0 : 0 ≤ δ := mul_nonneg h.1.le hl0.le
  have hSpre : ∀ k, T.PrefixLe (S k) 1 δ := fun k =>
    T.prefixLe_sum _ _ hδ0 fun i _ => T.prefixLe_teich' (s i) 1 (hsδ i)
  have hXpre : T.PrefixLe X 1 δ := fun m hm => by
    rw [hXc]
    exact le_of_tendsto ((continuous_norm.tendsto _).comp (ha m))
      (Filter.Eventually.of_forall fun k => hSpre k m hm)
  have hδr : δ < T.ptRad P0.η := by
    rw [P0.hrad]; show r * lam0 < r; nlinarith [h.1]
  obtain ⟨hξi, hradi'⟩ := T.isPrimOne_sub_of_prefix P0.hη (Y := ⟨X, hXint⟩) hδ0 hδr hXpre
  set ξi : T.int := P0.η - ⟨X, hXint⟩ with hξidef
  have hradi : T.ptRad ξi = r := hradi'.trans P0.hrad
  have hri : T.ptRad ξi ≤ ρ0 := hradi.trans_le h.2.le
  have hIoci : T.ptRadIoc hξi hri = ⟨r, h.1, h.2.le⟩ := Subtype.ext hradi

  have hr1 : r < 1 := h.2.trans ρ0.2.2
  have hDint : ∀ k, X - S k ∈ T.int := fun k => sub_mem hXint (hSint k)
  set G : ℕ → ℝ := fun k => gaussNorm (T.zcoeff (X - S k)) r
  have hG : Tendsto G atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    set e' := min e 1 / 2 with he'
    have he'0 : 0 < e' := by positivity
    have he'1 : e' < 1 := by
      have := min_le_right e 1; rw [he']; linarith
    have he'e : e' < e := by
      have := min_le_left e 1; rw [he']; linarith
    obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one he'0 hr1
    set tol := e' ^ (p ^ n0 : ℕ)
    have htol0 : 0 < tol := by positivity
    have htol1 : tol ≤ 1 := pow_le_one₀ he'0.le he'1.le
    have htole : tol ^ ((p ^ n0 : ℕ) : ℝ)⁻¹ = e' :=
      Real.pow_rpow_inv_natCast he'0.le (pow_ne_zero _ hp.out.ne_zero)
    have hev : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (n0 + 1), ‖a i - T.coeff (S k) i‖ < tol := by
      refine (Finset.eventually_all _).2 fun i _ => ?_
      have := (ha i).eventually (Metric.ball_mem_nhds (a i) htol0)
      filter_upwards [this] with k hk
      rw [dist_eq_norm, norm_sub_rev] at hk
      exact hk
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg h.1)]
    have hpre := T.prefixLe_sub_of_coeff_close (u := X) (v := S k) (n := n0) htol0.le htol1
      (fun i _ => by rw [hXc]; exact ha1 i) (fun i _ => T.mem_int_iff.1 (hSint k) i)
      (fun i hi => by rw [hXc]; exact (hK k hk i (Finset.mem_range.2 (by omega))).le)
    rw [Real.one_rpow, one_mul, htole] at hpre
    refine lt_of_le_of_lt (gaussNorm_le fun n => ?_) he'e
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact he'0.le
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [T.zcoeff_natCast, zpow_natCast]
    by_cases hmn : m ≤ n0
    · calc ‖T.coeff (X - S k) m‖ * r ^ m ≤ ‖T.coeff (X - S k) m‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ h.1.le hr1.le) (norm_nonneg _)
        _ ≤ e' := by rw [mul_one]; exact hpre m hmn
    · have hc1 : ‖T.coeff (X - S k) m‖ ≤ 1 := T.mem_int_iff.1 (hDint k) m
      calc ‖T.coeff (X - S k) m‖ * r ^ m ≤ 1 * r ^ m :=
            mul_le_mul_of_nonneg_right hc1 (pow_nonneg h.1.le m)
        _ ≤ r ^ n0 := by rw [one_mul]; exact pow_le_pow_of_le_one h.1.le hr1.le (by omega)
        _ ≤ e' := hn0.le

  have hbound : ∀ k, ‖T.ptEval hξi hri x‖ ≤ max (ε k) (G k * (N / r)) := by
    intro k
    have hrk : T.ptRad (pts k).η ≤ ρ0 := (pts k).hrad.trans_le h.2.le
    set D := T.divStep (pts k).hη hrk x
    have h1 : ‖T.ptEval hξi hri (T.liftExt ρ0 D.z D.hV)‖ ≤ ε k := by
      refine (T.norm_ptEval_le hξi hri _).trans ?_
      rw [T.extNorm_liftExt _ _ D.hred, D.hz]
    have h2 : ‖T.ptEval hξi hri (T.ξExt (pts k).η ρ0)‖ ≤ G k := by
      rw [ξExt, T.ptEval_coe_algebraMap hξi hri]
      have hr0' := T.ptRad_pos' hξi
      have hr1' := T.ptRad_lt_one' hξi
      have hdiff : ((pts k).η : Γ) = (ξi : Γ) + (X - S k) := by
        rw [hSpts k, hξidef]; push_cast; ring
      rw [hdiff, T.ptE_add hξi (T.convergesAt_of_mem_int ξi.2 hr0' hr1')
        (T.convergesAt_of_mem_int (hDint k) hr0' hr1'), T.ptE_ξ hξi, zero_add]
      refine (T.norm_ptE_le hξi (T.convergesAt_of_mem_int (hDint k) hr0' hr1')).trans ?_
      rw [hradi]
    have h3 : ‖T.ptEval hξi hri D.next‖ ≤ N / r := by
      refine (T.norm_ptEval_le hξi hri _).trans ?_
      rw [hIoci]
      have := T.extNorm_next_le (hξ := (pts k).hη) (hr := hrk) x
      have hIock : T.ptRadIoc (pts k).hη hrk = ⟨r, h.1, h.2.le⟩ := Subtype.ext (pts k).hrad
      rw [hIock, (pts k).hrad] at this
      rw [le_div_iff₀ h.1, mul_comm]
      exact this
    have e := D.eq
    rw [e, map_add, map_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 ?_)
    rw [norm_mul]
    exact mul_le_mul h2 h3 (norm_nonneg _) (gaussNorm_nonneg h.1)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (ε 0)
    rw [zero_mul] at this
    exact squeeze_zero hεnn hεgeom this
  have hmaxlim : Tendsto (fun k => max (ε k) (G k * (N / r))) atTop (𝓝 0) := by
    have := hεlim.max (hG.mul_const (N / r))
    rwa [zero_mul, max_self] at this
  have hz : ‖T.ptEval hξi hri x‖ = 0 :=
    le_antisymm (ge_of_tendsto' hmaxlim hbound) (norm_nonneg _)
  exact ⟨ξi, hξi, hradi, norm_eq_zero.1 hz⟩

end Limit

variable [IsAlgClosed L] [CompleteSpace L] in

/- English proof (translation)
Take `⟨c, hc0, hc1, hrad, hlt⟩` from `T.exists_start_point hx ⟨hr0, hrρ⟩ hm`. Take `⟨η, hη, hrad', hval⟩` from `T.exists_zero_of_goodPt ⟨hr0, hrρ⟩ hx hm ⟨T.ptElt hc1.le, T.isPrimOne_ptElt hc0 hc1, hrad, hlt⟩`. Take `⟨y, hy⟩` from `(T.ptEval_eq_zero_iff hη _ x).1 hval`. Conclude with `⟨η, hη, hrad', y, hy⟩`.
-/
theorem exists_point_dvd {ρ0 : Set.Ioo (0 : ℝ) 1} {x : T.RobbaExt ρ0} (hx : x ≠ 0) {r : ℝ}
    (hr0 : 0 < r) (hrρ : r < ρ0) (hm : 1 ≤ T.mult x r) :
    ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ), T.ptRad ξ = r ∧ ∃ y, x = T.ξExt ξ ρ0 * y := by
  obtain ⟨c, hc0, hc1, hrad, hlt⟩ := T.exists_start_point hx ⟨hr0, hrρ⟩ hm
  obtain ⟨η, hη, hrad', hval⟩ := T.exists_zero_of_goodPt ⟨hr0, hrρ⟩ hx hm
    ⟨T.ptElt hc1.le, T.isPrimOne_ptElt hc0 hc1, hrad, hlt⟩
  obtain ⟨y, hy⟩ := (T.ptEval_eq_zero_iff hη _ x).1 hval
  exact ⟨η, hη, hrad', y, hy⟩

end TeichLift

end GroundTheory.PAdicHodge
