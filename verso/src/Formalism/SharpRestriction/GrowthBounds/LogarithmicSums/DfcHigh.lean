import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeRpowNegLevelLe

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

open Classical in

def dropI (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then 1 else 0

/- English proof (translation)
Apply the tactic sequence `unfold dropI; split_ifs <;> norm_num`.
-/
theorem dropI_nonneg (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : 0 ≤ dropI X K a b p := by
  unfold dropI; split_ifs <;> norm_num

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem WReq_iff (X : Inst D L) (K : Consts) (a b : HH D → ℤ) :
    WReq X K a b ↔ ∑ p ∈ candF D L K, Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) ≤
      L.sc.x ^ (-9 : ℝ) := Iff.rfl

/- English proof (translation)
Unfold `candF`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 h.2.1), h⟩`.
-/
theorem mem_candF {K : Consts} {p : ℕ} (h : Cand D L K p) : p ∈ candF D L K := by
  classical
  unfold candF
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 h.2.1), h⟩

/- English proof (translation)
Unfold `candF at h`. Conclude with `(Finset.mem_filter.1 h).2`.
-/
theorem cand_of_mem {K : Consts} {p : ℕ} (h : p ∈ candF D L K) : Cand D L K p := by
  classical
  unfold candF at h
  exact (Finset.mem_filter.1 h).2

/- English proof (translation)
The claim follows from `div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)`.
-/
theorem lp_nonneg (p : ℕ) : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/- English proof (translation)
Unfold `SizeData₂.lifts`. Simplify using the standard rewrite rules.
-/
theorem lifts_card (D : D7) : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp

def Dfc (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) -
    ((∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p - ioP X K a b p)

/- English proof (translation)
Establish `ha` using `sc_one_lt_a L.sc`. Unfold `ioP`. Use `split_ifs with hne hc hc`. Establish `hC` using `cand_of_mem hc`. Establish `hp` using `hC.1`.

Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hs` using `hSig p hC`. Establish `hl : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`. Establish `hsup : (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤ 2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p`. Apply `Finset.sup'_le` to reduce the goal to its premises.

Introduce `t0 _`. Use `le_trans (sv_le X K hK P h p hp hC.2.1 t0) ?_` and prove the remaining obligations. Rewrite using `[div_le_div_iff_of_pos_right hp0]`. Establish `hN : (Nv X p t0 : ℝ) ≤ (D.host.TT.card : ℝ)`. Unfold `Nv topsOn`.

Conclude with `Finset.card_filter_le _ _` after adjusting the coercions. Establish `hm : (0 : ℝ) ≤ 2 * (D.R.m : ℝ)` using `by positivity`. Use `mul_le_mul_of_nonneg_left hN hm` as an intermediate fact. Conclude with `mul_le_mul_of_nonneg_right this (by linarith)`. Establish `h1 : 2 * Sig X K a b p * (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤ 2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p)` using `mul_le_mul_of_nonneg_left hsup (by linarith)`.

Establish `h2` using `mul_le_mul_of_nonneg_left h1 hl`. Use `le_trans h2 ?_` and prove the remaining obligations. Establish `hd` using `dropI_nonneg X K a b p`. Establish `h3 : 0 ≤ Real.log p / p * dropI X K a b p * (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)`. Use `lp_nonneg p` as an intermediate fact.

Check the signs of the components of the expression. Establish `e : Real.log p * (2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p)) = Real.log p / p * Sig X K a b p * (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd (mem_candF (cand_of_VV_ne X K a b p (Finset.nonempty_iff_ne_empty.1 hne))) hc`. Establish `hC` using `cand_of_mem hc`. Use `hSig p hC` as an intermediate fact. Use `dropI_nonneg X K a b p` as an intermediate fact.

Use `lp_nonneg p` as an intermediate fact. Rewrite using `[mul_zero]`. Check the signs of the components of the expression. Simplify using the standard rewrite rules.
-/
theorem io_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) {a b : HH D → ℤ} (h : InWin L a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p) (p : ℕ) :
    Real.log p * ioP X K a b p ≤
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
  classical
  have ha := sc_one_lt_a L.sc
  unfold ioP
  split_ifs with hne hc hc
  · have hC := cand_of_mem hc
    have hp := hC.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs := hSig p hC
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hsup : (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p := by
      apply Finset.sup'_le
      intro t0 _
      refine le_trans (sv_le X K hK P h p hp hC.2.1 t0) ?_
      rw [div_le_div_iff_of_pos_right hp0]
      have hN : (Nv X p t0 : ℝ) ≤ (D.host.TT.card : ℝ) := by
        unfold Nv topsOn
        exact_mod_cast Finset.card_filter_le _ _
      have hm : (0 : ℝ) ≤ 2 * (D.R.m : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hN hm
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h1 : 2 * Sig X K a b p * (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p) :=
      mul_le_mul_of_nonneg_left hsup (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 hl
    refine le_trans h2 ?_
    have hd := dropI_nonneg X K a b p
    have h3 : 0 ≤ Real.log p / p * dropI X K a b p * (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      have := lp_nonneg p
      positivity
    have e : Real.log p * (2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p)) =
        Real.log p / p * Sig X K a b p * (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      field_simp
      ring
    rw [e]
    linarith
  · exact absurd (mem_candF (cand_of_VV_ne X K a b p (Finset.nonempty_iff_ne_empty.1 hne))) hc
  · have hC := cand_of_mem hc
    have := hSig p hC
    have := dropI_nonneg X K a b p
    have := lp_nonneg p
    rw [mul_zero]
    positivity
  · simp

/- English proof (translation)
Introduce `h'`. Unfold `IsResidueClassZero at h`. Unfold `IsSg at h'`. Rewrite `h'` using `[h]`. Consider the cases of `h'`.
-/
theorem not_singular_of_central {p : ℕ} (h : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h'
  unfold IsResidueClassZero at h
  unfold IsSg at h'
  rw [h] at h'
  cases h'

/- English proof (translation)
Unfold `TTP`. Use `split_ifs`. Conclude with `Finset.Subset.refl _`. Conclude with `Finset.filter_subset _ _`.
-/
theorem TTP_subset (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

/- English proof (translation)
Establish `hlp` using `lp_nonneg p`. Establish `hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ)` using `Nat.cast_nonneg _`. Apply the tactic sequence `have t3 : 0 ≤ (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by split_ifs <;> positivity`. Apply the tactic sequence `have t4 : 0 ≤ (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by split_ifs <;> positivity`. Establish `t2 : 0 ≤ (if p ∈ PS then Real.log p / p * badf p else 0)` using `by split_ifs`.

Conclude with `mul_nonneg hlp (hbad0 p)`. Conclude with `le_rfl`. Establish `t8 : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) * (D.host.TT.card : ℝ)` using `by split_ifs with hc`. Use `hSig p (cand_of_mem hc)` as an intermediate fact. Use `dropI_nonneg X K a b p` as an intermediate fact.

Check the signs of the components of the expression. Simplify using the standard rewrite rules. Establish `hall : ((D.host.TT \ TTP X K a b p).card : ℝ) ≤ (D.host.TT.card : ℝ)`. Conclude with `Finset.card_le_card Finset.sdiff_subset` after adjusting the coercions. Establish `hall'` using `mul_le_mul_of_nonneg_left hall hlp`.

Distinguish the cases in `hX : (p : ℝ) < L.sc.X'`. Distinguish the cases in `ho : (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)`. Rewrite `t3`, the goal using `[if_pos (hA3 p hp hc0 hX ho)]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hb : L.sc.p0 D.R.k ≤ (p : ℝ) ∧ InBand D K L.sc p`.

Rewrite `t4`, the goal using `[if_pos (hA4 p hp hX hb.2)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC : Cand D L K p` using `⟨hp, hX, hc0, not_lt.1 ho, fun h1 h2 => hb ⟨h1, h2⟩⟩`. Establish `hs` using `hSig p hC`. Distinguish the cases in `hd : Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps)`.

Establish `hVV : VV X K a b p = goodReps X p` using `by unfold VV; rw [if_pos ⟨hC, hd⟩]`. Establish `hT : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)`. Unfold `TTP`. Rewrite using `[if_neg (by`. Introduce `h`.

Break down `h with h | h` into its components or cases. Conclude with `not_singular_of_central hc0 h`. Use the proof step `linarith), hVV]`. Rewrite `*` using `[hT, if_pos (hPS p hC)]`. Use `mul_le_mul_of_nonneg_left (hbad p hC) hlp` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdI : dropI X K a b p = 1` using `by unfold dropI; rw [if_pos (not_le.1 hd)]`. Rewrite `t8`, the goal using `[if_pos (mem_candF hC), hdI]`. Establish `: Real.log p / p * (D.host.TT.card : ℝ) ≤ Real.log p / p * (2 * 1 + 4 * Sig X K a b p) * (D.host.TT.card : ℝ)`. Establish `h1 : Real.log p / p ≤ Real.log p / p * (2 * 1 + 4 * Sig X K a b p)` using `by nlinarith`.

Conclude with `mul_le_mul_of_nonneg_right h1 hN`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : TTP X K a b p = D.host.TT`. Unfold `TTP`. Rewrite using `[if_pos (Or.inr (not_lt.1 hX))]`.

Rewrite using `[hT, Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sdiff_le (X : Inst D L) (K : Consts) {a b : HH D → ℤ}
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ)
    (hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3)
    (hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4)
    (hPS : ∀ p, Cand D L K p → p ∈ PS)
    (hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p)
    (hbad0 : ∀ p, 0 ≤ badf p) (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) :
    Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) ≤
      (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ PS then Real.log p / p * badf p else 0) +
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) * (D.host.TT.card : ℝ) := by
  classical
  have hlp := lp_nonneg p
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have t3 : 0 ≤ (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t4 : 0 ≤ (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t2 : 0 ≤ (if p ∈ PS then Real.log p / p * badf p else 0) := by
    split_ifs
    · exact mul_nonneg hlp (hbad0 p)
    · exact le_rfl
  have t8 : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (D.host.TT.card : ℝ) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      positivity
    · simp
  have hall : ((D.host.TT \ TTP X K a b p).card : ℝ) ≤ (D.host.TT.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hall' := mul_le_mul_of_nonneg_left hall hlp
  by_cases hX : (p : ℝ) < L.sc.X'
  · by_cases ho : (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)
    · rw [if_pos (hA3 p hp hc0 hX ho)] at t3 ⊢
      linarith
    · by_cases hb : L.sc.p0 D.R.k ≤ (p : ℝ) ∧ InBand D K L.sc p
      · rw [if_pos (hA4 p hp hX hb.2)] at t4 ⊢
        linarith
      · have hC : Cand D L K p := ⟨hp, hX, hc0, not_lt.1 ho, fun h1 h2 => hb ⟨h1, h2⟩⟩
        have hs := hSig p hC
        by_cases hd : Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps)
        · have hVV : VV X K a b p = goodReps X p := by unfold VV; rw [if_pos ⟨hC, hd⟩]
          have hT : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p) := by
            unfold TTP
            rw [if_neg (by
              intro h
              rcases h with h | h
              · exact not_singular_of_central hc0 h
              · linarith), hVV]
          rw [hT, if_pos (hPS p hC)] at *
          have := mul_le_mul_of_nonneg_left (hbad p hC) hlp
          linarith
        · have hdI : dropI X K a b p = 1 := by unfold dropI; rw [if_pos (not_le.1 hd)]
          rw [if_pos (mem_candF hC), hdI] at t8 ⊢
          have : Real.log p / p * (D.host.TT.card : ℝ) ≤
              Real.log p / p * (2 * 1 + 4 * Sig X K a b p) * (D.host.TT.card : ℝ) := by
            have h1 : Real.log p / p ≤ Real.log p / p * (2 * 1 + 4 * Sig X K a b p) := by nlinarith
            exact mul_le_mul_of_nonneg_right h1 hN
          linarith
  · have hT : TTP X K a b p = D.host.TT := by
      unfold TTP
      rw [if_pos (Or.inr (not_lt.1 hX))]
    rw [hT, Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith

/- English proof (translation)
Establish `g` using `(hG p hp (Or.inl hc0) hpX).2`. Establish `hsub` using `TTP_subset X K a b p`. Establish `hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L C bo p) + (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) + (D.host.TT.card : ℝ) * lo K L C bo p)`. Introduce `j hjl`. Rewrite using `[← Finset.sum_sdiff hsub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`.

Establish `h1 : ∑ s ∈ D.host.TT \ TTP X K a b p, askG X a b p j s ≤ ((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)`. Rewrite using `[← nsmul_eq_mul]`. Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises. Introduce `s hs`. Conclude with `(ask_bounds P X h p hp j hjl s (Finset.mem_sdiff.1 hs).1).2`.

Establish `h2 : ((TTP X K a b p).card : ℝ) * lo K L C bo p ≤ (D.host.TT.card : ℝ) * lo K L C bo p`. Apply `mul_le_mul_of_nonneg_right _ hlo` to reduce the goal to its premises. Conclude with `Finset.card_le_card hsub` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `Finset.sum_le_sum hj`.

Rewrite `hs` using `[Finset.sum_add_distrib, Finset.sum_const, lifts_card, nsmul_eq_mul]`. Unfold `Dfc`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dfc_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) (hlo : 0 ≤ lo K L C bo p) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p := by
  classical
  have g := (hG p hp (Or.inl hc0) hpX).2
  have hsub := TTP_subset X K a b p
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤
      ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L C bo p) +
        (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) + (D.host.TT.card : ℝ) * lo K L C bo p) := by
    intro j hjl
    rw [← Finset.sum_sdiff hsub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ s ∈ D.host.TT \ TTP X K a b p, askG X a b p j s ≤
        ((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro s hs
      exact (ask_bounds P X h p hp j hjl s (Finset.mem_sdiff.1 hs).1).2
    have h2 : ((TTP X K a b p).card : ℝ) * lo K L C bo p ≤ (D.host.TT.card : ℝ) * lo K L C bo p := by
      apply mul_le_mul_of_nonneg_right _ hlo
      exact_mod_cast Finset.card_le_card hsub
    linarith
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_const, lifts_card, nsmul_eq_mul] at hs
  unfold Dfc
  linarith

/- English proof (translation)
Establish `hVV : VV X K a b p = ∅`. Assume the negation of the conclusion as `hne`. Establish `hC` using `cand_of_VV_ne X K a b p hne`. Use `X'_le_X'' L.sc D.R.n (n_pos D)` as an intermediate fact. Use `hC.2.1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg : ∀ j, gainP X K a b p j = 0`. Introduce `j`. Unfold `gainP`. Rewrite using `[if_pos (Or.inr hpX)]`.

Establish `ht : tauP X K a b p = 0` using `by unfold tauP; rw [if_pos hVV]`. Establish `hi : ioP X K a b p = 0`. Unfold `ioP; rw [dif_neg (by rw [hVV]; simp)]`. Unfold `Dfc`. Rewrite using `[ht, hi]`.

Simplify using `only [hg, Finset.sum_const_zero, sub_zero]`. Establish `hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) * (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)`. Introduce `j hjl`. Rewrite using `[← nsmul_eq_mul]`. Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises.

Introduce `s hs`. Conclude with `ask_high P X h p hpX j hjl s hs`. Establish `hs` using `Finset.sum_le_card_nsmul _ _ _ hj`. Rewrite `hs` using `[lifts_card, nsmul_eq_mul]`. Conclude with `hs`.
-/
theorem dfc_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) {a b : HH D → ℤ} (h : InWin L a b)
    (p : ℕ) (hpX : L.sc.X'' D.R.n < (p : ℝ)) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)) := by
  classical
  have hVV : VV X K a b p = ∅ := by
    by_contra hne
    have hC := cand_of_VV_ne X K a b p hne
    have := X'_le_X'' L.sc D.R.n (n_pos D)
    have := hC.2.1
    linarith
  have hg : ∀ j, gainP X K a b p j = 0 := by
    intro j; unfold gainP; rw [if_pos (Or.inr hpX)]
  have ht : tauP X K a b p = 0 := by unfold tauP; rw [if_pos hVV]
  have hi : ioP X K a b p = 0 := by
    unfold ioP; rw [dif_neg (by rw [hVV]; simp)]
  unfold Dfc
  rw [ht, hi]
  simp only [hg, Finset.sum_const_zero, sub_zero]
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0) := by
    intro j hjl
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro s hs
    exact ask_high P X h p hpX j hjl s hs
  have hs := Finset.sum_le_card_nsmul _ _ _ hj
  rw [lifts_card, nsmul_eq_mul] at hs
  exact hs

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
