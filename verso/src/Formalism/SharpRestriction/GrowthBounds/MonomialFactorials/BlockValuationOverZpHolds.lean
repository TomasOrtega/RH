import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinPosEqCast

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

/- English proof (translation)
Establish `hs0 : 0 ≤ s` using `le_trans ht0 hts`. Establish `hA : 0 ≤ (((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)` using `by nlinarith`. Establish `e1 : ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 ≤ ((2 * s + 2) * r + 3 * (s + 1)) * Λ`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : U ≤ (s + 1) * ((r + 1) * (Λ + 1) + 1)`.

Establish `: 0 ≤ (r + 1) * (Λ + 1) + 1` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `e3 : (s + 1) * ((r + 1) * (Λ + 1) + 1) ≤ (s + 1) * ((2 * r + 3) * Λ)`. Apply `mul_le_mul_of_nonneg_left _ (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem loss_num (s t r Λ L1 U k0 : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr : 4 ≤ r) (hΛ : 1 ≤ Λ) (hL0 : 0 ≤ L1)
    (hL : L1 ≤ Λ) (hU : U ≤ (t + 1) * ((r + 1) * (Λ + 1) + 1)) (hk : 0 ≤ k0) :
    ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 + 2 * U ≤ 10 * (s + 1) * (r + 1) * Λ + k0 := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hA : 0 ≤ (((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1) := by nlinarith
  have e1 : ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 ≤
      ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by
    calc ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1
        ≤ ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * Λ := mul_le_mul_of_nonneg_left hL hA
      _ ≤ ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by nlinarith
  have e2 : U ≤ (s + 1) * ((r + 1) * (Λ + 1) + 1) := by
    have : 0 ≤ (r + 1) * (Λ + 1) + 1 := by nlinarith
    nlinarith
  have e3 : (s + 1) * ((r + 1) * (Λ + 1) + 1) ≤ (s + 1) * ((2 * r + 3) * Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  nlinarith

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

/- English proof (translation)
Introduce `aTop hT aPlus hP b hK l hl j' jp' hl' μ hw`. Take `⟨hA1, h2, h3, h4, h5⟩` from `gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK`. Establish `hF` using `hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH`. Establish `hlok : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK l.1 l.2` using `(Finset.mem_filter.1 hl).2`. Establish `hv` using `val_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) (aBig X) h2 h3 h4 h5 l.1 l.2 hlok j' jp' hl' μ hw`.

Establish `hvR : (padicValNat X.p (lvC (r` using `X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 * degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) ≤ (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + (((((2 * (X.s : ℝ) + 1) + 1) * (X.r : ℝ) + (((X.S C0 CE1 CE2).t : ℝ) + 1) * 2) + (((X.S C0 CE1 CE2).t : ℝ) + 1)) * (Nat.log …`. Use `(Nat.cast_le (α := ℝ)).2 hv` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hmR : (4 : ℝ) ≤ (X.r : ℝ)` using `by exact_mod_cast hF.m4`.

Establish `hp25 : (25 : ℝ) ≤ (X.p : ℝ)` using `by nlinarith [hF.p_ge]`. Establish `hp1 : (1 : ℝ) < (X.p : ℝ)` using `by linarith`. Establish `hs0 : (0 : ℝ) ≤ (X.s : ℝ)` using `Nat.cast_nonneg _`. Establish `ha1 : (1 : ℝ) ≤ (X.L.a : ℝ)` using `hF.a1`. Establish `hsm : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ)` using `by exact_mod_cast hF.s_le`.

Establish `hsp : 3 * (X.s : ℝ) + 2 ≤ (X.p : ℝ)` using `by nlinarith [hF.p_ge]`. Establish `hbase : (0 : ℝ) < 8 * (X.L.a : ℝ) + (X.r : ℝ)` using `by linarith`. Establish `hΛ : 1 ≤ lgA X.p X.L.a X.r`. Unfold `lgA`. Establish `: 0 ≤ Real.logb X.p (8 * (X.L.a : ℝ) + (X.r : ℝ))` using `Real.logb_nonneg hp1 (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbig : Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) ≤ lgA X.p X.L.a X.r`. Establish `e1 : 8 * (aBig X : ℝ) + (X.r : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * (X.L.a : ℝ) + (X.r : ℝ))`. Unfold `aBig`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e0 : (0 : ℝ) < 8 * (aBig X : ℝ) + (X.r : ℝ)`. Establish `: (0 : ℝ) ≤ (aBig X : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2` using `Real.logb_le_logb_of_le hp1 e0 e1`.

Rewrite `e2` using `[Real.logb_mul (by linarith) hbase.ne']`. Establish `e3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1`. Rewrite using `[Real.logb_le_iff_le_rpow hp1 (by linarith), Real.rpow_one]`. Conclude with `hsp`. Unfold `lgA`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL1 : (Nat.log X.p (8 * aBig X + X.r) : ℝ) ≤ lgA X.p X.L.a X.r`. Use `Real.natLog_le_logb (8 * aBig X + X.r) X.p` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this.trans hbig`.

Establish `hU : (expU X.p (r` using `X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤ (((X.S C0 CE1 CE2).t : ℝ) + 1) * (((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) + 1) := by`. Establish `e1 : (expU X.p (r` using `X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) = (((X.S C0 CE1 CE2).t : ℝ) + 1) * (⌈((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r⌉₊ : ℝ) := by`. Unfold `expU`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `e2 : Formalism.GM.lgV2 X.p (aBig X) X.r ≤ lgA X.p X.L.a X.r + 1`. Unfold `Formalism.GM.lgV2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e3 : 0 ≤ Formalism.GM.lgV2 X.p (aBig X) X.r`. Unfold `Formalism.GM.lgV2`. Establish `: 0 ≤ Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ))`. Apply `Real.logb_nonneg hp1` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ (aBig X : ℝ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4` using `(Nat.ceil_lt_add_one (show 0 ≤ ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r by positivity)).le`. Use `e4.trans ?_` and prove the remaining obligations. Establish `: ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r ≤ ((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1)` using `mul_le_mul_of_nonneg_left e2 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk0 : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r`. Unfold `kappaZeroExponent`. Establish `: 0 ≤ Real.logb X.p (X.L.a : ℝ)` using `Real.logb_nonneg hp1 ha1`. Check the signs of the components of the expression.

Establish `hts : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ)`. Establish `: (X.S C0 CE1 CE2).t ≤ X.s` using `Nat.sub_le _ _`. Conclude with `this` after adjusting the coercions. Establish `hfin` using `loss_num (X.s : ℝ) ((X.S C0 CE1 CE2).t : ℝ) (X.r : ℝ) (lgA X.p X.L.a X.r) (Nat.log X.p (8 * aBig X + X.r) : ℝ) (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) (kappaZeroExponent X.p X.L.a X.Nt X.r) (Nat.cast_nonneg _) hts hmR hΛ (Nat.cast_nonneg _) hL1 hU hk0`. Unfold `levelPassageLoss`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem restValNum_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestValNum C0 CE1 CE2 X := by
  classical
  intro aTop hT aPlus hP b hK l hl j' jp' hl' μ hw
  obtain ⟨hA1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hlok : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK l.1 l.2 := (Finset.mem_filter.1 hl).2
  have hv := val_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) (aBig X)
    h2 h3 h4 h5 l.1 l.2 hlok j' jp' hl' μ hw
  have hvR : (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
      degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) ≤
      (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) +
        (((((2 * (X.s : ℝ) + 1) + 1) * (X.r : ℝ) + (((X.S C0 CE1 CE2).t : ℝ) + 1) * 2) +
          (((X.S C0 CE1 CE2).t : ℝ) + 1)) * (Nat.log X.p (8 * aBig X + X.r) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hv
    push_cast at this
    exact this

  have hmR : (4 : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : (1 : ℝ) < (X.p : ℝ) := by linarith
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ (X.L.a : ℝ) := hF.a1
  have hsm : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hF.s_le
  have hsp : 3 * (X.s : ℝ) + 2 ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hbase : (0 : ℝ) < 8 * (X.L.a : ℝ) + (X.r : ℝ) := by linarith
  have hΛ : 1 ≤ lgA X.p X.L.a X.r := by
    unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.L.a : ℝ) + (X.r : ℝ)) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hbig : Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) ≤ lgA X.p X.L.a X.r := by
    have e1 : 8 * (aBig X : ℝ) + (X.r : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * (X.L.a : ℝ) + (X.r : ℝ)) := by
      unfold aBig; push_cast; nlinarith
    have e0 : (0 : ℝ) < 8 * (aBig X : ℝ) + (X.r : ℝ) := by
      have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
      linarith
    have e2 := Real.logb_le_logb_of_le hp1 e0 e1
    rw [Real.logb_mul (by linarith) hbase.ne'] at e2
    have e3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow hp1 (by linarith), Real.rpow_one]
      exact hsp
    unfold lgA
    linarith
  have hL1 : (Nat.log X.p (8 * aBig X + X.r) : ℝ) ≤ lgA X.p X.L.a X.r := by
    have := Real.natLog_le_logb (8 * aBig X + X.r) X.p
    push_cast at this
    exact this.trans hbig
  have hU : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
      (((X.S C0 CE1 CE2).t : ℝ) + 1) * (((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) + 1) := by
    have e1 : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) =
        (((X.S C0 CE1 CE2).t : ℝ) + 1) * (⌈((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r⌉₊ : ℝ) := by
      unfold expU
      push_cast
      rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e2 : Formalism.GM.lgV2 X.p (aBig X) X.r ≤ lgA X.p X.L.a X.r + 1 := by
      unfold Formalism.GM.lgV2
      linarith
    have e3 : 0 ≤ Formalism.GM.lgV2 X.p (aBig X) X.r := by
      unfold Formalism.GM.lgV2
      have : 0 ≤ Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) := by
        apply Real.logb_nonneg hp1
        have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have e4 := (Nat.ceil_lt_add_one (show 0 ≤ ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r by positivity)).le
    refine e4.trans ?_
    have : ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r ≤ ((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hk0 : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
    unfold kappaZeroExponent
    have : 0 ≤ Real.logb X.p (X.L.a : ℝ) := Real.logb_nonneg hp1 ha1
    positivity
  have hts : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hfin := loss_num (X.s : ℝ) ((X.S C0 CE1 CE2).t : ℝ) (X.r : ℝ) (lgA X.p X.L.a X.r)
    (Nat.log X.p (8 * aBig X + X.r) : ℝ) (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ)
    (kappaZeroExponent X.p X.L.a X.Nt X.r) (Nat.cast_nonneg _) hts hmR hΛ (Nat.cast_nonneg _) hL1 hU hk0
  unfold levelPassageLoss
  linarith

/- English proof (translation)
The claim follows from `block_valuation_Zp_of_numeric_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restValNum_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH)`.
-/
theorem block_valuation_over_Zp_holds {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_numeric_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restValNum_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
