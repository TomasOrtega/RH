import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

/- English proof (translation)
Introduce `U0 W Top m f D Pl Emb _ hne logOmτ logOm hT`. Use `⟨fun hM => ?_, fun ρ => hT ρ⟩` and prove the remaining obligations. Take `⟨ρ⟩` from `hne`. Conclude with `(hM ρ).symm.trans (hT ρ)`.
-/
theorem periodicity_of_text : PerOfText := by
  intro U0 W Top m f D Pl Emb _ hne logOmτ logOm hT
  refine ⟨fun hM => ?_, fun ρ => hT ρ⟩
  obtain ⟨ρ⟩ := hne
  exact (hM ρ).symm.trans (hT ρ)

/- English proof (translation)
Introduce `U0 W Top _ m f D C`. Conclude with `Iff.rfl`.
-/
theorem divisibility_iff_free : DivIffFree := by
  intro U0 W Top _ m f D C
  exact Iff.rfl

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm h hp`. Establish `e : logOm = D.logOm` using `hp`. Substitute `e` using the available equality. Conclude with `h`.
-/
theorem divisibility_of_free : DivOfFree := by
  intro U0 W Top _ m f D C logOm h hp
  have e : logOm = D.logOm := hp
  subst e
  exact h

/- English proof (translation)
Introduce `Top _ m aT logT Om Om'`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun t _ => by ring`.
-/
theorem divisibility_principal_shift : DivMainShift := by
  intro Top _ m aT logT Om Om'
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm logOm'`. Establish `key : ∀ u0 (u : W u0), (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm) - D.aT t * Real.log (D.T u0 u))) = (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm') - D.aT t * Real.log (D.T u0 u))) + (m : ℝ) * D.sumA * (logOm' - logOm)`. Introduce `u0 u`. Use `divisibility_principal_shift Top (m : ℝ) D.aT (Real.log (D.T u0 u)) logOm' logOm` as an intermediate fact. Rewrite using `[this]`.

Unfold `Data.sumA`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `h u0 u`. Use `h u0 u` as an intermediate fact.

Rewrite `this` using `[key u0 u]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h u0 u`. Use `h u0 u` as an intermediate fact. Rewrite using `[key u0 u]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divisibility_free_shift : DivFreeShift := by
  intro U0 W Top _ m f D C logOm logOm'
  have key : ∀ u0 (u : W u0),
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm) - D.aT t * Real.log (D.T u0 u)))
        = (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm') - D.aT t * Real.log (D.T u0 u)))
          + (m : ℝ) * D.sumA * (logOm' - logOm) := by
    intro u0 u
    have := divisibility_principal_shift Top (m : ℝ) D.aT (Real.log (D.T u0 u)) logOm' logOm
    rw [this]
    unfold Data.sumA
    ring
  constructor
  · intro h u0 u
    have := h u0 u
    rw [key u0 u] at this
    linarith
  · intro h u0 u
    have := h u0 u
    rw [key u0 u]
    linarith

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm ha h hp`. Establish `h2` using `(divisibility_free_shift U0 W Top m f D C logOm D.logOm).mp h`. Introduce `u0 u`. Establish `h3` using `h2 u0 u`. Establish `hs : 0 ≤ D.sumA` using `Finset.sum_nonneg fun t _ => ha t`.

Establish `hle : D.logOm - logOm ≤ 0`. Establish `: D.logOm ≤ logOm` using `hp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : 0 ≤ (m : ℝ) * D.sumA` using `mul_nonneg (Nat.cast_nonneg m) hs`. Establish `: (m : ℝ) * D.sumA * (D.logOm - logOm) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hm hle`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divisibility_of_free_le : DivOfFreeLe := by
  intro U0 W Top _ m f D C logOm ha h hp
  have h2 := (divisibility_free_shift U0 W Top m f D C logOm D.logOm).mp h
  intro u0 u
  have h3 := h2 u0 u
  have hs : 0 ≤ D.sumA := Finset.sum_nonneg fun t _ => ha t
  have hle : D.logOm - logOm ≤ 0 := by
    have : D.logOm ≤ logOm := hp
    linarith
  have hm : 0 ≤ (m : ℝ) * D.sumA := mul_nonneg (Nat.cast_nonneg m) hs
  have : (m : ℝ) * D.sumA * (D.logOm - logOm) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hle
  linarith

/- English proof (translation)
Introduce `U0 W Top m f D logOm A B hp hg hA hB hL`. Establish `hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL` using `hp`. Rewrite using `[hp']`. Establish `h1` using `abs_le.mp hg`. Establish `h2` using `abs_le.mp hA`.

Establish `h3` using `abs_le.mp hB`. Conclude with `abs_le.mpr ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩`.
-/
theorem omega_size_of_periodicity : OmSizeOfPer := by
  intro U0 W Top m f D logOm A B hp hg hA hB hL
  have hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL := hp
  rw [hp']
  have h1 := abs_le.mp hg
  have h2 := abs_le.mp hA
  have h3 := abs_le.mp hB
  exact abs_le.mpr ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩

/- English proof (translation)
Introduce `U0 W Top m f D logOm hv`. Unfold `Per`. Rewrite using `[Real.log_div Real.pi_pos.ne' hv.ne']`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Real.exp_add, Real.exp_log Real.pi_pos]`. Introduce `h`. Establish `h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm)`.

Rewrite using `[h, Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem periodicity_iff_v : PerIffV := by
  intro U0 W Top m f D logOm hv
  unfold Per
  rw [Real.log_div Real.pi_pos.ne' hv.ne']
  constructor
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by linarith
    calc D.v = Real.exp (Real.log D.v) := (Real.exp_log hv).symm
      _ = Real.pi * Real.exp (D.gam - D.LpL - logOm) := by
        rw [h1, Real.exp_add, Real.exp_log Real.pi_pos]
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by
      rw [h, Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith

/- English proof (translation)
Introduce `gam LpL logOm`. Use `⟨Real.pi * Real.exp (gam - LpL - logOm), mul_pos Real.pi_pos (Real.exp_pos _), ?_⟩` and prove the remaining obligations. Rewrite using `[Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne', Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem periodicity_solvable : PerSolvable := by
  intro gam LpL logOm
  refine ⟨Real.pi * Real.exp (gam - LpL - logOm), mul_pos Real.pi_pos (Real.exp_pos _), ?_⟩
  rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
    Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm hv hw hp`. Establish `e : ∀ u0 j ρ, Real.log (D.w u0 j ρ * D.v / Real.pi) = Real.log (D.w u0 j ρ) + (D.gam - D.LpL - logOm)`. Introduce `u0 j ρ`. Establish `hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL` using `hp`. Rewrite `hp'` using `[Real.log_div Real.pi_pos.ne' hv.ne']`.

Rewrite using `[Real.log_div (mul_pos (hw u0 j ρ) hv).ne' Real.pi_pos.ne', Real.log_mul (hw u0 j ρ).ne' hv.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `CountFree`. Simplify using `only [e]`.
-/
theorem free_count_of_count : CountFreeOfCount := by
  intro U0 W Top _ m f D C logOm hv hw hp
  have e : ∀ u0 j ρ, Real.log (D.w u0 j ρ * D.v / Real.pi)
      = Real.log (D.w u0 j ρ) + (D.gam - D.LpL - logOm) := by
    intro u0 j ρ
    have hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL := hp
    rw [Real.log_div Real.pi_pos.ne' hv.ne'] at hp'
    rw [Real.log_div (mul_pos (hw u0 j ρ) hv).ne' Real.pi_pos.ne',
      Real.log_mul (hw u0 j ρ).ne' hv.ne']
    linarith
  unfold CountFree
  simp only [e]

/- English proof (translation)
Introduce `U0 W Top _ m f D C hw`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hD, hC⟩`. Use `⟨(withV D v).logOm, fun u0 u => hD u0 u, ?_, fun u0 u => ⟨(hC u0 u).2.1, (hC u0 u).2.2⟩⟩` and prove the remaining obligations. Establish `h` using `(free_count_of_count U0 W Top m f (withV D v) C (withV D v).logOm hv hw rfl).mpr (fun u0 u => (hC u0 u).1)`.

Conclude with `h`. Introduce and unpack `⟨logOm, h1, h2, h3⟩`. Take `⟨v, hv, hp⟩` from `periodicity_solvable D.gam D.LpL logOm`. Use `⟨v, hv, divisibility_of_free U0 W Top m f (withV D v) C logOm h1 hp, ?_⟩` and prove the remaining obligations. Introduce `u0 u`.

Conclude with `⟨(free_count_of_count U0 W Top m f (withV D v) C logOm hv hw hp).mp h2 u0 u, (h3 u0 u).1, (h3 u0 u).2⟩`.
-/
theorem v_elimination : VElim := by
  intro U0 W Top _ m f D C hw
  constructor
  · rintro ⟨v, hv, hD, hC⟩
    refine ⟨(withV D v).logOm, fun u0 u => hD u0 u, ?_, fun u0 u => ⟨(hC u0 u).2.1, (hC u0 u).2.2⟩⟩
    have h := (free_count_of_count U0 W Top m f (withV D v) C (withV D v).logOm hv hw rfl).mpr
      (fun u0 u => (hC u0 u).1)
    exact h
  · rintro ⟨logOm, h1, h2, h3⟩
    obtain ⟨v, hv, hp⟩ := periodicity_solvable D.gam D.LpL logOm
    refine ⟨v, hv, divisibility_of_free U0 W Top m f (withV D v) C logOm h1 hp, ?_⟩
    intro u0 u
    exact ⟨(free_count_of_count U0 W Top m f (withV D v) C logOm hv hw hp).mp h2 u0 u,
      (h3 u0 u).1, (h3 u0 u).2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma ph_eq (y : ℝ) : Formalism.LatticeIndexTer.ph y = ph y := rfl

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm C0 Pl e aP FoP haP hFo hC ha hLa hB hx h u0 u`. Establish `h1` using `h u0 u`. Unfold `ThmConcl at h1`. Rewrite `h1` using `[Finset.sum_map, Finset.card_map, Finset.card_univ]`. Simplify using `only [haP, ph_eq] at h1`.

Rewrite using `[hFo u0]`. Establish `hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa`. Establish `hY : 0 ≤ (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (Real.rpow_nonneg hx _)`. Establish `h2` using `mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)`. Establish `e1 : C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) = C.cDiv * ((Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))`.

Unfold `Data.nT`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divisibility_of_conclusion : DivOfConcl := by
  intro U0 W Top _ m f D C logOm C0 Pl e aP FoP haP hFo hC ha hLa hB hx h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP, ph_eq] at h1
  rw [hFo u0]
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa
  have hY : 0 ≤ (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  have e1 : C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
      = C.cDiv * ((Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)) := by
    unfold Data.nT
    ring
  linarith

/- English proof (translation)
Introduce `T U0 W Top _ m f D C P logOm Pl _ e _ aP St haP hFo hC hP hS`. Take `⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33⟩` from `hP`. Establish `hb : 0 < D.b` using `by rw [p4]; exact Real.exp_pos _`. Establish `hx0 : 0 ≤ D.x` using `by linarith`. Establish `ha : 0 ≤ D.a` using `by rw [p5]; exact mul_nonneg hx0 hb.le`.

Establish `hLa : 0 ≤ D.La` using `le_trans (abs_nonneg _) p22`. Establish `hB0 : 0 ≤ D.B0`. Rewrite using `[p10]`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le) (Real.rpow_nonneg hx0 _)`. Use `divisibility_of_conclusion U0 W Top m f D C logOm P.C0 Pl e aP (fun u0 => D.Fo u0 / 2) haP (fun u0 => by ring) hC.ge ha hLa (by linarith) hx0 ?_` and prove the remaining obligations.

Introduce `u0 u`. Take `⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩` from `hS u0 u`. Establish `hF : D.Fo u0 / 2 = (St u0 u).FoP` using `by rw [hFo u0 u]; ring`. Rewrite using `[hF]`. Conclude with `T (Fin m) Pl (Finset.univ.map e) (D.muCC u0) (St u0 u).mu0 (St u0 u).FoP (D.h u0 u) (St u0 u).hP (St u0 u).mlam (Real.log (D.T u0 u)) (St u0 u).hK aP (St u0 u).phν (St u0 u).nν (St u0 u).fa D.x D.ε D.L D.b D.a P.rd D.La D.B0 D.Nc (D.x ^ (C.eDiv * D.ε)) (m : ℝ) P.f D.k P.N P.S P.t …`.
-/
theorem divisibility_of_theorem : DivOfThm := by
  intro T U0 W Top _ m f D C P logOm Pl _ e _ aP St haP hFo hC hP hS
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33⟩ := hP
  have hb : 0 < D.b := by rw [p4]; exact Real.exp_pos _
  have hx0 : 0 ≤ D.x := by linarith
  have ha : 0 ≤ D.a := by rw [p5]; exact mul_nonneg hx0 hb.le
  have hLa : 0 ≤ D.La := le_trans (abs_nonneg _) p22
  have hB0 : 0 ≤ D.B0 := by
    rw [p10]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le) (Real.rpow_nonneg hx0 _)
  refine divisibility_of_conclusion U0 W Top m f D C logOm P.C0 Pl e aP (fun u0 => D.Fo u0 / 2) haP
    (fun u0 => by ring) hC.ge ha hLa (by linarith) hx0 ?_
  intro u0 u
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩ := hS u0 u
  have hF : D.Fo u0 / 2 = (St u0 u).FoP := by rw [hFo u0 u]; ring
  rw [hF]
  exact T (Fin m) Pl (Finset.univ.map e) (D.muCC u0) (St u0 u).mu0 (St u0 u).FoP (D.h u0 u) (St u0 u).hP
    (St u0 u).mlam (Real.log (D.T u0 u)) (St u0 u).hK aP (St u0 u).phν (St u0 u).nν (St u0 u).fa
    D.x D.ε D.L D.b D.a P.rd D.La D.B0 D.Nc (D.x ^ (C.eDiv * D.ε)) (m : ℝ) P.f D.k P.N P.S P.tt P.η P.w'' D.b'
    P.dC P.lam0 P.C0 (St u0 u).Lpass (St u0 u).Eb (St u0 u).e6 (St u0 u).eP logOm (St u0 u).eK (St u0 u).pq
    (St u0 u).w (St u0 u).eE (St u0 u).δ
    s1 s2 s3 s4 s5 s6 s7 s8 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 (by simp) p13 p14 p15 p16 p17 p18 p19 p20 p21
    s9 s10 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 s11 s12 s13 s14 s15 s16 s17

/- English proof (translation)
Introduce `x ε eDiv hx hε he`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)`.
-/
theorem exponent_of_divisibility : XeOfEDiv := by
  intro x ε eDiv hx hε he
  exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)

/- English proof (translation)
Introduce `H _ _ _ W _ m G cHH D ell N TT T2 a w Fm`. Establish `hL : (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε` using `by show Real.log (bTx G.x G.ε) = _`. Unfold `bTx`. Rewrite using `[Real.log_exp]`. Use `⟨hL, ?_, rfl, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hL]`. Both sides reduce to the same expression. Establish `h1 : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H` using `H)).card : ℂ) := Formalism.D5.Bal.card_G_eq`. Establish `h2 : Fintype.card (E0 × H) = 2 * (PhiSet (H` using `H)).card := by exact_mod_cast h1`. Establish `h3 : Fintype.card (E0 × H) = 4 * Fintype.card H`.

Simplify using `[Fintype.card_prod]`. Establish `h4 : (PhiSet (H` using `H)).card = 2 * Fintype.card H := by omega`. Conclude with `h4` after adjusting the coercions. Introduce `hx hk show 0 ≤ (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))`. Establish `hb : 0 ≤ bTx G.x G.ε` using `(Real.exp_pos _).le`.

Conclude with `div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk) hb) (Real.rpow_nonneg hx _)) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)))`. Use `show (Fintype.card TT : ℝ) = _`. Rewrite using `[Fintype.card_coe]`.
-/
theorem construct_parameter_definitions : MkParDefs := by
  intro H _ _ _ W _ m G cHH D ell N TT T2 a w Fm
  have hL : (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε := by
    show Real.log (bTx G.x G.ε) = _
    unfold bTx
    rw [Real.log_exp]
  refine ⟨hL, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hL]; rfl
  · have h1 : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := Formalism.D5.Bal.card_G_eq
    have h2 : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by exact_mod_cast h1
    have h3 : Fintype.card (E0 × H) = 4 * Fintype.card H := by
      simp [Fintype.card_prod]
    have h4 : (PhiSet (H := H)).card = 2 * Fintype.card H := by omega
    exact_mod_cast h4
  · intro hx hk
    show 0 ≤ (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
    have hb : 0 ≤ bTx G.x G.ε := (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk) hb) (Real.rpow_nonneg hx _))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)))
  · show (Fintype.card TT : ℝ) = _
    rw [Fintype.card_coe]

/- English proof (translation)
Introduce `U0 W Top _ m f D C C0 Pl e aP sE haP hE hC hB h`. Establish `hsum : (∑ t ∈ Finset.univ.map e, aP t) = D.sumA`. Rewrite using `[Finset.sum_map]`. Simplify using `only [haP]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Introduce `u0 u j`. Establish `h1` using `(h u0 u).1 j`. Rewrite `h1` using `[hsum]`. Rewrite using `[hE u0 u j]`.

Conclude with `h1.trans (mul_le_mul_of_nonneg_right hC hB)`. Introduce `u0 u`. Establish `h1` using `(h u0 u).2`. Rewrite `h1` using `[hsum]`. Establish `e1 : D.Ee u0 u = 2 * ∑ j, sE u0 u j`.

Unfold `Data.Ee`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => hE u0 u j`. Rewrite using `[e1]`. Establish `e2 : (m : ℝ) * D.sumA * D.lg = (m : ℝ) * (D.sumA * D.lg)` using `by ring`.

Rewrite using `[e2]`. Establish `hmB : 0 ≤ (m : ℝ) * D.B0` using `mul_nonneg (Nat.cast_nonneg _) hB`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exponent_comparison_of_constant : TypePrimeCostOfDeviationBound := by
  intro U0 W Top _ m f D C C0 Pl e aP sE haP hE hC hB h
  have hsum : (∑ t ∈ Finset.univ.map e, aP t) = D.sumA := by
    rw [Finset.sum_map]
    simp only [haP]
    rfl
  constructor
  · intro u0 u j
    have h1 := (h u0 u).1 j
    rw [hsum] at h1
    rw [hE u0 u j]
    exact h1.trans (mul_le_mul_of_nonneg_right hC hB)
  · intro u0 u
    have h1 := (h u0 u).2
    rw [hsum] at h1
    have e1 : D.Ee u0 u = 2 * ∑ j, sE u0 u j := by
      unfold Data.Ee
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hE u0 u j
    rw [e1]
    have e2 : (m : ℝ) * D.sumA * D.lg = (m : ℝ) * (D.sumA * D.lg) := by ring
    rw [e2]
    have hmB : 0 ≤ (m : ℝ) * D.B0 := mul_nonneg (Nat.cast_nonneg _) hB
    calc _ ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * ((m : ℝ) * D.B0) := h1
      _ ≤ C.cE * ((m : ℝ) * D.B0) := mul_le_mul_of_nonneg_right hC hmB
      _ = C.cE * (m : ℝ) * D.B0 := by ring

/- English proof (translation)
Introduce `U0 W Top _ m f D C C0 Pl e aP haP hC ha hLa hB h u0 u u'`. Establish `h1` using `h u0 u u'`. Rewrite `h1` using `[Finset.sum_map, Finset.sum_map, Finset.card_map, Finset.card_univ]`. Simplify using `only [haP] at h1`. Establish `hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * D.B0` using `add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa) (mul_nonneg (Nat.cast_nonneg _) hB)`.

Conclude with `h1.trans (mul_le_mul_of_nonneg_right hC hX)`.
-/
theorem height_comparison_of_constant : HeightVariationOfCorrectedHeightBound := by
  intro U0 W Top _ m f D C C0 Pl e aP haP hC ha hLa hB h u0 u u'
  have h1 := h u0 u u'
  rw [Finset.sum_map, Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP] at h1
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * D.B0 :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa) (mul_nonneg (Nat.cast_nonneg _) hB)
  exact h1.trans (mul_le_mul_of_nonneg_right hC hX)

/- English proof (translation)
Introduce `U0 W _ Top m f D C muMaxRR hF hD u0`. Take `⟨h1, h2, h3⟩` from `hF u0`. Establish `h4` using `hD u0`. Conclude with `⟨by linarith, h2, h3⟩`.
-/
theorem height_bound_of_function : HHOfFun := by
  intro U0 W _ Top m f D C muMaxRR hF hD u0
  obtain ⟨h1, h2, h3⟩ := hF u0
  have h4 := hD u0
  exact ⟨by linarith, h2, h3⟩

/- English proof (translation)
Introduce `U0 W _ Top m f D C muMaxRR c p1 p2 hx hb h1 h2 hp hH u0`. Rewrite using `[hH u0]`. Use `⟨?_, mul_pos (Real.rpow_pos_of_pos hx _) hb, le_rfl⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right hp hb.le` as an intermediate fact. Establish `a1` using `h1 u0`.

Establish `a2` using `h2 u0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem function_of_parts : FunOfParts := by
  intro U0 W _ Top m f D C muMaxRR c p1 p2 hx hb h1 h2 hp hH u0
  rw [hH u0]
  refine ⟨?_, mul_pos (Real.rpow_pos_of_pos hx _) hb, le_rfl⟩
  have := mul_le_mul_of_nonneg_right hp hb.le
  have a1 := h1 u0
  have a2 := h2 u0
  nlinarith

/- English proof (translation)
Introduce `U0 W _ Top _ m f D C c logOm hd hne`. Establish `hs : ∀ u0, (shiftRows D c).s u0 = D.s u0 + c u0`. Introduce `u0`. Use `hne u0` as an intermediate fact. Establish `hpos : 0 < ∑ u, D.d u0 u` using `Finset.sum_pos (fun u _ => hd u0 u) Finset.univ_nonempty`.

Use `show wmean (D.d u0) (fun u => D.muN u0 u - (D.h u0 u - c u0)) = wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u) + c u0`. Unfold `wmean`. Rewrite using `[eq_comm, div_add' _ _ _ hpos.ne']`. Use `congr 1`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun u _ => by ring`. Establish `e1 : ∀ u0 (u : W u0), (D.muCC u0 + c u0) + (D.h u0 u - c u0) - D.Fo u0 = D.muCC u0 + D.h u0 u - D.Fo u0` using `fun u0 u => by ring`. Use `⟨?_, ?_, ?_, ?_, hs⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h u0 u`.

Use `h u0 u` as an intermediate fact. Rewrite using `[← e1 u0 u]`. Conclude with `this`. Introduce `h u0 u`. Use `h u0 u` as an intermediate fact.

Rewrite `this` using `[← e1 u0 u]`. Conclude with `this`. Prove the components needed by the constructor for the conclusion. Introduce `h u0 u`. Use `h u0 u` as an intermediate fact.

Rewrite using `[← e1 u0 u]`. Conclude with `this`. Introduce `h u0 u`. Use `h u0 u` as an intermediate fact. Rewrite `this` using `[← e1 u0 u]`.

Conclude with `this`. Establish `e2 : ∀ u0 (u u' : W u0), ((D.h u0 u - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u)) - ((D.h u0 u' - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u')) = (D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u)) - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u'))` using `fun u0 u u' => by ring`. Prove the components needed by the constructor for the conclusion. Introduce `h u0 u u'`. Use `h u0 u u'` as an intermediate fact.

Rewrite using `[← e2 u0 u u']`. Conclude with `this`. Introduce `h u0 u u'`. Use `h u0 u u'` as an intermediate fact. Rewrite `this` using `[← e2 u0 u u']`.

Conclude with `this`. Establish `e3 : ∀ u0, (shiftRows D c).s u0 - (D.muMinCC u0 + c u0) = D.s u0 - D.muMinCC u0`. Introduce `u0`. Rewrite using `[hs u0]`. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Introduce `h u0`. Use `h u0` as an intermediate fact. Rewrite using `[← e3 u0]`. Conclude with `this`.

Introduce `h u0`. Use `h u0` as an intermediate fact. Rewrite `this` using `[← e3 u0]`. Conclude with `this`.
-/
theorem scale_free : ScaleFree := by
  intro U0 W _ Top _ m f D C c logOm hd hne
  have hs : ∀ u0, (shiftRows D c).s u0 = D.s u0 + c u0 := by
    intro u0
    have := hne u0
    have hpos : 0 < ∑ u, D.d u0 u := Finset.sum_pos (fun u _ => hd u0 u) Finset.univ_nonempty
    show wmean (D.d u0) (fun u => D.muN u0 u - (D.h u0 u - c u0))
      = wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u) + c u0
    unfold wmean
    rw [eq_comm, div_add' _ _ _ hpos.ne']
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have e1 : ∀ u0 (u : W u0), (D.muCC u0 + c u0) + (D.h u0 u - c u0) - D.Fo u0
      = D.muCC u0 + D.h u0 u - D.Fo u0 := fun u0 u => by ring
  refine ⟨?_, ?_, ?_, ?_, hs⟩
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · have e2 : ∀ u0 (u u' : W u0),
        ((D.h u0 u - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u))
          - ((D.h u0 u' - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u'))
        = (D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u))
          - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u')) := fun u0 u u' => by ring
    constructor
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u']
      exact this
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u'] at this
      exact this
  · have e3 : ∀ u0, (shiftRows D c).s u0 - (D.muMinCC u0 + c u0) = D.s u0 - D.muMinCC u0 := by
      intro u0
      rw [hs u0]
      ring
    constructor
    · intro h u0
      have := h u0
      rw [← e3 u0]
      exact this
    · intro h u0
      have := h u0
      rw [← e3 u0] at this
      exact this

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h0 : Submodule.span K (((⊥ : Submodule (𝓞 K) V) : Set V)) = ⊥` using `by simp`. Rewrite `hsp` using `[h0]`. Take `⟨i⟩` from `(inferInstance : Nonempty ι)`. Establish `: b i ∈ (⊥ : Submodule K V)` using `by rw [hsp]; trivial`.

Conclude with `b.ne_zero i (by simpa using this)`.
-/
lemma ne_bot_of_span {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [Nonempty ι]
    (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hsp : Submodule.span K (A : Set V) = ⊤) : A ≠ ⊥ := by
  rintro rfl
  have h0 : Submodule.span K (((⊥ : Submodule (𝓞 K) V) : Set V)) = ⊥ := by simp
  rw [h0] at hsp
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have : b i ∈ (⊥ : Submodule K V) := by rw [hsp]; trivial
  exact b.ne_zero i (by simpa using this)

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp`. Take `⟨dfg, dsp, _, dsize, dleast, dlargest, _⟩` from `dual_polygon_identity K V ι b X hX A hA hsp`. Establish `hX'` using `Formalism.HN.DualPolygon.dualFrame_unit X hX`. Establish `hA0 : A ≠ ⊥` using `ne_bot_of_span b A hsp`. Establish `hD0 : dualLat A ≠ ⊥` using `ne_bot_of_span b.dualBasis (dualLat A) dsp`.

Take `⟨_, a2, _, a4, a5, _⟩` from `size_maximal_slope K V ι b X hX A hA hA0`. Take `⟨_, d2, _, d4, d5, _⟩` from `size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' (dualLat A) dfg hD0`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[d2, a2, dsize, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `dlargest` using `[d5, a4, ← Real.exp_neg]`. Establish `h` using `Real.exp_injective dlargest`. Unfold `muMinDef muMaxDef`. Establish `e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2` using `by ring`. Rewrite `h` using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `dleast` using `[d4, a5, ← Real.exp_neg]`. Establish `h` using `Real.exp_injective dleast`. Unfold `muMinDef muMaxDef`. Establish `e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2` using `by ring`.

Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dual_slopes : DualSlopes := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  obtain ⟨dfg, dsp, _, dsize, dleast, dlargest, _⟩ := dual_polygon_identity K V ι b X hX A hA hsp
  have hX' := Formalism.HN.DualPolygon.dualFrame_unit X hX
  have hA0 : A ≠ ⊥ := ne_bot_of_span b A hsp
  have hD0 : dualLat A ≠ ⊥ := ne_bot_of_span b.dualBasis (dualLat A) dsp
  obtain ⟨_, a2, _, a4, a5, _⟩ := size_maximal_slope K V ι b X hX A hA hA0
  obtain ⟨_, d2, _, d4, d5, _⟩ :=
    size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' (dualLat A) dfg hD0
  refine ⟨?_, ?_, ?_⟩
  · rw [d2, a2, dsize, Real.log_inv]
    ring
  · rw [d5, a4, ← Real.exp_neg] at dlargest
    have h := Real.exp_injective dlargest
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith
  · rw [d4, a5, ← Real.exp_neg] at dleast
    have h := Real.exp_injective dleast
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith

/- English proof (translation)
Introduce `K _ _ _ _ D hD X hX R hR`. Establish `: Nonempty (Fin D)` using `⟨⟨0, hD⟩⟩`. Establish `hR0 : R ≠ ⊥` using `ne_bot_of_span (Pi.basisFun K (Fin D)) R hR.span_eq_top`. Take `⟨_, a2, _⟩` from `size_maximal_slope K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg hR0`. Establish `hpos : 0 < ht (Pi.basisFun K (Fin D)) X R` using `(place_lattice_structure K _ (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg).2.2`.

Establish `hrk : rkK R = D`. Unfold `rkK`. Rewrite using `[hR.span_eq_top, finrank_top]`. Simplify using the standard rewrite rules. Establish `hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ)`.

Use `sizeMu_finrank_eq K` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[a2]`. Unfold `size lcv`. Rewrite using `[Real.log_rpow hpos, hrk, hn]`.

Establish `hD' : (D : ℝ) ≠ 0` using `by exact_mod_cast hD.ne'`. Establish `hnp : (nPl K : ℝ) ≠ 0`. Establish `h1 : (0 : ℝ) < (Module.finrank ℚ K : ℝ)` using `by exact_mod_cast Module.finrank_pos`. Introduce `h0`. Rewrite `h1` using `[hn, h0]`.

Simplify using `at h1`. Clear the denominators using the available nonvanishing facts.
-/
theorem mu_log_conductor : MuLcv := by
  intro K _ _ _ _ D hD X hX R hR
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hR0 : R ≠ ⊥ := ne_bot_of_span (Pi.basisFun K (Fin D)) R hR.span_eq_top
  obtain ⟨_, a2, _⟩ := size_maximal_slope K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg hR0
  have hpos : 0 < ht (Pi.basisFun K (Fin D)) X R :=
    (place_lattice_structure K _ (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg).2.2
  have hrk : rkK R = D := by
    unfold rkK
    rw [hR.span_eq_top, finrank_top]
    simp
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    have := sizeMu_finrank_eq K
    exact_mod_cast this
  rw [a2]
  unfold size lcv
  rw [Real.log_rpow hpos, hrk, hn]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnp : (nPl K : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
    intro h0
    rw [hn, h0] at h1
    simp at h1
  field_simp

/- English proof (translation)
Introduce `I m F D hD XE hXE hX' R hR ψ hψ`. Take `⟨hinj, hnorm, hcc⟩` from `hψ`. Establish `: Nonempty (Fin D)` using `⟨⟨0, hD⟩⟩`. Take `⟨dfg, _⟩` from `dual_polygon_identity F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg hR.span_eq_top`. Take `⟨_, _, r3, _, r5, _⟩` from `lattice_rerealization F.K (Module.Dual F.K (Fin D → F.K)) (Fin D) F.Wd F.κ (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) F.b' F.X' ψ (Formalism.HN.DualPolygon.dualFrame_unit XE hXE) hX' hinj hnorm (dualLat R) dfg`.

Take `⟨s1, s2, _⟩` from `dual_slopes F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg hR.span_eq_top`. Establish `m1` using `mu_log_conductor F.K D hD XE hXE R hR`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hcc]`. Establish `: muDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K))) = muDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R)`.

Unfold `muDef`. Rewrite using `[r3]`. Rewrite using `[this, s1, m1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcc]`.

Establish `: muMinDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K))) = muMinDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R)`. Unfold `muMinDef`. Rewrite using `[r5]`. Rewrite using `[this, s2]`.
-/
theorem mu_constant_of_blocks : MuCCOfRows := by
  intro I m F D hD XE hXE hX' R hR ψ hψ
  obtain ⟨hinj, hnorm, hcc⟩ := hψ
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨dfg, _⟩ := dual_polygon_identity F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  obtain ⟨_, _, r3, _, r5, _⟩ := lattice_rerealization F.K (Module.Dual F.K (Fin D → F.K)) (Fin D) F.Wd F.κ
    (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) F.b' F.X' ψ (Formalism.HN.DualPolygon.dualFrame_unit XE hXE) hX' hinj hnorm
    (dualLat R) dfg
  obtain ⟨s1, s2, _⟩ := dual_slopes F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  have m1 := mu_log_conductor F.K D hD XE hXE R hR
  constructor
  · rw [hcc]
    have : muDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muDef
      rw [r3]
    rw [this, s1, m1]
    ring
  · rw [hcc]
    have : muMinDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muMinDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muMinDef
      rw [r5]
    rw [this, s2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `w w' h`. Establish `: w.asIdeal = w'.asIdeal` using `congrArg Subtype.val h`. Conclude with `HeightOneSpectrum.ext this`. Introduce `p`.

Use `⟨⟨p.1, p.2.isPrime, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)`.
-/
lemma plOf_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (plOf : HeightOneSpectrum (𝓞 K) → slopeLatticeData.FinPl K) := by
  constructor
  · intro w w' h
    have : w.asIdeal = w'.asIdeal := congrArg Subtype.val h
    exact HeightOneSpectrum.ext this
  · intro p
    refine ⟨⟨p.1, p.2.isPrime, ?_⟩, rfl⟩
    exact Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)

/- English proof (translation)
Introduce `K _ _ S φ`. Establish `hb` using `plOf_bijective K`. Prove the components needed by the constructor for the conclusion. Use `(S.finite_toSet.preimage hb.1.injOn).subset ?_` and prove the remaining obligations. Introduce `w hw`.

Assume the negation of the conclusion as `hn`. Apply `hw` to reduce the goal to its premises. Establish `: plOf w ∉ S` using `hn`. Simplify using `[this]`. Use `set g : slopeLatticeData.FinPl K → ℝ := fun v => slopeLatticeData.ell v * (if v ∈ S then ramE v * φ v else 0) with hg`.

Establish `h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)) = ∑ᶠ v, g v` using `finsum_comp_equiv (Equiv.ofBijective plOf hb) (f := g)`. Rewrite using `[h1, finsum_eq_sum_of_support_subset (s := S)]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Simplify using `only [hg, hw, if_true, lE]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `v hv`. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Establish `: v ∉ S` using `hn`. Simplify using `[hg, this]`.
-/
theorem sum_over_places : SumOverPlaces := by
  intro K _ _ S φ
  have hb := plOf_bijective K
  constructor
  · refine (S.finite_toSet.preimage hb.1.injOn).subset ?_
    intro w hw
    by_contra hn
    apply hw
    have : plOf w ∉ S := hn
    simp [this]
  · set g : slopeLatticeData.FinPl K → ℝ := fun v => slopeLatticeData.ell v * (if v ∈ S then ramE v * φ v else 0) with hg
    have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K),
        lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)) = ∑ᶠ v, g v :=
      finsum_comp_equiv (Equiv.ofBijective plOf hb) (f := g)
    rw [h1, finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [hg, hw, if_true, lE]
      ring
    · intro v hv
      by_contra hn
      apply hv
      have : v ∉ S := hn
      simp [hg, this]

/- English proof (translation)
Introduce `I m F`. Use `show 2 * ∑ j ∈ Finset.univ, ∑ w ∈ F.S, lE w * F.Fj j w = _`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => (sum_over_places F.K F.S (F.Fj j)).2`.
-/
theorem function_of_places : FoOfPlaces := by
  intro I m F
  show 2 * ∑ j ∈ Finset.univ, ∑ w ∈ F.S, lE w * F.Fj j w = _
  congr 1
  exact Finset.sum_congr rfl fun j _ => (sum_over_places F.K F.S (F.Fj j)).2

/- English proof (translation)
Introduce `I m F u j`. Use `show 2 * ∑ w ∈ F.S, lE w * F.Ej u j w = _`. Use `congr 1`. Conclude with `(sum_over_places F.K F.S (F.Ej u j)).2`.
-/
theorem exponent_of_places : EeJOfPlaces := by
  intro I m F u j
  show 2 * ∑ w ∈ F.S, lE w * F.Ej u j w = _
  congr 1
  exact (sum_over_places F.K F.S (F.Ej u j)).2

/- English proof (translation)
Introduce `H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm h hp`. Conclude with `divisibility_of_free H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C logOm h hp`.
-/
theorem construct_divisibility_of_free : MkDivOfFree := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm h hp
  exact divisibility_of_free H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C logOm h hp

/- English proof (translation)
Introduce `U0 W Top _ m f D C logOm`. Conclude with `Iff.rfl`.
-/
theorem divisibility_free_at : DivFreeIsDivAt := by
  intro U0 W Top _ m f D C logOm
  exact Iff.rfl

/- English proof (translation)
Introduce `e q d _ _ G logOm hv`. Unfold `PerHost PerMk`. Rewrite using `[hv]`.
-/
theorem construct_periodicity_of_modulus : PerMkOfHost := by
  intro e q d _ _ G logOm hv
  unfold PerHost PerMk
  rw [hv]

/- English proof (translation)
Introduce `H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm C0 Dd XE R ψ hD hXE hX' hR hψ hC hx hk hLa h u0 u`. Establish `h1` using `h u0 u`. Unfold `ThmConcl at h1`. Rewrite `h1` using `[Finset.sum_map, Finset.card_map]`. Establish `hmu` using `(mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0) (ψ u0) (hψ u0)).1`.

Establish `hFo` using `function_of_places (W u0) m (Fm u0)`. Rewrite `h1` using `[← hmu, ← hFo]`. Establish `hNc : 0 ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Nc` using `(construct_parameter_definitions H W m G C.cHH D ell N TT T2 a w Fm).2.2.2.2.2.1 hx hk`. Use `set Nc := (mkData G C.cHH D ell N TT T2 a w Fm).Nc with hNcdef`. Use `show muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc + (Fm u0).h u - (Fm u0).Fo ≤ (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ))) + C.cDiv * (Fintype.card TT : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m …`.

Rewrite using `[Finset.sum_coe_sort TT (fun t => (m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)), Fintype.card_coe]`. Establish `hsum : (∑ t ∈ TT, ((m : ℝ) * (Formalism.LatticeIndexTer.ph ((fun ρ : E0 × H => a ρ.2) (topEmb H t)) - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * logOm) - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * Real.log ((Fm u0).T u : ℝ))) = ∑ t ∈ TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Re …` using `rfl`. Rewrite `h1` using `[hsum]`. Establish `he : 0 ≤ Real.exp (G.x ^ G.ε)` using `(Real.exp_pos _).le`. Establish `hX : 0 ≤ (TT.card : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hx he)) hLa`.

Establish `hB : 0 ≤ (2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε` using `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) he) (Real.rpow_nonneg hx _)`. Establish `hY : 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc) * G.x ^ (C.eDiv * G.ε)` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB hNc)) (Real.rpow_nonneg hx _)`. Establish `h2` using `mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)`. Use polynomial arithmetic with `[h1, h2]`.
-/
theorem construct_divisibility_of_conclusion : MkDivOfConcl := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm C0 Dd XE R ψ hD hXE hX' hR hψ hC hx hk hLa h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map] at h1
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).1
  have hFo := function_of_places (W u0) m (Fm u0)
  rw [← hmu, ← hFo] at h1
  have hNc : 0 ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Nc :=
    (construct_parameter_definitions H W m G C.cHH D ell N TT T2 a w Fm).2.2.2.2.2.1 hx hk
  set Nc := (mkData G C.cHH D ell N TT T2 a w Fm).Nc with hNcdef
  show muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc + (Fm u0).h u - (Fm u0).Fo ≤
    (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)))
      + C.cDiv * (Fintype.card TT : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La
      + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
        * G.x ^ (C.eDiv * G.ε)
  rw [Finset.sum_coe_sort TT
    (fun t => (m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)), Fintype.card_coe]
  have hsum : (∑ t ∈ TT, ((m : ℝ) * (Formalism.LatticeIndexTer.ph ((fun ρ : E0 × H => a ρ.2) (topEmb H t))
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * logOm)
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * Real.log ((Fm u0).T u : ℝ)))
      = ∑ t ∈ TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)) := rfl
  rw [hsum] at h1
  have he : 0 ≤ Real.exp (G.x ^ G.ε) := (Real.exp_pos _).le
  have hX : 0 ≤ (TT.card : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hx he)) hLa
  have hB : 0 ≤ (2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) he)
      (Real.rpow_nonneg hx _)
  have hY : 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
      * G.x ^ (C.eDiv * G.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB hNc)) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  nlinarith [h1, h2]

/- English proof (translation)
Rewrite using `[← Finset.map_map, Finset.univ_eq_attach, Finset.attach_map_val]`.
-/
lemma univ_map_top {H : Type} [AddCommGroup H] (TT : Finset H) :
    (Finset.univ : Finset TT).map ((Function.Embedding.subtype _).trans (topEmb H)) = TT.map (topEmb H) := by
  rw [← Finset.map_map, Finset.univ_eq_attach, Finset.attach_map_val]

/- English proof (translation)
The claim follows from `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Real.exp_pos _).le) (Real.rpow_nonneg hx _)`.
-/
lemma threshold_constant_nonneg {H : Type} [Fintype H] (m : ℕ) (x ε : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (x ^ ε) * x ^ ε :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Real.exp_pos _).le) (Real.rpow_nonneg hx _)

/- English proof (translation)
Introduce `H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 g hg hC hx h`. Use `exponent_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H) ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun u0 u j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K), lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u …` and prove the remaining obligations. Introduce `u0 u`. Rewrite using `[univ_map_top]`. Establish `h1` using `h u0 u`.

Rewrite `h1` using `[← hg]`. Conclude with `h1`.
-/
theorem construct_exponent_comparison : TypePrimeCostOfDeviationBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 g hg hC hx h
  refine exponent_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2)
    (fun u0 u j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u j (plOf z) else 0))
    (fun t => rfl) (fun u0 u j => exponent_of_places (W u0) m (Fm u0) u j) hC
    (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0 u
  rw [univ_map_top]
  have h1 := h u0 u
  rw [← hg] at h1
  exact h1

/- English proof (translation)
Introduce `H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 hC hx hLa h`. Use `height_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H) ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun t => rfl) hC (mul_nonneg hx (Real.exp_pos _).le) hLa (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_` and prove the remaining obligations. Introduce `u0`. Rewrite using `[univ_map_top]`. Conclude with `h u0`.
-/
theorem construct_height_comparison : HeightVariationOfCorrectedHeightBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 hC hx hLa h
  refine height_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun t => rfl) hC
    (mul_nonneg hx (Real.exp_pos _).le) hLa (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0
  rw [univ_map_top]
  exact h u0

/- English proof (translation)
Introduce `H _ _ _ W _ m G C D ell N TT T2 a w Fm Dd XE R ψ hD hXE hX' hR hψ h u0`. Establish `hmu` using `(mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0) (ψ u0) (hψ u0)).2`. Establish `h1` using `h u0`. Rewrite using `[hmu]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem construct_height_bound : MkHHOfFun := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm Dd XE R ψ hD hXE hX' hR hψ h u0
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).2
  have h1 := h u0
  rw [hmu]
  linarith

def satD : Data Unit (fun _ => Unit) (Fin 1) 1 1 where
  x := 1
  ε := 1 / 52
  a := Real.exp 1
  b := Real.exp 1
  b' := 1
  k := 1
  L := 1
  La := 1
  B0 := Real.exp 1
  Nc := 0
  gam := 0
  LpL := 0
  v := Real.pi * Real.exp (-1)
  lg := 0
  logGam := 0
  aT := fun _ => 0
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 4
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 3 + Real.exp 1
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

def satC : Consts where
  cDiv := 60
  eDiv := 1
  cE := 0
  cH := 0
  cCount := 0
  cSlope := 0
  cSl1 := 0
  cLoss := 0
  eLoss := 0
  cHH := 0

def satP : ParNums where
  rd := 1
  f := 1
  N := 1
  S := 0
  tt := 0
  η := 0
  w'' := 0
  dC := 1
  lam0 := 1
  C0 := 1

def satSt : StepNums (Fin 1) (Fin 1) where
  mu0 := 1 + Real.exp 1
  FoP := 0
  hP := 2
  mlam := -1
  hK := fun _ => 1
  phν := fun _ _ => 2
  nν := fun _ _ => 4
  fa := fun _ _ => 0
  Lpass := 2
  Eb := Real.exp 1
  e6 := 1
  eP := 2
  eK := fun _ => 3
  pq := fun _ => 1
  w := fun _ _ => 1
  eE := fun _ _ => 2
  δ := fun _ _ => 3

/- English proof (translation)
Establish `e2 : (2 : ℝ) ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [ParHyp, satD, satP, satC]`. Evaluate the numerical expressions. Use the proof step `repeat' apply And.intro`.

Apply the tactic sequence `all_goals linarith`. Simplify using `only [StepHyp, satD, satP, satC, satSt, Formalism.LatticeIndexTer.ph]`. Evaluate the numerical expressions. Use the proof step `repeat' apply And.intro`. Apply the tactic sequence `all_goals linarith`.

Simplify using `only [Per, satD]`. Rewrite using `[Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne', Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_pos Real.pi_pos (Real.exp_pos _)`. Simplify using `only [satC, satP]`.

Evaluate the numerical expressions. Simplify using `only [satD, satSt]`. Evaluate the numerical expressions.
-/
theorem joint_sat :
    ParHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε)) (Fintype.card (Fin 1) : ℝ) ∧
    StepHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε))
      (Finset.univ.map (Function.Embedding.refl (Fin 1))) (fun _ => 0) () () satSt ∧
    Per satD 1 ∧ 0 < satD.v ∧ satC.cDiv = 50 * satP.C0 + 10 ∧ satD.Fo () = 2 * satSt.FoP := by
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ParHyp, satD, satP, satC]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [StepHyp, satD, satP, satC, satSt, Formalism.LatticeIndexTer.ph]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [Per, satD]
    rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
      Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  · exact mul_pos Real.pi_pos (Real.exp_pos _)
  · simp only [satC, satP]; norm_num
  · simp only [satD, satSt]; norm_num

end Formalism.LFunctionChainParameters.LBrDiv
