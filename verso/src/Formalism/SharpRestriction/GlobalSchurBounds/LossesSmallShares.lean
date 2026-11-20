import Formalism.SharpRestriction.GlobalSchurBounds.PrvFOfFamilyTheoremTiesEventualIncidenceTransport
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesSeven

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

variable {eps : ℝ}

def LossFS (Fm : FamP eps) (eL : ℝ) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    (∃ i1 : Fm.Ix x, ∀ t : (Fm.D x i1).host.TT,
        (Fm.L x i1).aT t = av (t : (Fm.D x i1).R.A).val ∧
        (Fm.L x i1).bT t = bv (t : (Fm.D x i1).R.A).val) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → Loss_at (Fm.L x i) C eL

/- English proof (translation)
Take `⟨C, x0, hC, hL⟩` from `h`. Use `⟨C, max x0 (Fm.x1 + 1), hC, fun x hx hwin => ?_⟩` and prove the remaining obligations. Take `⟨i0, av, bv, h1, h2⟩` from `hL x (le_of_max_le_left hx) hwin`. Establish `hx1 : Fm.x1 < x` using `by linarith [le_of_max_le_right hx]`. Establish `hn : 0 < (Fm.D x i0).R.n`.

Establish `e1` using `(Fm.D x i0).R.two_le_m`. Establish `e2` using `(Fm.D x i0).R.m_le_f`. Unfold `Formalism.BasicNotions.Ranks.n`. Use linear arithmetic over natural numbers and integers. Take `⟨i1, -, hi1⟩` from `hc x hx1 i0 0 av bv hn h1`.

Conclude with `⟨i0, av, bv, h1, ⟨i1, hi1⟩, h2⟩`.
-/
theorem lossFS_of_cover (Fm : FamP eps) (eL : ℝ) (h : LossF Fm eL) (hc : Fm.CoverAll) : LossFS Fm eL := by
  obtain ⟨C, x0, hC, hL⟩ := h
  refine ⟨C, max x0 (Fm.x1 + 1), hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h2⟩ := hL x (le_of_max_le_left hx) hwin
  have hx1 : Fm.x1 < x := by linarith [le_of_max_le_right hx]
  have hn : 0 < (Fm.D x i0).R.n := by
    have e1 := (Fm.D x i0).R.two_le_m
    have e2 := (Fm.D x i0).R.m_le_f
    unfold Formalism.BasicNotions.Ranks.n
    omega
  obtain ⟨i1, -, hi1⟩ := hc x hx1 i0 0 av bv hn h1
  exact ⟨i0, av, bv, h1, ⟨i1, hi1⟩, h2⟩

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨xQD, hQD⟩` from `cQD`. Take `⟨xTh, hTh⟩` from `cTh`. Take `⟨Cc, xC, hCc, hC⟩` from `hCount`. Take `⟨Cs, xS, hCs, hS⟩` from `hSM`. Take `⟨C1, xN, hC1, hN⟩` from `hSN`.

Take `⟨xL, hL⟩` from `hLat`. Take `⟨xO, hO⟩` from `hNodes`. Take `⟨xF, hF⟩` from `hFr`. Take `⟨Cl, xLo, hCl, hLo⟩` from `hLoss`. Take `⟨xCh, hChr⟩` from `hChar c6 C5`.

Take `⟨eK, xW, heK, hW⟩` from `hWin c6 hc6`. Take `⟨xTT, hTT⟩` from `cTT`. Take `⟨xI, hI⟩` from `lI`. Take `⟨Cd, xD, hD⟩` from `lD`. Establish `hCd' : (0 : ℝ) ≤ max Cd 0` using `le_max_right _ _`.

Establish `hCdle : Cd ≤ max Cd 0` using `le_max_left _ _`. Use `⟨max Cd 0 + Cc + Cs + C1 + Cl + 6, CH, eK, C5, Fm.x1 + 1 + |xQD| + |xTh| + |xC| + |xS| + |xN| + |xL| + |xO| + |xF| + |xLo| + |xCh| + |xW| + |xTT| + |xI| + |xD|, fun x hx hxw => ?_⟩` and prove the remaining obligations. Establish `hpos` using `Fm.one_lt_family_threshold`. Establish `habs : 0 ≤ |xQD| ∧ 0 ≤ |xTh| ∧ 0 ≤ |xC| ∧ 0 ≤ |xS| ∧ 0 ≤ |xN| ∧ 0 ≤ |xL| ∧ 0 ≤ |xO| ∧ 0 ≤ |xF| ∧ 0 ≤ |xLo| ∧ 0 ≤ |xCh| ∧ 0 ≤ |xW| ∧ 0 ≤ |xTT| ∧ 0 ≤ |xI| ∧ 0 ≤ |xD|` using `⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _⟩`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩` from `habs`.

Establish `hx1 : Fm.x1 < x` using `by linarith`. Establish `hxQD : x ≥ xQD` using `by linarith [le_abs_self xQD]`. Establish `hxTh : x ≥ xTh` using `by linarith [le_abs_self xTh]`. Establish `hxC : x ≥ xC` using `by linarith [le_abs_self xC]`. Establish `hxS : x ≥ xS` using `by linarith [le_abs_self xS]`.

Establish `hxN : x ≥ xN` using `by linarith [le_abs_self xN]`. Establish `hxL : x ≥ xL` using `by linarith [le_abs_self xL]`. Establish `hxO : x ≥ xO` using `by linarith [le_abs_self xO]`. Establish `hxF : x ≥ xF` using `by linarith [le_abs_self xF]`. Establish `hxLo : x ≥ xLo` using `by linarith [le_abs_self xLo]`.

Establish `hxCh : x ≥ xCh` using `by linarith [le_abs_self xCh]`. Establish `hxW : x ≥ xW` using `by linarith [le_abs_self xW]`. Establish `hxTT : x ≥ xTT` using `by linarith [le_abs_self xTT]`. Establish `hxI : x ≥ xI` using `by linarith [le_abs_self xI]`. Establish `hxD : x ≥ xD` using `by linarith [le_abs_self xD]`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1' : 1 ≤ x` using `by linarith`. Take `⟨i0, av, bv, hadm, ⟨i1, hc1⟩, hloss⟩` from `hLo x hxLo hxw`. Establish `hcov : ∀ u0 : (Fm.D x i0).R.A, ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = hval _ u0 ∧ ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧ (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val` using `fun u0 => Fm.coverS_carry x hx1 i1 av bv hc1 (hval _ u0) (by rw [Fm.R_eq x i1 i0]; exact hval_lt _ u0)`. Use `choose pt hpt1 hpt2 using hcov`.

Set `M : Mod Fm x` to `⟨i0, av, bv, pt, hpt1, hpt2⟩`. Establish `iq : Fact M.q.Prime` using `⟨(Fm.D x i0).host.hyp.1⟩`. Establish `id : Fact M.d.Prime` using `⟨(Fm.D x i0).host.hyp.2.1⟩`. Take `⟨etaB, eB, hη0, he0, he4, h6, hFa⟩` from `hF x hxF`. Establish `hFa' : ∀ u0 : M.e.A, Frame_at (Fm.D x (M.pt u0)) etaB eB` using `fun u0 => hFa (M.pt u0)`.

Unfold `Frame_at at hFa'`. Use `choose ηv ev hηv0 hηvB hev0 hevB hfr using hFa'`. Take `⟨ell, hell1, hell2, hell3, hell4⟩` from `hChr x hxCh i0 M.e M.AD rfl HEq.rfl`. Establish `heps : 0 < eps` using `by have h := (Fm.L x i0).sc.eps_pos; rwa [Fm.L_eps] at h`. Establish `hez : 0 < Fm.ez` using `div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)`.

Establish `heps1 : eps ≤ 1` using `by have h := (Fm.L x i0).sc.eps_lt; rw [Fm.L_eps] at h; linarith`. Establish `hsx : (Fm.L x i0).sc.x = x` using `Fm.L_x x i0 hx1`. Establish `hse : (Fm.L x i0).sc.eps = eps` using `Fm.L_eps x i0`. Establish `hWu : ∀ u0 : M.e.A, Win_at (Fm.L x (M.pt u0)) eK c6` using `fun u0 => hW x hxW (M.pt u0)`. Establish `hW0` using `hW x hxW i0`.

Unfold `Win_at at hW0`. Rewrite `hW0` using `[hsx, hse]`. Take `⟨w1, w2, w3, w4, w5, w6, w7, w8, -, -, w11, w12, w13, w14, w15, -, w17⟩` from `hW0`. Establish `ha0` using `sc_a_pos (Fm.L x i0).sc`. Establish `hb'0` using `sc_b'_pos (Fm.L x i0).sc`.

Establish `hb0 : 0 < (Fm.L x i0).sc.b` using `Real.exp_pos _`. Establish `hab : (Fm.L x i0).sc.a = x * (Fm.L x i0).sc.b` using `by show (Fm.L x i0).sc.x * (Fm.L x i0).sc.b = _`. Rewrite using `[hsx]`. Establish `hLx : (Fm.L x i0).sc.L = x ^ eps` using `by show (Fm.L x i0).sc.x ^ (Fm.L x i0).sc.eps = _`. Rewrite using `[hsx, hse]`.

Establish `hxe : 1 ≤ x ^ eps` using `Real.one_le_rpow hx1' heps.le`. Establish `hb1 : 1 ≤ (Fm.L x i0).sc.b` using `by show 1 ≤ Real.exp (Fm.L x i0).sc.L`. Rewrite using `[hLx]; exact Real.one_le_exp (by linarith)`. Establish `hk5` using `(Fm.D x i0).R.k_ge`. Establish `hk1 : (1 : ℝ) ≤ ((Fm.D x i0).R.k : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ (Fm.D x i0).R.k)`.

Establish `hnod` using `fun u0 : M.e.A => hO x hxO (M.pt u0) M.e M.m M.T2 u0 (M.w u0) (M.he u0) (M.hm u0) (fun h => by rw [M.mem_thick_set_model_iff, Fm.realisedChain_torus_eq x M.i0 (M.pt u0)]) (M.point_base_value u0) (M.w_tie u0) (M.w_off u0)`. Establish `hcut : ∀ (u0 : M.e.A) (j : Fin M.m) (t : M.e.A) (ρ : E0 × M.e.A), t ∈ M.TT → InPhi ρ → M.a t / M.w u0 j ρ ≤ (⌈2 * (Fm.L x i0).sc.a⌉₊ : ℝ)`. Introduce `u0 j t ρ ht hρ`. Take `⟨ha1, ha2, -⟩` from `M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)`. Establish `hw1` using `(hnod u0).1 j ρ hρ`.

Establish `hat : 0 ≤ M.a t` using `le_trans ha0.le ha1`. Combine the equalities or inequalities in the displayed calculation. Establish `hDu` using `fun u0 : M.e.A => hD x hxD (M.pt u0)`. Establish `hLau : ∀ u0 : M.e.A, 0 ≤ (Fm.L x (M.pt u0)).La` using `fun u0 => (hWu u0).2.2.2.2.1`. Establish `hnT : (1 : ℝ) ≤ (Fintype.card ↥(Fm.TTn x) : ℝ)`.

Establish `h1` using `(hTT x hxTT i0).1`. Establish `hd : 0 < (Fm.L x i0).sc.delta1`. Unfold `Scale.delta1`. Rewrite using `[hsx]`. Conclude with `Real.rpow_pos_of_pos hx0 _`.

Establish `hn : (0 : ℝ) < ((Fm.D x i0).R.n : ℝ)`. Establish `: 0 < (Fm.D x i0).R.n` using `(Fm.D x i0).R.toFrame.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `h2 : (0 : ℝ) < ((Fm.D x i0).host.TT.card : ℝ)` using `lt_of_lt_of_le (by positivity) h1`. Rewrite `h2` using `[card_TT Fm x i0]`.

Conclude with `Nat.succ_le_of_lt (Nat.cast_pos.mp h2)` after adjusting the coercions. Establish `hXpp0 : 0 ≤ (Fm.L x i0).sc.X'' (Fm.D x i0).R.n`. Unfold `Scale.X'' Scale.w''`. Conclude with `div_nonneg ha0.le (div_nonneg hb'0.le (mul_nonneg (by rw [hsx]; exact hx0.le) (Nat.cast_nonneg _)))`. Establish `hX' : (Fm.L x i0).sc.X' = Real.exp (x ^ (eps / 3))` using `by show Real.exp ((Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3)) = _`.

Rewrite using `[hsx, hse]`. Establish `L1 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HidaSetting (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)` using `⟨hx0, hb0, ha0.le, hb'0.le, lt_of_lt_of_le one_pos hk1, w17, Nat.mul_pos two_pos (Fm.D x i0).R.toFrame.ord_pos, fun τ => le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1, fun u0 j ρ => lt_of_lt_of_le one_pos ((hnod u0).1 j _ (Finset.mem_filter.mp (M.eP ρ).2).2), fun u0 u => Nat.cas …`. Establish `h` using `Real.exp_lt_exp.mpr (show -(x ^ (Fm.ez / 7)) < 0 by`. Use `Real.rpow_pos_of_pos hx0 (Fm.ez / 7)` as an intermediate fact. Use the proof step `linarith)`.

Rewrite using `[Real.exp_zero] at h), hη0, he0, he4⟩` and apply the resulting hypothesis. Establish `L2 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).DIV (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)`. Apply `M.data_DIV hx1` to reduce the goal to its premises. Introduce `u0 u`. Establish `h` using `(hDu u0).2.2.2.2.2.2.1 u`.

Establish `hX1 : 0 ≤ ((Fm.D x (M.pt u0)).host.TT.card : ℝ) * ((Fm.L x (M.pt u0)).sc.a * (Fm.L x (M.pt u0)).La)` using `mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sc_a_pos _).le (hLau u0))`. Establish `hX2 : 0 ≤ ((Fm.D x (M.pt u0)).R.m : ℝ) * (((Fm.L x (M.pt u0)).B0 + (Fm.L x (M.pt u0)).Nc) * (Fm.L x (M.pt u0)).sc.x ^ (Cabs * (Fm.L x (M.pt u0)).sc.eps))` using `mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (add_nonneg (loss_bound_nonneg _) (Nc_nonneg _)) (Real.rpow_nonneg (lt_trans one_pos (Fm.L x (M.pt u0)).sc.one_lt_alt).le _))`. Establish `e1` using `up hCdle hX1`. Establish `e2` using `up hCdle hX2`. Use `show _ ≤ _ + max Cd 0 * _ * _ * _ + max Cd 0 * _ * _ * _ ^ (Cabs * _)`.

Simplify using `only [mul_assoc] at h e1 e2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `L3 : EComp5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)`. Apply `M.data_EComp5 hx1` to reduce the goal to its premises. Introduce `u0 u j hj`.

Conclude with `le_trans ((hDu u0).2.2.2.2.2.2.2.1 u j hj) (up hCdle (loss_bound_nonneg _))`. Establish `L4 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HComp (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)`. Apply `M.data_HComp hx1` to reduce the goal to its premises. Introduce `u0 u u'`. Conclude with `le_trans ((hDu u0).2.2.2.2.2.2.2.2 u u') (up hCdle (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sc_a_pos _).le) (hLau u0)) (mul_nonneg (Nat.cast_nonneg _) (loss_bound_nonneg _))))`.

Establish `L5 : Count5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)` using `M.data_Count5 hx1 _ _ _ _ _ _ _ (fun u0 => hC x hxC (M.pt u0))`. Establish `L6 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).Slopes (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)` using `M.data_Slopes hx1 _ _ _ _ _ _ _ (fun u0 => hS x hxS (M.pt u0))`. Establish `L7 : QuotientSlopeBoundsWith (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n)` using `M.model_slopes_five hx1 _ _ _ _ _ _ _ (fun u0 => hN x hxN (M.pt u0))`. Establish `L8 : LossBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)`. Introduce `u0`.

Take `⟨hio, hask⟩` from `hloss (M.pt u0) (M.pt_w u0)`. Establish `h1` using `hask M.e M.m M.AD ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.a (M.w u0) (M.reads u0) (M.hAD u0) (hcut u0)`. Rewrite `h1`, `hio` using `[M.s_card u0, M.s_m u0, M.s_sc hx1 u0, M.s_x hx1, M.s_eps]`. Conclude with `⟨h1, hio⟩`. Establish `liftZP_newton : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).SlopeIneq` using `M.data_SlopeIneq _ _ _ _ _ _ hfr`.

Establish `ParameterUpperBound : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HHBound (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)` using `M.data_HHBound hx1 _ _ _ _ _ _ _ rfl (fun u0 => (hDu u0).2.1) (fun u0 => (hL x hxL (M.pt u0)).2)`. Establish `liftZP_unit : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).FParams` using `fun u0 => ⟨(hI x hxI (M.pt u0)).1, (hI x hxI (M.pt u0)).2, hηv0 u0, hηvB u0, hev0 u0, hevB u0⟩`. Establish `hK6 : (6 : ℝ) ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`. Establish `k1 : max Cd 0 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`. Establish `k2 : Cc ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`.

Establish `k3 : Cs ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`. Establish `k4 : C1 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`. Establish `k5 : Cl ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6` using `by linarith`. Establish `E0 : ErrWindows0 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6)` using `⟨hx1', heps, heps1, hb1, le_of_eq hab.symm, hnT, w1, w2, heK, hk1, w3, w4, (by show 0 ≤ (Fm.L x i0).sc.L; rw [hLx]; linarith), (by show (Fm.L x i0).sc.L ≤ 2 * x ^ eps; rw [hLx]; linarith), w5, w6, hb'0.le, w7, hXpp0, w8, fun τ => ⟨le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1, ( …`. Establish `h` using `(hWu u0).2.2.2.2.2.2.2.2.2.1`.

Rewrite `h` using `[M.s_k u0]`. Conclude with `h,`. Use `exp_neg_le_half (Real.one_le_rpow hx1' (by positivity : 0 ≤ Fm.ez / 7)), hη0, he0,`. Use the proof step `⟨hCd', k1, hCd', k1, hCd', k1, hCc, k2, hCs, k3, hC1, k4, hCl, k5, hCabs, heL, hCH⟩⟩`. Establish `E1 : ErrWindows (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6)`.

Use `⟨E0, ?_⟩` and prove the remaining obligations. Use `show (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps * ((Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a)`. Establish `s1 : (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤ 6 * (Fm.L x i0).sc.b`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right h6 hb0.le`.

Establish `s2 : (Fm.L x i0).sc.b ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a`. Rewrite using `[hab]`. Combine the equalities or inequalities in the displayed calculation. Establish `s3 : (6 : ℝ) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hcardH : (Fintype.card M.e.A : ℝ) = ((Fm.D x i0).R.n : ℝ)` using `by rw [card_HA]; rfl`. Establish `B1 : BNBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) M.T2`. Prove the components needed by the constructor for the conclusion. Apply `le_of_eq show (Fm.L x i0).B0 = (2 * (Fintype.card M.e.A : ℝ)) * (M.m : ℝ) * (Fm.L x i0).sc.b * x ^ eps` to reduce the goal to its premises.

Rewrite using `[hcardH]`. Unfold `SizeData₂.B0 sizeBudget bSize Scale.b Scale.L Ranks.f`. Rewrite using `[hsx, hse]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Apply `le_of_eq show (Fm.L x i0).Nc = (M.T2.card : ℝ) * ((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.b * x ^ eps / ((Fintype.card M.e.A : ℝ) * ((Fintype.card M.e.A : ℝ) * x ^ (-eps)))` to reduce the goal to its premises. Rewrite using `[hcardH, M.card_thick_set_model_eq]`. Unfold `SizeData₂.Nc budgetNc rankBudget bSize Scale.b Scale.L`. Rewrite using `[hsx, hse]`. Establish `R1 : GrowthInequalityRemainingHyps M.AD ell ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.T2 M.a M.w x eps (Fm.L x i0).sc.b (Fm.L x i0).sc.b' (Fm.L x i0).etaSz (Fm.L x i0).sc.X' (Real.exp (-(c6 * x ^ (eps / 8)))) C5` using `⟨⟨(Fm.L x i0).etaSz_pos.le, Real.exp_pos _, hb'0, le_of_eq (by rw [← hab]; exact div_mul_cancel₀ _ (Real.exp_pos _).ne'), (Real.exp_pos _).le, fun t ht => (M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)).2.2, ⟨fun u0 j ρ hρ => lt_of_lt_of_le one_pos ((hnod u0).1 j ρ hρ), fun u0 j ρ …`.

Establish `h` using `(hnod u0).2.1 j ρ hρ`. Rewrite `h` using `[M.s_sc hx1 u0, Fm.eta_eq x (M.pt u0) M.i0]`. Conclude with `h,`. Use `fun u0 j ρ hρ hρ' => by`. Establish `h` using `(hnod u0).2.2 j ρ hρ hρ'`.

Rewrite `h` using `[M.s_sc hx1 u0]`. Conclude with `h⟩,`. Use `fun u0 j t ρ ht hρ => hcut u0 j t ρ ht hρ⟩,`. Use `by rw [hX']; exact hell3 (hTh x hxTh i0), hell4 (hQD x hxQD i0)⟩`. Establish `W1 : CostWindows x (fPl M.e.A) (Fm.L x i0).sc.b (Fm.L x i0).etaSz (Real.exp (-(c6 * x ^ (eps / 8))))`.

Rewrite using `[M.fPl_eq]`. Conclude with `⟨w11, w12⟩`. Establish `S1 : RestSize eps x (Fintype.card M.e.A) M.TT.card M.T2.card M.m (Fm.L x i0).sc.b ((Fm.D x i0).R.k : ℝ) (Fm.L x i0).sc.a`. Establish `h1` using `(hTT x hxTT i0).1`. Unfold `Scale.delta1 at h1`.

Rewrite `h1` using `[hsx, hse, card_TT Fm x i0, ← M.card_TT']`. Use `⟨by rw [hab]; have := mul_pos hx0 hb0; linarith, ?_, ?_, w13, ?_⟩` and prove the remaining obligations. Rewrite using `[hcardH]`. Conclude with `h1`. Rewrite using `[hcardH, M.card_thick_set_model_eq]`.

Conclude with `w15`. Rewrite using `[hcardH]`. Conclude with `w14`. Conclude with `⟨i0, M.m, M.f, M.pt, av, bv, ↥(Fm.TTn x), inferInstance, M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev, mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH, (Fm.L x i0).sc.X'' (Fm.D x i0).R.n, ell, ⌈2 * (Fm.L x i0).sc.a⌉₊, M.TT, M.T2, M.a, M.w, M.eT, M.eP, (Fm.L x i0).etaSz, (Fm.L x i0).sc.X …`.
-/
theorem linkCore (Fm : FamP eps) (Cabs CH eL C5 c6 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 ≤ CH) (heL : 0 ≤ eL) (hc6 : 0 < c6)
    (hCount : CountF Fm) (hSM : SlopesMF Fm) (hSN : SlopesNF Fm) (hLat : LatF Fm) (hNodes : NodesF Fm)
    (hFr : FrameF Fm CH) (hLoss : LossFS Fm eL) (hChar : CharF Fm) (hWin : WinF Fm)
    (cTT : ChosenTT Fm) (cQD : ChosenQD Fm C5) (cTh : ChosenThin Fm c6) (lI : LinkIRR Fm) (lD : LinkDIV Fm Cabs CH) :
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm Cabs eL K cHH eK CL x := by
  obtain ⟨xQD, hQD⟩ := cQD
  obtain ⟨xTh, hTh⟩ := cTh
  obtain ⟨Cc, xC, hCc, hC⟩ := hCount
  obtain ⟨Cs, xS, hCs, hS⟩ := hSM
  obtain ⟨C1, xN, hC1, hN⟩ := hSN
  obtain ⟨xL, hL⟩ := hLat
  obtain ⟨xO, hO⟩ := hNodes
  obtain ⟨xF, hF⟩ := hFr
  obtain ⟨Cl, xLo, hCl, hLo⟩ := hLoss
  obtain ⟨xCh, hChr⟩ := hChar c6 C5
  obtain ⟨eK, xW, heK, hW⟩ := hWin c6 hc6
  obtain ⟨xTT, hTT⟩ := cTT
  obtain ⟨xI, hI⟩ := lI
  obtain ⟨Cd, xD, hD⟩ := lD
  have hCd' : (0 : ℝ) ≤ max Cd 0 := le_max_right _ _
  have hCdle : Cd ≤ max Cd 0 := le_max_left _ _
  refine ⟨max Cd 0 + Cc + Cs + C1 + Cl + 6, CH, eK, C5,
    Fm.x1 + 1 + |xQD| + |xTh| + |xC| + |xS| + |xN| + |xL| + |xO| + |xF| + |xLo| + |xCh| + |xW| + |xTT| + |xI| + |xD|,
    fun x hx hxw => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have habs : 0 ≤ |xQD| ∧ 0 ≤ |xTh| ∧ 0 ≤ |xC| ∧ 0 ≤ |xS| ∧ 0 ≤ |xN| ∧ 0 ≤ |xL| ∧ 0 ≤ |xO| ∧ 0 ≤ |xF| ∧ 0 ≤ |xLo| ∧
      0 ≤ |xCh| ∧ 0 ≤ |xW| ∧ 0 ≤ |xTT| ∧ 0 ≤ |xI| ∧ 0 ≤ |xD| :=
    ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _,
      abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := habs
  have hx1 : Fm.x1 < x := by linarith
  have hxQD : x ≥ xQD := by linarith [le_abs_self xQD]
  have hxTh : x ≥ xTh := by linarith [le_abs_self xTh]
  have hxC : x ≥ xC := by linarith [le_abs_self xC]
  have hxS : x ≥ xS := by linarith [le_abs_self xS]
  have hxN : x ≥ xN := by linarith [le_abs_self xN]
  have hxL : x ≥ xL := by linarith [le_abs_self xL]
  have hxO : x ≥ xO := by linarith [le_abs_self xO]
  have hxF : x ≥ xF := by linarith [le_abs_self xF]
  have hxLo : x ≥ xLo := by linarith [le_abs_self xLo]
  have hxCh : x ≥ xCh := by linarith [le_abs_self xCh]
  have hxW : x ≥ xW := by linarith [le_abs_self xW]
  have hxTT : x ≥ xTT := by linarith [le_abs_self xTT]
  have hxI : x ≥ xI := by linarith [le_abs_self xI]
  have hxD : x ≥ xD := by linarith [le_abs_self xD]
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith

  obtain ⟨i0, av, bv, hadm, ⟨i1, hc1⟩, hloss⟩ := hLo x hxLo hxw
  have hcov : ∀ u0 : (Fm.D x i0).R.A, ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = hval _ u0 ∧
      ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val :=
    fun u0 => Fm.coverS_carry x hx1 i1 av bv hc1 (hval _ u0) (by rw [Fm.R_eq x i1 i0]; exact hval_lt _ u0)
  choose pt hpt1 hpt2 using hcov
  let M : Mod Fm x := ⟨i0, av, bv, pt, hpt1, hpt2⟩
  have iq : Fact M.q.Prime := ⟨(Fm.D x i0).host.hyp.1⟩
  have id : Fact M.d.Prime := ⟨(Fm.D x i0).host.hyp.2.1⟩

  obtain ⟨etaB, eB, hη0, he0, he4, h6, hFa⟩ := hF x hxF
  have hFa' : ∀ u0 : M.e.A, Frame_at (Fm.D x (M.pt u0)) etaB eB := fun u0 => hFa (M.pt u0)
  unfold Frame_at at hFa'
  choose ηv ev hηv0 hηvB hev0 hevB hfr using hFa'

  obtain ⟨ell, hell1, hell2, hell3, hell4⟩ := hChr x hxCh i0 M.e M.AD rfl HEq.rfl

  have heps : 0 < eps := by have h := (Fm.L x i0).sc.eps_pos; rwa [Fm.L_eps] at h
  have hez : 0 < Fm.ez := div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)
  have heps1 : eps ≤ 1 := by have h := (Fm.L x i0).sc.eps_lt; rw [Fm.L_eps] at h; linarith
  have hsx : (Fm.L x i0).sc.x = x := Fm.L_x x i0 hx1
  have hse : (Fm.L x i0).sc.eps = eps := Fm.L_eps x i0
  have hWu : ∀ u0 : M.e.A, Win_at (Fm.L x (M.pt u0)) eK c6 := fun u0 => hW x hxW (M.pt u0)
  have hW0 := hW x hxW i0
  unfold Win_at at hW0
  rw [hsx, hse] at hW0
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, -, -, w11, w12, w13, w14, w15, -, w17⟩ := hW0
  have ha0 := sc_a_pos (Fm.L x i0).sc
  have hb'0 := sc_b'_pos (Fm.L x i0).sc
  have hb0 : 0 < (Fm.L x i0).sc.b := Real.exp_pos _
  have hab : (Fm.L x i0).sc.a = x * (Fm.L x i0).sc.b := by
    show (Fm.L x i0).sc.x * (Fm.L x i0).sc.b = _
    rw [hsx]
  have hLx : (Fm.L x i0).sc.L = x ^ eps := by
    show (Fm.L x i0).sc.x ^ (Fm.L x i0).sc.eps = _
    rw [hsx, hse]
  have hxe : 1 ≤ x ^ eps := Real.one_le_rpow hx1' heps.le
  have hb1 : 1 ≤ (Fm.L x i0).sc.b := by
    show 1 ≤ Real.exp (Fm.L x i0).sc.L
    rw [hLx]; exact Real.one_le_exp (by linarith)
  have hk5 := (Fm.D x i0).R.k_ge
  have hk1 : (1 : ℝ) ≤ ((Fm.D x i0).R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ (Fm.D x i0).R.k)
  have hnod := fun u0 : M.e.A => hO x hxO (M.pt u0) M.e M.m M.T2 u0 (M.w u0) (M.he u0) (M.hm u0)
    (fun h => by rw [M.mem_thick_set_model_iff, Fm.realisedChain_torus_eq x M.i0 (M.pt u0)]) (M.point_base_value u0) (M.w_tie u0) (M.w_off u0)
  have hcut : ∀ (u0 : M.e.A) (j : Fin M.m) (t : M.e.A) (ρ : E0 × M.e.A), t ∈ M.TT → InPhi ρ →
      M.a t / M.w u0 j ρ ≤ (⌈2 * (Fm.L x i0).sc.a⌉₊ : ℝ) := by
    intro u0 j t ρ ht hρ
    obtain ⟨ha1, ha2, -⟩ := M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)
    have hw1 := (hnod u0).1 j ρ hρ
    have hat : 0 ≤ M.a t := le_trans ha0.le ha1
    calc M.a t / M.w u0 j ρ ≤ M.a t := div_le_self hat hw1
      _ ≤ 2 * (Fm.L x i0).sc.a := ha2
      _ ≤ _ := Nat.le_ceil _
  have hDu := fun u0 : M.e.A => hD x hxD (M.pt u0)
  have hLau : ∀ u0 : M.e.A, 0 ≤ (Fm.L x (M.pt u0)).La := fun u0 => (hWu u0).2.2.2.2.1
  have hnT : (1 : ℝ) ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) := by
    have h1 := (hTT x hxTT i0).1
    have hd : 0 < (Fm.L x i0).sc.delta1 := by
      unfold Scale.delta1; rw [hsx]; exact Real.rpow_pos_of_pos hx0 _
    have hn : (0 : ℝ) < ((Fm.D x i0).R.n : ℝ) := by
      have : 0 < (Fm.D x i0).R.n := (Fm.D x i0).R.toFrame.ord_pos
      exact_mod_cast this
    have h2 : (0 : ℝ) < ((Fm.D x i0).host.TT.card : ℝ) := lt_of_lt_of_le (by positivity) h1
    rw [card_TT Fm x i0] at h2
    exact_mod_cast Nat.succ_le_of_lt (Nat.cast_pos.mp h2)
  have hXpp0 : 0 ≤ (Fm.L x i0).sc.X'' (Fm.D x i0).R.n := by
    unfold Scale.X'' Scale.w''
    exact div_nonneg ha0.le (div_nonneg hb'0.le (mul_nonneg (by rw [hsx]; exact hx0.le) (Nat.cast_nonneg _)))
  have hX' : (Fm.L x i0).sc.X' = Real.exp (x ^ (eps / 3)) := by
    show Real.exp ((Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3)) = _
    rw [hsx, hse]

  have L1 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HidaSetting (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    ⟨hx0, hb0, ha0.le, hb'0.le, lt_of_lt_of_le one_pos hk1, w17, Nat.mul_pos two_pos (Fm.D x i0).R.toFrame.ord_pos,
      fun τ => le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1,
      fun u0 j ρ => lt_of_lt_of_le one_pos ((hnod u0).1 j _ (Finset.mem_filter.mp (M.eP ρ).2).2),
      fun u0 u => Nat.cast_pos.mpr ((hL x hxL (M.pt u0)).1 u).1,
      fun u0 u => Nat.cast_pos.mpr ((Fm.D x (M.pt u0)).mem u).A.T_prime.pos,
      fun u0 u => ((hL x hxL (M.pt u0)).1 u).2, hC1,
      (by
        have h := Real.exp_lt_exp.mpr (show -(x ^ (Fm.ez / 7)) < 0 by
          have := Real.rpow_pos_of_pos hx0 (Fm.ez / 7); linarith)
        rwa [Real.exp_zero] at h), hη0, he0, he4⟩
  have L2 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).DIV (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_DIV hx1
    intro u0 u
    have h := (hDu u0).2.2.2.2.2.2.1 u
    have hX1 : 0 ≤ ((Fm.D x (M.pt u0)).host.TT.card : ℝ) * ((Fm.L x (M.pt u0)).sc.a * (Fm.L x (M.pt u0)).La) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sc_a_pos _).le (hLau u0))
    have hX2 : 0 ≤ ((Fm.D x (M.pt u0)).R.m : ℝ) * (((Fm.L x (M.pt u0)).B0 + (Fm.L x (M.pt u0)).Nc) *
        (Fm.L x (M.pt u0)).sc.x ^ (Cabs * (Fm.L x (M.pt u0)).sc.eps)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (add_nonneg (loss_bound_nonneg _) (Nc_nonneg _))
        (Real.rpow_nonneg (lt_trans one_pos (Fm.L x (M.pt u0)).sc.one_lt_alt).le _))
    have e1 := up hCdle hX1
    have e2 := up hCdle hX2
    show _ ≤ _ + max Cd 0 * _ * _ * _ + max Cd 0 * _ * _ * _ ^ (Cabs * _)
    simp only [mul_assoc] at h e1 e2 ⊢
    linarith
  have L3 : EComp5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_EComp5 hx1
    intro u0 u j hj
    exact le_trans ((hDu u0).2.2.2.2.2.2.2.1 u j hj) (up hCdle (loss_bound_nonneg _))
  have L4 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HComp (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_HComp hx1
    intro u0 u u'
    exact le_trans ((hDu u0).2.2.2.2.2.2.2.2 u u') (up hCdle (add_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sc_a_pos _).le) (hLau u0))
      (mul_nonneg (Nat.cast_nonneg _) (loss_bound_nonneg _))))
  have L5 : Count5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_Count5 hx1 _ _ _ _ _ _ _ (fun u0 => hC x hxC (M.pt u0))
  have L6 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).Slopes (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_Slopes hx1 _ _ _ _ _ _ _ (fun u0 => hS x hxS (M.pt u0))
  have L7 : QuotientSlopeBoundsWith (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) :=
    M.model_slopes_five hx1 _ _ _ _ _ _ _ (fun u0 => hN x hxN (M.pt u0))
  have L8 : LossBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    intro u0
    obtain ⟨hio, hask⟩ := hloss (M.pt u0) (M.pt_w u0)
    have h1 := hask M.e M.m M.AD ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.a (M.w u0) (M.reads u0) (M.hAD u0) (hcut u0)
    rw [M.s_card u0, M.s_m u0, M.s_sc hx1 u0, M.s_x hx1, M.s_eps] at h1 hio
    exact ⟨h1, hio⟩
  have liftZP_newton : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).SlopeIneq := M.data_SlopeIneq _ _ _ _ _ _ hfr
  have ParameterUpperBound : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HHBound (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_HHBound hx1 _ _ _ _ _ _ _ rfl (fun u0 => (hDu u0).2.1) (fun u0 => (hL x hxL (M.pt u0)).2)
  have liftZP_unit : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).FParams := fun u0 =>
    ⟨(hI x hxI (M.pt u0)).1, (hI x hxI (M.pt u0)).2, hηv0 u0, hηvB u0, hev0 u0, hevB u0⟩

  have hK6 : (6 : ℝ) ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k1 : max Cd 0 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k2 : Cc ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k3 : Cs ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k4 : C1 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k5 : Cl ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have E0 : ErrWindows0 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6) :=
    ⟨hx1', heps, heps1, hb1, le_of_eq hab.symm, hnT, w1, w2, heK, hk1, w3, w4, (by show 0 ≤ (Fm.L x i0).sc.L; rw [hLx]; linarith),
      (by show (Fm.L x i0).sc.L ≤ 2 * x ^ eps; rw [hLx]; linarith), w5, w6, hb'0.le, w7, hXpp0, w8,
      fun τ => ⟨le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1, (M.av_facts hx1 (hWu 0) τ.2).2.1⟩,
      loss_bound_nonneg _, Nc_nonneg _,
      fun u0 => by
        have h := (hWu u0).2.2.2.2.2.2.2.2.2.1
        rw [M.s_k u0] at h
        exact h,
      exp_neg_le_half (Real.one_le_rpow hx1' (by positivity : 0 ≤ Fm.ez / 7)), hη0, he0,
      ⟨hCd', k1, hCd', k1, hCd', k1, hCc, k2, hCs, k3, hC1, k4, hCl, k5, hCabs, heL, hCH⟩⟩
  have E1 : ErrWindows (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6) := by
    refine ⟨E0, ?_⟩
    show (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤
      (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps * ((Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a)
    have s1 : (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤ 6 * (Fm.L x i0).sc.b := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h6 hb0.le
    have s2 : (Fm.L x i0).sc.b ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a := by
      rw [hab]
      calc (Fm.L x i0).sc.b = 1 * (1 * (Fm.L x i0).sc.b) := by ring
        _ ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) * (x * (Fm.L x i0).sc.b) :=
          mul_le_mul hnT (mul_le_mul_of_nonneg_right hx1' hb0.le) (by linarith) (by linarith)
    have s3 : (6 : ℝ) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps :=
      calc (6 : ℝ) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * 1 := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hxe (by linarith)
    calc _ ≤ 6 * (Fm.L x i0).sc.b := s1
      _ ≤ 6 * ((Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right s3 (by positivity)
  have hcardH : (Fintype.card M.e.A : ℝ) = ((Fm.D x i0).R.n : ℝ) := by rw [card_HA]; rfl
  have B1 : BNBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) M.T2 := by
    constructor
    · apply le_of_eq
      show (Fm.L x i0).B0 = (2 * (Fintype.card M.e.A : ℝ)) * (M.m : ℝ) * (Fm.L x i0).sc.b * x ^ eps
      rw [hcardH]
      unfold SizeData₂.B0 sizeBudget bSize Scale.b Scale.L Ranks.f
      rw [hsx, hse]; push_cast; ring
    · apply le_of_eq
      show (Fm.L x i0).Nc = (M.T2.card : ℝ) * ((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.b * x ^ eps /
        ((Fintype.card M.e.A : ℝ) * ((Fintype.card M.e.A : ℝ) * x ^ (-eps)))
      rw [hcardH, M.card_thick_set_model_eq]
      unfold SizeData₂.Nc budgetNc rankBudget bSize Scale.b Scale.L
      rw [hsx, hse]
  have R1 : GrowthInequalityRemainingHyps M.AD ell ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.T2 M.a M.w x eps (Fm.L x i0).sc.b
      (Fm.L x i0).sc.b' (Fm.L x i0).etaSz (Fm.L x i0).sc.X' (Real.exp (-(c6 * x ^ (eps / 8)))) C5 :=
    ⟨⟨(Fm.L x i0).etaSz_pos.le, Real.exp_pos _, hb'0,
      le_of_eq (by rw [← hab]; exact div_mul_cancel₀ _ (Real.exp_pos _).ne'), (Real.exp_pos _).le,
      fun t ht => (M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)).2.2,
      ⟨fun u0 j ρ hρ => lt_of_lt_of_le one_pos ((hnod u0).1 j ρ hρ),
        fun u0 j ρ hρ => by
          have h := (hnod u0).2.1 j ρ hρ
          rw [M.s_sc hx1 u0, Fm.eta_eq x (M.pt u0) M.i0] at h
          exact h,
        fun u0 j ρ hρ hρ' => by
          have h := (hnod u0).2.2 j ρ hρ hρ'
          rw [M.s_sc hx1 u0] at h
          exact h⟩,
      fun u0 j t ρ ht hρ => hcut u0 j t ρ ht hρ⟩,
      by rw [hX']; exact hell3 (hTh x hxTh i0), hell4 (hQD x hxQD i0)⟩
  have W1 : CostWindows x (fPl M.e.A) (Fm.L x i0).sc.b (Fm.L x i0).etaSz (Real.exp (-(c6 * x ^ (eps / 8)))) := by
    rw [M.fPl_eq]; exact ⟨w11, w12⟩
  have S1 : RestSize eps x (Fintype.card M.e.A) M.TT.card M.T2.card M.m (Fm.L x i0).sc.b
      ((Fm.D x i0).R.k : ℝ) (Fm.L x i0).sc.a := by
    have h1 := (hTT x hxTT i0).1
    unfold Scale.delta1 at h1
    rw [hsx, hse, card_TT Fm x i0, ← M.card_TT'] at h1
    refine ⟨by rw [hab]; have := mul_pos hx0 hb0; linarith, ?_, ?_, w13, ?_⟩
    · rw [hcardH]; exact h1
    · rw [hcardH, M.card_thick_set_model_eq]; exact w15
    · rw [hcardH]; exact w14
  exact ⟨i0, M.m, M.f, M.pt, av, bv, ↥(Fm.TTn x), inferInstance,
    M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev, mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH,
    (Fm.L x i0).sc.X'' (Fm.D x i0).R.n, ell, ⌈2 * (Fm.L x i0).sc.a⌉₊, M.TT, M.T2, M.a, M.w, M.eT, M.eP,
    (Fm.L x i0).etaSz, (Fm.L x i0).sc.X', Real.exp (-(c6 * x ^ (eps / 8))),
    M.tiePts, M.tieGlobal hx1 _ _ _ _ _ _, M.tieLocal _ _ _ _ _ _, M.tieArith ell hell1, rfl, rfl, le_refl _, le_refl _,
    le_refl _, M.ident _ _ _ _ _ _ ell hell2,
    ⟨L1, L2, L3, L4, L5, L6, L7, L8, liftZP_newton, ParameterUpperBound, liftZP_unit⟩, E1, B1, R1, W1, S1⟩

def LossesSmallShares (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, ChW_at (Fm.Gx x i) Fm.GK → Loss_at (Fm.L x i) C 0

/- English proof (translation)
Take `⟨C, x0, hC, hL⟩` from `h`. Take `⟨x1, hW⟩` from `hW`. Use `⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩` and prove the remaining obligations. Take `⟨i0, av, bv, h1, h3⟩` from `hW x (le_of_max_le_right hx) hwin`. Conclude with `⟨i0, av, bv, h1, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩`.
-/
theorem lossF_of_7W (Fm : FamP eps) (h : LossesSmallShares Fm) (hW : ChosenW Fm) : LossF Fm 0 := by
  obtain ⟨C, x0, hC, hL⟩ := h
  obtain ⟨x1, hW⟩ := hW
  refine ⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h3⟩ := hW x (le_of_max_le_right hx) hwin
  exact ⟨i0, av, bv, h1, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩

/- English proof (translation)
Take `⟨C, x0, hC, hL⟩` from `h`. Take `⟨x1, hW⟩` from `hW`. Use `⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩` and prove the remaining obligations. Take `⟨i0, av, bv, h1, h2, h3⟩` from `hW x (le_of_max_le_right hx) hwin`. Conclude with `⟨i0, av, bv, h1, h2, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩`.
-/
theorem lossF_of_7 (Fm : FamP eps) (h : LossesSmallShares Fm) (hW : ChosenWS Fm) : LossFS Fm 0 := by
  obtain ⟨C, x0, hC, hL⟩ := h
  obtain ⟨x1, hW⟩ := hW
  refine ⟨C, max x0 x1, hC, fun x hx hwin => ?_⟩
  obtain ⟨i0, av, bv, h1, h2, h3⟩ := hW x (le_of_max_le_right hx) hwin
  exact ⟨i0, av, bv, h1, h2, fun i hi => hL x (le_of_max_le_left hx) i (h3 i hi)⟩

/- English proof (translation)
Introduce `c6 hc6`. Establish `h0 : 0 < eps` using `fam_eps_pos Fm`. Take `⟨aT, hT2⟩` from `hT2`. Take `⟨a1, h1⟩` from `ev_pow_le_exp 1 (eps / 3) 5 one_pos (by positivity)`. Take `⟨a3, h3⟩` from `ev_pow_le_exp c6 (eps / 8) 7 hc6 (by positivity)`.

Take `⟨a4, h4⟩` from `ev_pow_le_exp 1 eps 9 one_pos h0`. Take `⟨a5, h5⟩` from `ev_pow_le_exp (1 / 2) eps 5 (by norm_num) h0`. Take `⟨a6, h6⟩` from `ev_two_le_rpow (eps - (eps / 5 + eps / 100)) (by linarith)`. Use `⟨5, Fm.x1 + 3 + |a1| + |a3| + |a4| + |a5| + |a6| + |aT|, by norm_num, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hpos` using `Fm.one_lt_family_threshold`.

Establish `n1` using `abs_nonneg a1`. Establish `n3` using `abs_nonneg a3`. Establish `n4` using `abs_nonneg a4`. Establish `n5` using `abs_nonneg a5`. Establish `n6` using `abs_nonneg a6`.

Establish `nT` using `abs_nonneg aT`. Establish `hx1 : Fm.x1 < x` using `by linarith`. Establish `hx3 : 3 ≤ x` using `by linarith`. Establish `hone : 1 ≤ x` using `by linarith`. Establish `b1 : x ≥ a1` using `by linarith [le_abs_self a1]`.

Establish `b3 : x ≥ a3` using `by linarith [le_abs_self a3]`. Establish `b4 : x ≥ a4` using `by linarith [le_abs_self a4]`. Establish `b5 : x ≥ a5` using `by linarith [le_abs_self a5]`. Establish `b6 : x ≥ a6` using `by linarith [le_abs_self a6]`. Establish `bT : x ≥ aT` using `by linarith [le_abs_self aT]`.

Establish `hsx` using `Fm.L_x x i hx1`. Establish `hse` using `Fm.L_eps x i`. Establish `hX : XL (Fm.L x i).sc c6`. Unfold `XL`. Rewrite using `[hsx, hse]`.

Conclude with `⟨hx3, h1 x b1 hone, h3 x b3 hone, h4 x b4 hone, h5 x b5 hone, h6 x b6⟩`. Establish `hS` using `Fm.sizes x hx1 i`. Establish `hNum` using `numN_at (Fm.params x hx1 i) hS (by rw [hsx]; exact hx3)`. Take `⟨sN, sM, sK, -, -, -, sQD, -⟩` from `hS`. Establish `hLa` using `winE sN sQD hX.1 hX.2.2.2.2.1 hX.2.2.2.2.2`.

Conclude with `size_window_at_five (Fm.params x hx1 i) sN sM sK hLa (winP sQD) hNum.1 (hT2 x bT i) c6 hX`.
-/
theorem size_windows_of_thick_density (Fm : FamP eps) (hT2 : ThickSetDensityEventually Fm) : WinF Fm := by
  intro c6 hc6
  have h0 : 0 < eps := fam_eps_pos Fm
  obtain ⟨aT, hT2⟩ := hT2
  obtain ⟨a1, h1⟩ := ev_pow_le_exp 1 (eps / 3) 5 one_pos (by positivity)
  obtain ⟨a3, h3⟩ := ev_pow_le_exp c6 (eps / 8) 7 hc6 (by positivity)
  obtain ⟨a4, h4⟩ := ev_pow_le_exp 1 eps 9 one_pos h0
  obtain ⟨a5, h5⟩ := ev_pow_le_exp (1 / 2) eps 5 (by norm_num) h0
  obtain ⟨a6, h6⟩ := ev_two_le_rpow (eps - (eps / 5 + eps / 100)) (by linarith)
  refine ⟨5, Fm.x1 + 3 + |a1| + |a3| + |a4| + |a5| + |a6| + |aT|, by norm_num, fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have n1 := abs_nonneg a1
  have n3 := abs_nonneg a3
  have n4 := abs_nonneg a4
  have n5 := abs_nonneg a5
  have n6 := abs_nonneg a6
  have nT := abs_nonneg aT
  have hx1 : Fm.x1 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  have hone : 1 ≤ x := by linarith
  have b1 : x ≥ a1 := by linarith [le_abs_self a1]
  have b3 : x ≥ a3 := by linarith [le_abs_self a3]
  have b4 : x ≥ a4 := by linarith [le_abs_self a4]
  have b5 : x ≥ a5 := by linarith [le_abs_self a5]
  have b6 : x ≥ a6 := by linarith [le_abs_self a6]
  have bT : x ≥ aT := by linarith [le_abs_self aT]
  have hsx := Fm.L_x x i hx1
  have hse := Fm.L_eps x i
  have hX : XL (Fm.L x i).sc c6 := by
    unfold XL
    rw [hsx, hse]
    exact ⟨hx3, h1 x b1 hone, h3 x b3 hone, h4 x b4 hone, h5 x b5 hone, h6 x b6⟩
  have hS := Fm.sizes x hx1 i
  have hNum := numN_at (Fm.params x hx1 i) hS (by rw [hsx]; exact hx3)
  obtain ⟨sN, sM, sK, -, -, -, sQD, -⟩ := hS
  have hLa := winE sN sQD hX.1 hX.2.2.2.2.1 hX.2.2.2.2.2
  exact size_window_at_five (Fm.params x hx1 i) sN sM sK hLa (winP sQD) hNum.1 (hT2 x bT i) c6 hX

/- English proof (translation)
Take `⟨eK, x0, -, h⟩` from `size_windows_of_thick_set Fm hT2 1 one_pos`. Conclude with `⟨x0, fun x hx i => (h x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩`.
-/
theorem thick_density_of_construction (Fm : FamP eps) (hT2 : ThickSetEventually Fm) : ThickSetDensityEventually Fm := by
  obtain ⟨eK, x0, -, h⟩ := size_windows_of_thick_set Fm hT2 1 one_pos
  exact ⟨x0, fun x hx i => (h x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/- English proof (translation)
Establish `heps` using `fam_eps_pos Fm`. Take `⟨a0, cTT⟩` from `cTT`. Take `⟨a1, cBad⟩` from `cBad`. Take `⟨a2, -, h2⟩` from `ev_le_rpow (2 * eps / 3) (by positivity) (16 * Cb)`. Use `⟨Fm.x1 + 1 + |a0| + |a1| + |a2|, fun x hx i => ?_⟩` and prove the remaining obligations.

Establish `hpos` using `Fm.one_lt_family_threshold`. Establish `n0` using `abs_nonneg a0`. Establish `n1` using `abs_nonneg a1`. Establish `n2` using `abs_nonneg a2`. Establish `hx1 : Fm.x1 < x` using `by linarith`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hone : 1 ≤ x` using `by linarith`. Establish `b0 : x ≥ a0` using `by linarith [le_abs_self a0]`. Establish `b1 : x ≥ a1` using `by linarith [le_abs_self a1]`. Establish `b2 : a2 ≤ x` using `by linarith [le_abs_self a2]`.

Establish `hsx` using `Fm.L_x x i hx1`. Establish `hse` using `Fm.L_eps x i`. Establish `hT` using `(cTT x b0 i).1`. Establish `hB` using `cBad x b1 i`. Unfold `ChBad_at at hB`.

Unfold `ChBadp_at`. Establish `hX' : (Fm.L x i).sc.X' = Real.exp (x ^ (eps / 3))` using `by show Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) = _`. Rewrite using `[hsx, hse]`. Establish `hXone : 1 ≤ (Fm.L x i).sc.X'`. Rewrite using `[hX']`.

Conclude with `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `hM` using `Formalism.L2.GlobalTheoryTheory.Places.mertens (Fm.L x i).sc.X' hXone`. Establish `hsub : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ ∑ p ∈ (Finset.range ⌈(Fm.L x i).sc.X'⌉₊).filter Nat.Prime, Real.log p / p`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `p hp`.

Unfold `largeOrderResiduePrimes at hp`. Take `⟨h1, h2, -⟩` from `Finset.mem_filter.mp hp`. Conclude with `Finset.mem_filter.mpr ⟨h1, h2⟩`. Introduce `p _ _`. Conclude with `div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)`.

Establish `hS : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ 2 * x ^ (eps / 3)`. Use `le_trans hsub (le_trans hM ?_)` and prove the remaining obligations. Rewrite using `[hX', Real.log_exp]`. Rewrite `hB` using `[hsx]`. Rewrite using `[hsx, hse]`.

Establish `hx2 : 0 ≤ x ^ (-2 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Establish `hdn : (Fm.L x i).sc.delta1 * (Fm.D x i).R.n ≤ 2 * ((Fm.D x i).host.TT.card : ℝ)` using `by linarith`. Establish `hdn0 : 0 ≤ (Fm.L x i).sc.delta1 * (Fm.D x i).R.n`. Establish `: 0 ≤ (Fm.L x i).sc.delta1` using `by unfold Scale.delta1; exact Real.rpow_nonneg (by rw [hsx]; exact hx0.le) _`. Conclude with `mul_nonneg this (Nat.cast_nonneg _)`.

Establish `hc0 : (0 : ℝ) ≤ ((Fm.D x i).host.TT.card : ℝ)` using `Nat.cast_nonneg _`. Establish `hx3 : 0 ≤ x ^ (eps / 3)` using `Real.rpow_nonneg hx0.le _`. Establish `hS0 : 0 ≤ ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p` using `Finset.sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))`. Establish `step : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ ((Fm.D x i).host.TT.card : ℝ) * (x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)))`. Establish `e1 : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p = (4 * Cb * x ^ (-2 : ℝ)) * (((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p)` using `by ring`.

Establish `e2 : ((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ (2 * ((Fm.D x i).host.TT.card : ℝ)) * (2 * x ^ (eps / 3))` using `mul_le_mul hdn hS hS0 (by linarith)`. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hfin : x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)) ≤ x ^ (-2 + eps)`. Establish `h3 : (16 * Cb) * x ^ (eps / 3) ≤ x ^ (2 * eps / 3) * x ^ (eps / 3)` using `mul_le_mul_of_nonneg_right (h2 x b2) hx3`.

Rewrite `h3` using `[← Real.rpow_add hx0]`. Establish `h4 : 2 * eps / 3 + eps / 3 = eps` using `by ring`. Rewrite `h3` using `[h4]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_trans hB (le_trans step (mul_le_mul_of_nonneg_left hfin hc0))`.
-/
theorem chosenBadp_of_old (Fm : FamP eps) (Cb : ℝ) (hCb : 0 ≤ Cb) (cTT : ChosenTT Fm) (cBad : ChosenBad Fm Cb) :
    ChosenBadp Fm := by
  have heps := fam_eps_pos Fm
  obtain ⟨a0, cTT⟩ := cTT
  obtain ⟨a1, cBad⟩ := cBad
  obtain ⟨a2, -, h2⟩ := ev_le_rpow (2 * eps / 3) (by positivity) (16 * Cb)
  refine ⟨Fm.x1 + 1 + |a0| + |a1| + |a2|, fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have n0 := abs_nonneg a0
  have n1 := abs_nonneg a1
  have n2 := abs_nonneg a2
  have hx1 : Fm.x1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hone : 1 ≤ x := by linarith
  have b0 : x ≥ a0 := by linarith [le_abs_self a0]
  have b1 : x ≥ a1 := by linarith [le_abs_self a1]
  have b2 : a2 ≤ x := by linarith [le_abs_self a2]
  have hsx := Fm.L_x x i hx1
  have hse := Fm.L_eps x i
  have hT := (cTT x b0 i).1
  have hB := cBad x b1 i
  unfold ChBad_at at hB
  unfold ChBadp_at
  have hX' : (Fm.L x i).sc.X' = Real.exp (x ^ (eps / 3)) := by
    show Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) = _
    rw [hsx, hse]
  have hXone : 1 ≤ (Fm.L x i).sc.X' := by
    rw [hX']; exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hM := Formalism.L2.GlobalTheoryTheory.Places.mertens (Fm.L x i).sc.X' hXone
  have hsub : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
      ∑ p ∈ (Finset.range ⌈(Fm.L x i).sc.X'⌉₊).filter Nat.Prime, Real.log p / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      unfold largeOrderResiduePrimes at hp
      obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨h1, h2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hS : ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤ 2 * x ^ (eps / 3) := by
    refine le_trans hsub (le_trans hM ?_)
    rw [hX', Real.log_exp]
  rw [hsx] at hB
  rw [hsx, hse]
  have hx2 : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hdn : (Fm.L x i).sc.delta1 * (Fm.D x i).R.n ≤ 2 * ((Fm.D x i).host.TT.card : ℝ) := by linarith
  have hdn0 : 0 ≤ (Fm.L x i).sc.delta1 * (Fm.D x i).R.n := by
    have : 0 ≤ (Fm.L x i).sc.delta1 := by unfold Scale.delta1; exact Real.rpow_nonneg (by rw [hsx]; exact hx0.le) _
    exact mul_nonneg this (Nat.cast_nonneg _)
  have hc0 : (0 : ℝ) ≤ ((Fm.D x i).host.TT.card : ℝ) := Nat.cast_nonneg _
  have hx3 : 0 ≤ x ^ (eps / 3) := Real.rpow_nonneg hx0.le _
  have hS0 : 0 ≤ ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p :=
    Finset.sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have step : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n *
      ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
      ((Fm.D x i).host.TT.card : ℝ) * (x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3))) := by
    have e1 : 4 * (Cb * x ^ (-2 : ℝ)) * (Fm.L x i).sc.delta1 * (Fm.D x i).R.n *
        ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p =
        (4 * Cb * x ^ (-2 : ℝ)) * (((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) *
          ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p) := by ring
    have e2 : ((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) * ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p ≤
        (2 * ((Fm.D x i).host.TT.card : ℝ)) * (2 * x ^ (eps / 3)) :=
      mul_le_mul hdn hS hS0 (by linarith)
    rw [e1]
    calc (4 * Cb * x ^ (-2 : ℝ)) * (((Fm.L x i).sc.delta1 * (Fm.D x i).R.n) *
          ∑ p ∈ largeOrderResiduePrimes (Fm.L x i), Real.log p / p)
        ≤ (4 * Cb * x ^ (-2 : ℝ)) * ((2 * ((Fm.D x i).host.TT.card : ℝ)) * (2 * x ^ (eps / 3))) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  have hfin : x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)) ≤ x ^ (-2 + eps) := by
    have h3 : (16 * Cb) * x ^ (eps / 3) ≤ x ^ (2 * eps / 3) * x ^ (eps / 3) :=
      mul_le_mul_of_nonneg_right (h2 x b2) hx3
    rw [← Real.rpow_add hx0] at h3
    have h4 : 2 * eps / 3 + eps / 3 = eps := by ring
    rw [h4] at h3
    calc x ^ (-2 : ℝ) * ((16 * Cb) * x ^ (eps / 3)) ≤ x ^ (-2 : ℝ) * x ^ eps := mul_le_mul_of_nonneg_left h3 hx2
      _ = x ^ (-2 + eps) := (Real.rpow_add hx0 _ _).symm
  exact le_trans hB (le_trans step (mul_le_mul_of_nonneg_left hfin hc0))

/- English proof (translation)
Take `⟨a3, hP⟩` from `cPr`. Take `⟨a0, hN⟩` from `hN`. Take `⟨a1, h10⟩` from `h10`. Take `⟨a2, hS⟩` from `hS`. Use `⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩` and prove the remaining obligations.

Establish `b0 : a0 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `b1 : a1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `b2 : a2 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `b3 : a3 ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `b4 : Fm.x1 < x`.

Use `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSet` using `hS x b2 b4 i u`. Establish `h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du` using `(hN x b0 i).rank u`. Rewrite using `[h1]`.

Conclude with `GlobalTheoryTheory.jnt_du_pos _ u (h10 x b1 i u hSet).2.1 (GlobalTheoryTheory.jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u) (GlobalTheoryTheory.two_lt_level_prime _ u hSet)`.
-/
theorem muRank_of_proviso (Fm : FamP eps) {C0 : ℝ} (crystallineComparison : ℝ) (hC0 : 0 < C0)
    (cPr : ChosenProviso Fm C0) (hN : NuFullF Fm) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : GlobalTheoryTheory.SettingEventually Fm) :
    J.MuRank Fm := by
  obtain ⟨a3, hP⟩ := cPr
  obtain ⟨a0, hN⟩ := hN
  obtain ⟨a1, h10⟩ := h10
  obtain ⟨a2, hS⟩ := hS
  refine ⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have b0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b2 : a2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b3 : a3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b4 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  have hSet := hS x b2 b4 i u
  have h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du := (hN x b0 i).rank u
  rw [h1]
  exact GlobalTheoryTheory.jnt_du_pos _ u (h10 x b1 i u hSet).2.1 (GlobalTheoryTheory.jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u)
    (GlobalTheoryTheory.two_lt_level_prime _ u hSet)

end Formalism.MainNotions.Lnk

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

variable {eps : ℝ}

def LinkGLOBAL7 (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) : Prop :=
  WeightVectorSmallSharesSeven Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 →
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x

/- English proof (translation)
Introduce `hTu hCh hIn`. Take `⟨C5, c6, hC5, hc6, cT2, cTT, cBad, cW, cQD, cTh, cPr, cCo⟩` from `hCh`. Take `⟨lG, lS, lI, lD, lMu⟩` from `hIn`. Establish `h10` using `prvF_of_familyTheorem_ties_eventualIncidenceTransport Fm C3 crystallineComparison C22 s59 s22 s24 s10 hF3 tVol t10`. Establish `tSet : SettingEventually Fm` using `Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu`.

Establish `hNF : NuFullF Fm` using `nuFullF_of Fm (nuCommensF_of Fm crystallineComparison h10 tSet)`. Establish `hRank : J.MuRank Fm` using `muRank_of_proviso Fm crystallineComparison (by linarith) cPr hNF h10 tSet`. Establish `hRR : RRRankF Fm` using `rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD`. Take `⟨C₅, h59a⟩` from `UnusedSlot33.field_lemmas_except_seven`. Establish `h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅` using `fun x hx i => by`.

Take `⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩` from `h59a (Fm.D x i) (Fm.L x i).sc`. Conclude with `⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩`. Establish `h24` using `s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol`. Establish `h22 : TaylorLogMetric.ConclusionOnFamily Fm C22` using `s22 (fun x i => TaylorLogMetric.first_hypothesis_of_lifting _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))`. Establish `h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev` using `fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1`.

Establish `hCount : CountF Fm` using `countF_fam Fm h24.2.2.2.2.2.2.2`. Establish `hDl` using `dl_of_chosen Fm C5 cQD`. Establish `h23` using `s23 ⟨flipTwoThree.theta_norm_family_of_linked Fm C22 h22 tOm, flipTwoThree.theta_condition_family_of_linked Fm C22 tFree tTh, flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 h4p, flipTwoThree.injectivity_family_of_theorem Fm crystallineComparison h10 tSet, flipTwoThr …`. Establish `hSM : SlopesMF Fm` using `flipTwoThree.slopesMF_of_count_fam Fm h23.2.2.2.2.1 h23.2.2.2.2.2.1 hCount hDl tCV`. Establish `hSN : SlopesNF Fm` using `slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_of Fm crystallineComparison h10 tSet hTu hRank lG lMu)`.

Establish `hLat : LatF Fm` using `latF Fm lD hNF hRank hRR`. Establish `hFr : FrameF Fm CH` using `frameF_of Fm CH C0 hCH hC0 (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_of Fm crystallineComparison h10 tSet) (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) hLat cPr cCo hNF`. Conclude with `linkCore Fm Cabs CH 0 C5 c6 hCabs hCH.le le_rfl hc6 hCount hSM hSN hLat (nodesF Fm) hFr (lossF_of_7 Fm (hL7 cTT cBad lG) cW) (charF Fm) (size_windows_of_thick_density Fm cT2) cTT cQD cTh lI lD`.
-/
theorem linkGLOBAL7_pk (Fm : FamP eps) (Cabs CH C0 C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 1 ≤ C0)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison)
    (hL7 : ChosenTT Fm → ChosenBadp Fm → LinkG Fm → LossesSmallShares Fm)
    (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (tVol : StandardLattice.TiesF Fm)
    (tOm : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ))
    (tFree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (tTh : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22)
    (t7 : flipTwoThree.admF7 Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  intro hTu hCh hIn
  obtain ⟨C5, c6, hC5, hc6, cT2, cTT, cBad, cW, cQD, cTh, cPr, cCo⟩ := hCh
  obtain ⟨lG, lS, lI, lD, lMu⟩ := hIn
  have h10 := prvF_of_familyTheorem_ties_eventualIncidenceTransport Fm C3 crystallineComparison C22 s59 s22 s24 s10 hF3 tVol t10
  have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
  have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_of Fm crystallineComparison h10 tSet)
  have hRank : J.MuRank Fm := muRank_of_proviso Fm crystallineComparison (by linarith) cPr hNF h10 tSet
  have hRR : RRRankF Fm := rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (fun x i => TaylorLogMetric.first_hypothesis_of_lifting _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1
  have hCount : CountF Fm := countF_fam Fm h24.2.2.2.2.2.2.2
  have hDl := dl_of_chosen Fm C5 cQD
  have h23 := s23 ⟨flipTwoThree.theta_norm_family_of_linked Fm C22 h22 tOm, flipTwoThree.theta_condition_family_of_linked Fm C22 tFree tTh,
    flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 h4p,
    flipTwoThree.injectivity_family_of_theorem Fm crystallineComparison h10 tSet, flipTwoThree.norm_bound_family_of_theorem Fm crystallineComparison h10 tSet, t7⟩
  have hSM : SlopesMF Fm := flipTwoThree.slopesMF_of_count_fam Fm h23.2.2.2.2.1 h23.2.2.2.2.2.1 hCount hDl tCV
  have hSN : SlopesNF Fm := slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_of Fm crystallineComparison h10 tSet hTu hRank lG lMu)
  have hLat : LatF Fm := latF Fm lD hNF hRank hRR
  have hFr : FrameF Fm CH := frameF_of Fm CH C0 hCH hC0
    (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_of Fm crystallineComparison h10 tSet)
      (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) hLat cPr cCo hNF
  exact linkCore Fm Cabs CH 0 C5 c6 hCabs hCH.le le_rfl hc6 hCount hSM hSN hLat (nodesF Fm) hFr
    (lossF_of_7 Fm (hL7 cTT cBad lG) cW) (charF Fm) (size_windows_of_thick_density Fm cT2) cTT cQD cTh lI lD

end Formalism.MainNotions

end
