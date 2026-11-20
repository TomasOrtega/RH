import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.DC GlobalTheory.Fc NumberField

/- English proof (translation)
Introduce and unpack `Q cT la G hla hM ⟨ε0, hε0, hK⟩`. Use `⟨min ε0 (1 / 53), lt_min hε0 (by norm_num), fun eps he hle K => ?_⟩` and prove the remaining obligations. Establish `he52 : eps < 1 / 52` using `lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)`. Take `⟨CT2, C8, C5, c6, Cb, K0, hC8, hC5, hc6, hCb, hK⟩` from `hK eps he (hle.trans (min_le_left _ _)) he52`. Take `⟨C, hStd, hCT2, hCp, hLK, hLK0, hGK⟩` from `exists_std_large (thrTu K (cT eps 9)) K0 CT2 C8 hC8`.

Take `⟨c1, hK⟩` from `hK C hStd hCT2 hCp hLK0`. Take `⟨c1', hN⟩` from `szRow_numAt eps he he52 C hStd`. Take `⟨c2, hK⟩` from `hK (max c1 c1') (le_max_left _ _)`. Take `⟨c2', hN⟩` from `hN (max c1 c1') (le_max_right _ _)`. Take `⟨x0, S, hK⟩` from `hK (max c2 c2') (le_max_left _ _)`.

Take `⟨x0', hN⟩` from `hN (max c2 c2') (le_max_right _ _)`. Establish `hx1 : (1 : ℝ) < max 2 (max x0 x0')` using `lt_of_lt_of_le one_lt_two (le_max_left _ _)`. Establish `hK' : ∀ s : Scale, s.eps = eps → max 2 (max x0 x0') ≤ s.x → S.Mem s → ∃ k : Kit C (max c1 c1') (max c2 c2') s, ∀ i, (k.pt i).Has (((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt).and G.pt) ∧ ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i) …` using `fun s hs hx hm => hK s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hm`. Use `choose k hk using hK'`. Establish `hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) ∧ ChTT_at ((k s h h' h'').pt i).L ∧ ChCode_at ((k s h h' h'').pt i).L 3 C.P.CF`.

Introduce `s h h' h'' i`. Use `hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)` and prove the remaining obligations. Rewrite using `[(k s h h' h'').sc_eq i]`. Conclude with `h`. Rewrite using `[(k s h h' h'').sc_eq i]`.

Conclude with `((le_max_right _ _).trans (le_max_right _ _)).trans h'`. Take `⟨Fm, hFx, hPre, hOut, hMid, hLast, hTu, hQ, hR, -, hWn, -⟩` from `exists_famP_of_kits eps C _ _ _ la S he he52 hx1 hla.le hStd hGK k (fun s h h' h'' i => (hnum s h h' h'' i).1)`. Use `replace hOut : Fm.cOut = C.cOut := hOut`. Establish `hall` using `hR (fun D L Gx => (ThickSetLowerBound L ∧ ChBad_at Gx Cb ∧ ChQD_at D L.sc.x L.sc.eps C5) ∧ (Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) ∧ Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊) (fun s h h' h'' i => ⟨(hk s h h' h'' i).2, hnum s h h' h'' i, (( …`. Establish `hCF : (1 : ℝ) ≤ C.P.CF` using `hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])`.

Establish `hc` using `hQ ((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt) (fun s h h' h'' i => (hk s h h' h'' i).1.1)`. Establish `hGc : G.cls la Fm` using `⟨fun y => by`. Take `⟨Y, a, b⟩` from `S.windows y`. Conclude with `⟨Y, a, fun x c d => hWn ▸ b x c d⟩,`. Use `hQ G.pt (fun s h h' h'' i => (hk s h h' h'' i).1.2)⟩`.

Take `⟨hFix, hWin⟩` from `fix_and_win_of_numAt eps C Fm hStd hOut (fun x i => (hall x i).2.1.1)`. Establish `hCYL : Fm.CYL = 9` using `hFix.2.2.2.2.2.2.2.1`. Establish `hlt : ∀ x, x ≥ Fm.x1 + 1 → Fm.x1 < x` using `fun x hx => by linarith`. Establish `hLarge : Fm.Large (thrTu K (cT eps 9)) C.P.CF`. Unfold `FamP.Large`.

Rewrite using `[hPre, hOut, hMid, hLast]`. Conclude with `hLK`. Establish `hTw : TwGood Fm` using `classOf_twPt Fm fun x hx i => (hc x hx i).1.1.2.2.2`. Establish `hQD : ChosenQD Fm C5`. Use `⟨Fm.x1 + 1, fun x hx i => ?_⟩` and prove the remaining obligations.

Use `(hall x i).1.2.2` as an intermediate fact. Rewrite `this` using `[Fm.L_x x i (hlt x hx), Fm.L_eps x i]`. Then use the resulting hypothesis. Establish `hreq` using `classOf_reqPt Fm fun x hx i => ⟨(hc x hx i).2, (hc x hx i).1.2.2.1, (hc x hx i).1.2.2.2.1⟩`. Establish `hDG : DGamDvdF Fm` using `⟨Fm.x1 + 1, fun x hx i u => (hc x (hlt x hx) i).1.1.2.2.1 _ (hM _) u⟩`. Establish `hTame : TameDistinctF Fm` using `⟨Fm.x1 + 1, fun x hx i => (hc x (hlt x hx) i).1.1.2.1⟩`.

Establish `hCFeq : Fm.CF = C.P.CF`. Use `congrArg (fun f : ℝ → List ℝ => (f 0).getD 9 0) hMid` as an intermediate fact. Simplify `this` using `[FamP.cMid, FC.cMid]`. Establish `hUp : CodeUpF Fm 3 C.P.CF`. Use `⟨Fm.x1 + 1, fun x hx i => ?_⟩` and prove the remaining obligations.

Establish `h` using `(hall x i).2.2`. Rewrite `h` using `[Fm.L_x x i (hlt x hx)]`. Establish `hx0 : (0 : ℝ) ≤ x` using `by have := Fm.one_lt_family_threshold; linarith`. Rewrite using `[h]`. Conclude with `(Nat.ceil_lt_add_one (by positivity)).le`.

Establish `hT2 : ThickSetEventually Fm` using `⟨0, fun x _ i => (hall x i).1.1⟩`. Establish `hTT : ChosenTT Fm` using `⟨0, fun x _ i => (hall x i).2.1.2.1⟩`. Establish `hBad : ChosenBad Fm Cb` using `⟨0, fun x _ i => (hall x i).1.2.1⟩`. Establish `hCode : ChosenCode Fm 3 C.P.CF` using `⟨0, fun x _ i => (hall x i).2.1.2.2⟩`. Establish `hLink : Link ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩ (setTu Fm (cT eps 9))`.

Use `⟨rfl, ⟨hC5, hc6, hCb⟩, hStd, hPre, ?_, hMid, hLast⟩` and prove the remaining obligations. Use `show (setTu Fm C.CTu).cOut = _`. Rewrite using `[← hTu]`. Conclude with `hOut`. Use `⟨setTu Fm (cT eps 9), C.P.CF, C5, Cb, ⟨⟨⟨_, hLink, (setTu_cls _ Fm _).2 ⟨hc, hFix, hWin⟩⟩, hGc⟩, hTw⟩, zero_le_one.trans hCF, (setTu_large Fm K _ _).2 hLarge, hC5, hCb, hT2, hTT, hBad, hQD, hCode, hreq.2.1, hreq.2.2, hDG, ?_, hTame, hCFeq, hUp, hCYL.le⟩` and prove the remaining obligations.

Use `show cT eps Fm.CYL ≤ cT eps 9`. Rewrite using `[hCYL]`.
-/
theorem designS : ∀ (Q : Par → PtProp) (cT : ℝ → ℝ → ℝ) (la : ℝ) (G : FReq), 1 < la → DC.MinkDiv →
    KitCPW la (fun κ => ((withDuty (DC.withObj (Q κ))).and DC.WallPt).and G.pt) →
    DC.DesignChoices (DC.WithTw fun Fm => (∃ κ : Par, Link κ Fm ∧ DC.cls (Q κ) Fm) ∧ G.cls la Fm) 3 cT := by
  rintro Q cT la G hla hM ⟨ε0, hε0, hK⟩
  refine ⟨min ε0 (1 / 53), lt_min hε0 (by norm_num), fun eps he hle K => ?_⟩
  have he52 : eps < 1 / 52 := lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨CT2, C8, C5, c6, Cb, K0, hC8, hC5, hc6, hCb, hK⟩ := hK eps he (hle.trans (min_le_left _ _)) he52
  obtain ⟨C, hStd, hCT2, hCp, hLK, hLK0, hGK⟩ := exists_std_large (thrTu K (cT eps 9)) K0 CT2 C8 hC8
  obtain ⟨c1, hK⟩ := hK C hStd hCT2 hCp hLK0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  obtain ⟨c2, hK⟩ := hK (max c1 c1') (le_max_left _ _)
  obtain ⟨c2', hN⟩ := hN (max c1 c1') (le_max_right _ _)
  obtain ⟨x0, S, hK⟩ := hK (max c2 c2') (le_max_left _ _)
  obtain ⟨x0', hN⟩ := hN (max c2 c2') (le_max_right _ _)
  have hx1 : (1 : ℝ) < max 2 (max x0 x0') := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  have hK' : ∀ s : Scale, s.eps = eps → max 2 (max x0 x0') ≤ s.x → S.Mem s →
      ∃ k : Kit C (max c1 c1') (max c2 c2') s, ∀ i, (k.pt i).Has (((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt).and G.pt) ∧
        ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧ ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5 :=
    fun s hs hx hm => hK s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hm
  choose k hk using hK'
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) ∧ ChTT_at ((k s h h' h'').pt i).L ∧
      ChCode_at ((k s h h' h'').pt i).L 3 C.P.CF := by
    intro s h h' h'' i
    refine hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, hTu, hQ, hR, -, hWn, -⟩ :=
    exists_famP_of_kits eps C _ _ _ la S he he52 hx1 hla.le hStd hGK k (fun s h h' h'' i => (hnum s h h' h'' i).1)
  replace hOut : Fm.cOut = C.cOut := hOut
  have hall := hR (fun D L Gx => (ThickSetLowerBound L ∧ ChBad_at Gx Cb ∧ ChQD_at D L.sc.x L.sc.eps C5) ∧
      (Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) ∧
      Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊)
    (fun s h h' h'' i => ⟨(hk s h h' h'' i).2, hnum s h h' h'' i, ((k s h h' h'').val i).words⟩)
  have hCF : (1 : ℝ) ≤ C.P.CF := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hc := hQ ((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt) (fun s h h' h'' i => (hk s h h' h'' i).1.1)
  have hGc : G.cls la Fm := ⟨fun y => by
      obtain ⟨Y, a, b⟩ := S.windows y
      exact ⟨Y, a, fun x c d => hWn ▸ b x c d⟩,
    hQ G.pt (fun s h h' h'' i => (hk s h h' h'' i).1.2)⟩
  obtain ⟨hFix, hWin⟩ := fix_and_win_of_numAt eps C Fm hStd hOut (fun x i => (hall x i).2.1.1)
  have hCYL : Fm.CYL = 9 := hFix.2.2.2.2.2.2.2.1
  have hlt : ∀ x, x ≥ Fm.x1 + 1 → Fm.x1 < x := fun x hx => by linarith
  have hLarge : Fm.Large (thrTu K (cT eps 9)) C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hLK
  have hTw : TwGood Fm := classOf_twPt Fm fun x hx i => (hc x hx i).1.1.2.2.2
  have hQD : ChosenQD Fm C5 := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have := (hall x i).1.2.2
    rwa [Fm.L_x x i (hlt x hx), Fm.L_eps x i] at this
  have hreq := classOf_reqPt Fm fun x hx i => ⟨(hc x hx i).2, (hc x hx i).1.2.2.1, (hc x hx i).1.2.2.2.1⟩
  have hDG : DGamDvdF Fm := ⟨Fm.x1 + 1, fun x hx i u => (hc x (hlt x hx) i).1.1.2.2.1 _ (hM _) u⟩
  have hTame : TameDistinctF Fm := ⟨Fm.x1 + 1, fun x hx i => (hc x (hlt x hx) i).1.1.2.1⟩
  have hCFeq : Fm.CF = C.P.CF := by
    have := congrArg (fun f : ℝ → List ℝ => (f 0).getD 9 0) hMid
    simpa [FamP.cMid, FC.cMid] using this
  have hUp : CodeUpF Fm 3 C.P.CF := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h := (hall x i).2.2
    rw [Fm.L_x x i (hlt x hx)] at h
    have hx0 : (0 : ℝ) ≤ x := by have := Fm.one_lt_family_threshold; linarith
    rw [h]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hT2 : ThickSetEventually Fm := ⟨0, fun x _ i => (hall x i).1.1⟩
  have hTT : ChosenTT Fm := ⟨0, fun x _ i => (hall x i).2.1.2.1⟩
  have hBad : ChosenBad Fm Cb := ⟨0, fun x _ i => (hall x i).1.2.1⟩
  have hCode : ChosenCode Fm 3 C.P.CF := ⟨0, fun x _ i => (hall x i).2.1.2.2⟩
  have hLink : Link ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩ (setTu Fm (cT eps 9)) := by
    refine ⟨rfl, ⟨hC5, hc6, hCb⟩, hStd, hPre, ?_, hMid, hLast⟩
    show (setTu Fm C.CTu).cOut = _
    rw [← hTu]
    exact hOut
  refine ⟨setTu Fm (cT eps 9), C.P.CF, C5, Cb, ⟨⟨⟨_, hLink, (setTu_cls _ Fm _).2 ⟨hc, hFix, hWin⟩⟩, hGc⟩, hTw⟩, zero_le_one.trans hCF,
    (setTu_large Fm K _ _).2 hLarge, hC5, hCb, hT2, hTT, hBad, hQD, hCode, hreq.2.1, hreq.2.2, hDG, ?_, hTame, hCFeq, hUp,
    hCYL.le⟩
  show cT eps Fm.CYL ≤ cT eps 9
  rw [hCYL]

end UpperTheory.Top

end
