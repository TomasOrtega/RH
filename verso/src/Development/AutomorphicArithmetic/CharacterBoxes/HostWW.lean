import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

/- English proof (translation)
Take `⟨⟨f1, f2, f3, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, hl⟩` from `h`. Establish `hm' : ∀ c ∈ C.cMid C.P.CF, 0 ≤ c` using `fun c hc => zero_le_one.trans (hm c hc)`. Establish `hl' : ∀ c ∈ C.cLast, 0 ≤ c` using `fun c hc => zero_le_one.trans (hl c hc)`. Apply the tactic sequence `refine ⟨hm' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, by rw [f2]; norm_num, by rw [f3]; norm_num, by rw [f1]; norm_num, hl' _ ?_⟩ <;> simp [FC.cMid, FC.cLast]`.
-/
private theorem gk_nonneg {C : FC} (h : Std C) : C.GK.Nonneg := by
  obtain ⟨⟨f1, f2, f3, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, hl⟩ := h
  have hm' : ∀ c ∈ C.cMid C.P.CF, 0 ≤ c := fun c hc => zero_le_one.trans (hm c hc)
  have hl' : ∀ c ∈ C.cLast, 0 ≤ c := fun c hc => zero_le_one.trans (hl c hc)
  refine ⟨hm' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_,
    by rw [f2]; norm_num, by rw [f3]; norm_num, by rw [f1]; norm_num, hl' _ ?_⟩ <;> simp [FC.cMid, FC.cLast]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩, ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc), fun …`.
-/
private theorem large_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
   ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

/- English proof (translation)
Consider the cases of `s`. Consider the cases of `s'`. Simplify the hypotheses and the goal together.
-/
private theorem scale_ext {s s' : Scale} (h1 : s.x = s'.x) (h2 : s.eps = s'.eps) (h3 : s.J = s'.J) : s = s' := by
  cases s; cases s'; simp_all

/- English proof (translation)
Introduce and unpack `Q la P hla hH ⟨ε0, hε0, hO⟩ ⟨ε1, hε1, hW⟩`. Use `⟨min ε0 ε1, lt_min hε0 hε1, fun eps he hle he52 => ?_⟩` and prove the remaining obligations. Take `⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩` from `hH eps he he52`. Take `⟨K0, hO⟩` from `hO eps C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) he52 h8`. Take `⟨K1, hW⟩` from `hW eps he (hle.trans (min_le_right _ _))`.

Use `⟨CT2, C8, C5, c6, Cb, K0.sup K1, h8, h5, h6, hb, fun C hStd hCT2 hCp hL => ?_⟩` and prove the remaining obligations. Take `⟨hL0, hL1⟩` from `large_sup hL`. Take `⟨c1, hO⟩` from `hO C hStd hCp hL0`. Take `⟨c1', hN⟩` from `szRow_numAt eps he he52 C hStd`. Use `⟨max c1 c1', fun cD hcD => ?_⟩` and prove the remaining obligations.

Take `⟨c2, hO⟩` from `hO cD ((le_max_left _ _).trans hcD)`. Take `⟨c2', hN⟩` from `hN cD ((le_max_right _ _).trans hcD)`. Use `⟨max c2 c2', fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨xO, hO⟩` from `hO ch ((le_max_left _ _).trans hch)`. Take `⟨xN, hN⟩` from `hN ch ((le_max_right _ _).trans hch)`.

Establish `hmid` using `hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hCF : (0 : ℝ) ≤ C.P.CF` using `zero_le_one.trans (hmid _ (by simp [FC.cMid]))`. Establish `hCG : (0 : ℝ) ≤ C.CGam` using `zero_le_one.trans (hmid _ (by simp [FC.cMid]))`. Take `⟨xw, hw⟩` from `exists_weights_in_windows eps C he he52 hStd`. Take `⟨xc, hc⟩` from `exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF`.

Take `⟨x1, hx1, a1, a2, a3, a5, a6⟩ : ∃ x1 : ℝ, 1 < x1 ∧ xH ≤ x1 ∧ xO ≤ x1 ∧ xN ≤ x1 ∧ xw ≤ x1 ∧ xc ≤ x1` from `⟨max 2 (max xH (max xO (max xN (max xw xc)))), by simp, by simp, by simp, by simp, by simp, by simp⟩`. Set `G : Scale → Prop` to `fun s => ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ), RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = DC.q0H H ∧ (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧ WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0`. Set `Q' : PtProp` to `fun D L _ Gx _ K _ _ _ => AuxBlock8.WeightVectorExists D L Gx K → G L.sc`. Establish `hK : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q'`. Introduce `s hs hx hm`.

Take `⟨R, H, q0, hRV, hHT, hHG, hq, hP⟩` from `hH s hs (a1.trans hx) hm`. Take `⟨a, b, hab⟩` from `hw s R H hs (a5.trans hx) hRV`. Take `⟨c, hci, -⟩` from `hc s R hs (a6.trans hx) hRV`. Take `⟨k, hk⟩` from `DC.kit_of_points Q C cD ch s R H a b _ c fun u0 hu => hO s R H q0 a b _ c u0 hs (a2.trans hx) hRV (hHT.trans hCT2.symm) hHG hq hab rfl hci hu`. Use `⟨k, fun i hp => ?_⟩` and prove the remaining obligations.

Take `⟨⟨u0, hF⟩, hI, -⟩` from `hk i`. Take `⟨a', b', e1, e2, e3⟩` from `weightWindowRequirement_host_of_point C cD ch (k.pt i) R H a b _ c u0 hStd (k.val i) hF hI hp`. Rewrite `e2`, `e3`, the goal using `[k.sc_eq i]`. Conclude with `⟨R, H, q0, a', b', hRV, hHT, hHG, hq, e1, e2, e3, hP⟩`. Use `choose k hk using hK`.

Establish `hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L)`. Introduce `s h h' h'' i`. Use `(hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)).1` and prove the remaining obligations. Rewrite using `[(k s h h' h'').sc_eq i]`. Conclude with `h`.

Rewrite using `[(k s h h' h'').sc_eq i]`. Conclude with `a3.trans h'`. Take `⟨Fm, hFx, hPre, hOut, hMid, hLast, -, hQ, -, hJ, hWin, -⟩` from `exists_famP_of_kits eps C cD ch x1 la S he he52 hx1 hla.le hStd (gk_nonneg hStd) k hnum`. Establish `hFL : Fm.Large K1 C.P.CF`. Unfold `FamP.Large`.

Rewrite using `[hPre, hOut, hMid, hLast]`. Conclude with `hL1`. Take `⟨xW, hW⟩` from `hW Fm C.P.CF trivial hFL`. Use `⟨max (Fm.x1 + 1) xW, S, fun s hs hx hm => ?_⟩` and prove the remaining obligations. Establish `hx' : Fm.x1 < s.x` using `by have := (le_max_left _ _).trans hx; linarith`.

Take `⟨i⟩` from `Fm.Ix_win s.x (by rw [hWin]; exact hm.2)`. Establish `hG : G (Fm.L s.x i).sc` using `hQ Q' hk s.x hx' i (hW s.x ((le_max_right _ _).trans hx) i)`. Establish `e : (Fm.L s.x i).sc = s` using `scale_ext (Fm.L_x _ i hx') ((Fm.L_eps _ i).trans hs.symm) ((Fm.L_J _ i).trans (hJ.trans hm.1.symm))`. Rewrite `hG` using `[e]`. Conclude with `hG`.
-/
theorem UpperTheory.Top.hostWW :
    ∀ (Q : PtProp) (la : ℝ) (P : HostReq), 1 < la → DC.HostExQW la P → DC.ObjC Q → DC.WClosed → DC.HostWW la P := by
  rintro Q la P hla hH ⟨ε0, hε0, hO⟩ ⟨ε1, hε1, hW⟩
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps he hle he52 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he52
  obtain ⟨K0, hO⟩ := hO eps C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) he52 h8
  obtain ⟨K1, hW⟩ := hW eps he (hle.trans (min_le_right _ _))
  refine ⟨CT2, C8, C5, c6, Cb, K0.sup K1, h8, h5, h6, hb, fun C hStd hCT2 hCp hL => ?_⟩
  obtain ⟨hL0, hL1⟩ := large_sup hL
  obtain ⟨c1, hO⟩ := hO C hStd hCp hL0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hO⟩ := hO cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hN⟩ := hN cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hO⟩ := hO ch ((le_max_left _ _).trans hch)
  obtain ⟨xN, hN⟩ := hN ch ((le_max_right _ _).trans hch)
  have hmid := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hStd
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x1, hx1, a1, a2, a3, a5, a6⟩ : ∃ x1 : ℝ, 1 < x1 ∧ xH ≤ x1 ∧ xO ≤ x1 ∧ xN ≤ x1 ∧ xw ≤ x1 ∧ xc ≤ x1 :=
    ⟨max 2 (max xH (max xO (max xN (max xw xc)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  let G : Scale → Prop := fun s => ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ),
    RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = DC.q0H H ∧ (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧
      WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0
  let Q' : PtProp := fun D L _ Gx _ K _ _ _ => AuxBlock8.WeightVectorExists D L Gx K → G L.sc
  have hK : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q' := by
    intro s hs hx hm
    obtain ⟨R, H, q0, hRV, hHT, hHG, hq, hP⟩ := hH s hs (a1.trans hx) hm
    obtain ⟨a, b, hab⟩ := hw s R H hs (a5.trans hx) hRV
    obtain ⟨c, hci, -⟩ := hc s R hs (a6.trans hx) hRV
    obtain ⟨k, hk⟩ := DC.kit_of_points Q C cD ch s R H a b _ c fun u0 hu =>
      hO s R H q0 a b _ c u0 hs (a2.trans hx) hRV (hHT.trans hCT2.symm) hHG hq hab rfl hci hu
    refine ⟨k, fun i hp => ?_⟩
    obtain ⟨⟨u0, hF⟩, hI, -⟩ := hk i
    obtain ⟨a', b', e1, e2, e3⟩ := weightWindowRequirement_host_of_point C cD ch (k.pt i) R H a b _ c u0 hStd (k.val i) hF hI hp
    rw [k.sc_eq i] at e2 e3 ⊢
    exact ⟨R, H, q0, a', b', hRV, hHT, hHG, hq, e1, e2, e3, hP⟩
  choose k hk using hK
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) := by
    intro s h h' h'' i
    refine (hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)).1
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact a3.trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, -, hQ, -, hJ, hWin, -⟩ :=
    exists_famP_of_kits eps C cD ch x1 la S he he52 hx1 hla.le hStd (gk_nonneg hStd) k hnum
  have hFL : Fm.Large K1 C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hL1
  obtain ⟨xW, hW⟩ := hW Fm C.P.CF trivial hFL
  refine ⟨max (Fm.x1 + 1) xW, S, fun s hs hx hm => ?_⟩
  have hx' : Fm.x1 < s.x := by have := (le_max_left _ _).trans hx; linarith
  obtain ⟨i⟩ := Fm.Ix_win s.x (by rw [hWin]; exact hm.2)
  have hG : G (Fm.L s.x i).sc := hQ Q' hk s.x hx' i (hW s.x ((le_max_right _ _).trans hx) i)
  have e : (Fm.L s.x i).sc = s :=
    scale_ext (Fm.L_x _ i hx') ((Fm.L_eps _ i).trans hs.symm) ((Fm.L_J _ i).trans (hJ.trans hm.1.symm))
  rw [e] at hG
  exact hG
