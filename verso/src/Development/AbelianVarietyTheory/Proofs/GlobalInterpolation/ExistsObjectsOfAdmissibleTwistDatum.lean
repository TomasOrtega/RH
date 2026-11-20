import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ObjCOfRecExObjO

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

/- English proof (translation)
The claim follows from `ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h`.
-/
theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h

open GlobalTheory.EX.DC in

/- English proof (translation)
Take `⟨ε0, h0, h⟩` from `h`. Use `⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩` and prove the remaining obligations. Take `⟨K0, h⟩` from `h eps C8 C5 c6 Cb a1 a2 a3 a4`. Use `⟨K0, fun C b1 b2 b3 => ?_⟩` and prove the remaining obligations. Take `⟨c1, h⟩` from `h C b1 b2 b3`.

Take `⟨c1', hP⟩` from `explicitConstants_parameterConditions_large eps a1 a3 C b1`. Use `⟨max c1 c1', fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨c2, h⟩` from `h cD ((le_max_left _ _).trans hcD)`. Take `⟨c2', hP⟩` from `hP cD ((le_max_right _ _).trans hcD)`. Use `⟨max c2 c2', fun ch hch => ?_⟩` and prove the remaining obligations.

Take `⟨x0, h⟩` from `h ch ((le_max_left _ _).trans hch)`. Take `⟨x1, hP⟩` from `hP ch ((le_max_right _ _).trans hch)`. Take `⟨x2, hq⟩` from `small_prime_lt eps C8 a1 a4`. Take `⟨x3, hJ⟩` from `GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1`. Use `⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩` and prove the remaining obligations.

Simplify using `only at d1 d4 d5 d6 d7`. Rewrite `d5` using `[b2]`. Simplify using `only [max_le_iff] at d2`. Take `⟨p, e1, e2, e3, e4, e5, e6⟩` from `h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9`. Use `⟨p, e1, e2, e3, e4, e5, e6, ?_⟩` and prove the remaining obligations.

Simplify using `only at e2 p`. Substitute `e1` using the available equality. Use `show GlobalTwistingFacts p.L`. Take `⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩` from `d5`. Establish `eq0 : q0Av p.D = q0` using `(eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm`.

Establish `hX : (q0Av p.D : ℝ) < p.L.sc.X'`. Rewrite using `[eq0]`. Conclude with `hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle`. Take `⟨P, -⟩` from `hP _ _ d1 d2.1.2 e2 e3`. Establish `hXb` using `X'_le_b p.L.sc`.

Establish `hs` using `globalTwisting_spec_fact p.D.host`. Establish `hg : ∀ j, q0Av p.D < p.D.host.g j`. Introduce `j`. Establish `hg` using `(e2.host.2.2.2.2.1 j).1`. Establish `hk : (1 : ℝ) ≤ p.D.R.k`.

Use `p.D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ p.D.R.k)` after adjusting the coercions. Establish `hb1 : 1 ≤ p.L.sc.b` using `Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)`. Establish `h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b` using `le_mul_of_one_le_left (by linarith) hk`. Establish `h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8` using `le_self_pow₀ (by linarith) (by norm_num)`.

Conclude with `(show (q0Av p.D : ℝ) < p.D.host.g j by linarith)` after adjusting the coercions. Use `⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2, fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩` and prove the remaining obligations. Rewrite using `[eq0]`. Conclude with `e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)`. Rewrite using `[Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]`.

Conclude with `hX.le.trans hXb`.
-/
theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb

open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in

/- English proof (translation)
Take `⟨ε0, h0, hRec⟩` from `hRec`. Use `⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩` and prove the remaining obligations. Take `⟨K0, hRec⟩` from `hRec eps C8 C5 c6 Cb e1 e2 e3 e4`. Use `⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩` and prove the remaining obligations. Establish `hL0 : C.Large K0 C.P.CF` using `⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩`.

Establish `hg : 10 ≤ C.cX.err.g` using `(le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))`. Take `⟨c1, hRec⟩` from `hRec C hS hC8 hL0`. Use `⟨max c1 0, fun cD hcD => ?_⟩` and prove the remaining obligations. Establish `hcD0 : 0 ≤ cD` using `(le_max_right _ _).trans hcD`. Take `⟨c2, hRec⟩` from `hRec cD ((le_max_left _ _).trans hcD)`.

Use `⟨max c2 402, fun ch hch => ?_⟩` and prove the remaining obligations. Establish `hch0 : 402 ≤ ch` using `(le_max_right _ _).trans hch`. Take `⟨cs, x1, hcs, hRec⟩` from `hRec ch ((le_max_left _ _).trans hch)`. Take `⟨x2, h2⟩` from `chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0`. Take `⟨x3, h3⟩` from `exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS`.

Take `⟨x4, h4⟩` from `exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0`. Take `⟨x5, h5⟩` from `scale_X'_le_of_log eps cs e1 hcs`. Take `⟨x6, h6⟩` from `scale_one_le_w'' eps e1`. Use `⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩` and prove the remaining obligations. Introduce `s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu`.

Simplify using `only [max_le_iff] at hx`. Take `⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩` from `hx`. Simplify using `only at hs hCT hH hW hM`. Rewrite `hH` using `[hq0]`. Take `⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩` from `h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc`.

Take `⟨du, Ds, hdu, hDs, hlog, hRec⟩` from `hRec s _ _ _ _ hs y1 hCh`. Take `⟨Lv, l1, l2, l3⟩` from `h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog`. Take `⟨D, Y, hO, hRO, hLO, hTW, hQ⟩` from `hRec Lv l1 l2 l3`. Take `⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩` from `h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO`. Establish `hDR : D.R = R` using `g0`.

Establish `hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ)`. Introduce `u`. Take `⟨u', hu'⟩` from `exists_T_of_over hO u`. Establish `w` using `(Lv.T_win u').1`. Rewrite `w` using `[l1, l2, l3]`.

Rewrite using `[hu']`. Use `le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w` and prove the remaining obligations. Establish `: (0 : ℝ) < du u'` using `by exact_mod_cast hdu u'`. Establish `: 0 < GamS C s R` using `Real.exp_pos _`. Check the signs of the components of the expression.

Take `⟨p, n1, n2, n3, n4⟩` from `Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO`. Conclude with `⟨p.pt, n1, p.pt_val n3, hA, ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩, hO.field⟩, p.pt_canon n4, hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩`.
-/
theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

/- English proof (translation)
Introduce `QO hL hR` and use `(objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩`.
-/
theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
