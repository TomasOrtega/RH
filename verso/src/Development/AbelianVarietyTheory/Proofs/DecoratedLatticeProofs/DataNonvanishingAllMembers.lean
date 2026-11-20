import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdBNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberData

open Formalism.MainNotions.S in

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hk0 : 0 < D.R.k` using `by omega`. Establish `hSc` using `Sc_eq' L`. Establish `e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ)` using `fun u τ => by`.

Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]`. Establish `e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ)` using `fun τ => vOne_succ τ 0 (by omega)`. Establish `hCc : L.Cc = 2` using `hV.Cc_eq.trans hC.2.1`. Establish `hdu : ∀ u, 0 < D.duS u` using `fun u => by`. Establish `h` using `hR u`.

Unfold `GlobalTheory.Core.Rk.RankMu at h`. Rewrite `h` using `[GlobalTheory.Core.Rk.d0_eq]`. Establish `hd : (0 : ℝ) < (D.mem u).A.duStar` using `by exact_mod_cast (D.mem u).A.duStar_pos`. Establish `hT : (1 : ℝ) < (D.mem u).A.T` using `by exact_mod_cast (D.mem u).A.T_prime.one_lt`. Establish `hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1` using `sub_pos.2 (one_lt_pow₀ hT (by omega))`.

Establish `h0 : (0 : ℝ) < D.duS u` using `by rw [h]; positivity`. Conclude with `h0` after adjusting the coercions. Use `⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8, fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu, Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1, discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_tw …` and prove the remaining obligations. Introduce `u τ`. Rewrite using `[e1, e2, ← hSc]`.

Distinguish the cases in `ht : Formalism.MainNotions.S.IsTop D τ`. Take `⟨t, ht⟩` from `ht`. Establish `h1` using `(L.top_u τ t hk0 ht).1`. Establish `h2` using `(L.cloud_v τ ⟨0, by omega⟩).2`. Establish `h3` using `(L.aT_win t).1`.

Establish `h4` using `Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS`. Establish `h5` using `L.Sc_pos`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Introduce `u τ ht`. Use `(L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `this` using `[hCc]`. Rewrite using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `u τ ht`.

Establish `hv` using `hV.hc.1 τ ⟨D.R.k - 2, by omega⟩`. Establish `hu` using `(hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2`. Establish `e : D.R.k - 1 = D.R.k - 2 + 1` using `by omega`. Establish `hv'` using `vOne_succ τ (D.R.k - 2) (by omega)`. Rewrite `hv'` using `[← e]`.

Rewrite using `[uOne_last u τ, hv', hv, hu]`. Evaluate the numerical expressions. Introduce `τ ht`. Take `⟨t, ht⟩` from `ht`. Establish `hm0 : 0 < D.R.m` using `by omega`.

Establish `eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ)`. Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]`. Establish `et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2`. Unfold `bTop`. Rewrite using `[uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `L.top_b τ t hm0 ht`. Take `⟨b1, hb, htop, -, -⟩` from `hV.hc.2.2.1`. Establish `hb0` using `(hb τ ⟨0, hm0⟩).1`. Establish `hbt` using `htop τ t ht`.

Establish `hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)`. Rewrite using `[hb0, hbt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x` using `Int.floor_le _`.

Establish `hb'0` using `Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)`. Establish `hx1` using `Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0 hx1`. Establish `hbT` using `L.bT_ge t`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`.

Rewrite using `[eb, et]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem dataNW_of_val {C : Formalism.MainNotions.Inhab.FC} {cD ch : ℝ} (hC : Std C) {D : D7} (L : SizeData₂ D)
    (hV : Val C cD ch L) (hS : SizesAt L) (hR : ∀ u, GlobalTheory.Core.Rk.RankMu D u) : GlobalTheory.Core.Deg.DataNW D := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hk0 : 0 < D.R.k := by omega
  have hSc := Sc_eq' L
  have e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := fun u τ => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]
  have e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := fun τ => vOne_succ τ 0 (by omega)
  have hCc : L.Cc = 2 := hV.Cc_eq.trans hC.2.1
  have hdu : ∀ u, 0 < D.duS u := fun u => by
    have h := hR u
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
    have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := sub_pos.2 (one_lt_pow₀ hT (by omega))
    have h0 : (0 : ℝ) < D.duS u := by rw [h]; positivity
    exact_mod_cast h0
  refine ⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8,
    fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu,
    Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1,
    discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),
    fun u => ne_of_mod (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le (T_mod D u)⟩
  · intro u τ
    rw [e1, e2, ← hSc]
    by_cases ht : Formalism.MainNotions.S.IsTop D τ
    · obtain ⟨t, ht⟩ := ht
      have h1 := (L.top_u τ t hk0 ht).1
      have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
      have h3 := (L.aT_win t).1
      have h4 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS
      have h5 := L.Sc_pos
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      rw [h1]
      linarith
    · have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1
      push_cast at this
      exact this
  · intro u τ ht
    have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2
    push_cast at this
    rw [hCc] at this
    rw [e1, e2]
    linarith
  · intro u τ ht
    have hv := hV.hc.1 τ ⟨D.R.k - 2, by omega⟩
    have hu := (hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2
    have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
    have hv' := vOne_succ τ (D.R.k - 2) (by omega)
    rw [← e] at hv'
    rw [uOne_last u τ, hv', hv, hu]
    norm_num
  · intro τ ht
    obtain ⟨t, ht⟩ := ht
    have hm0 : 0 < D.R.m := by omega
    have eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]
    have et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 := by
      unfold bTop
      rw [uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]
      ring
    have h1 := L.top_b τ t hm0 ht
    obtain ⟨b1, hb, htop, -, -⟩ := hV.hc.2.2.1
    have hb0 := (hb τ ⟨0, hm0⟩).1
    have hbt := htop τ t ht
    have hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
      rw [hb0, hbt]
      push_cast
      ring
    have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
    have hb'0 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)
    have hx1 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1
    have hbT := L.bT_ge t
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    rw [eb, et]
    constructor <;> linarith

/- English proof (translation)
Substitute `h1 h2 h3` using the available equality. Conclude with `h`.
-/
theorem val_congr {C C' : Formalism.MainNotions.Inhab.FC} {cD cD' ch ch' : ℝ} {D : D7} {L : SizeData₂ D} (h1 : C = C') (h2 : cD = cD')
    (h3 : ch = ch') (h : Val C cD ch L) : Val C' cD' ch' L := by
  subst h1 h2 h3
  exact h

/- English proof (translation)
Use `⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨c1, h1⟩` from `szRow_sizesAt eps he h52 C hC`. Use `⟨c1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨c2, h2⟩` from `h1 cD hcD`. Use `⟨c2, fun ch hch _ => ?_⟩` and prove the remaining obligations.

Take `⟨x0, h3⟩` from `h2 ch hch`. Use `⟨x0, fun K hK hx β _ c b _ => ?_⟩` and prove the remaining obligations. Take `⟨e1, e2, e3, e4, -⟩` from `hK`. Establish `hv : Val C cD ch β.O.L` using `val_congr e1 e2 e3 (β.p.pt_val β.val)`. Establish `hs : β.O.L.sc = K.s` using `β.sc`.

Use `⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `e4`. Rewrite using `[hs]`. Conclude with `hx`.
-/
theorem val_sizes_at (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p)
    (fun κ _ O _ _ => Std κ.C ∧ Val κ.C κ.cD κ.ch O.L ∧ SizesAt O.L) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, h1⟩ := szRow_sizesAt eps he h52 C hC
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h2⟩ := h1 cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x0, h3⟩ := h2 ch hch
  refine ⟨x0, fun K hK hx β _ c b _ => ?_⟩
  obtain ⟨e1, e2, e3, e4, -⟩ := hK
  have hv : Val C cD ch β.O.L := val_congr e1 e2 e3 (β.p.pt_val β.val)
  have hs : β.O.L.sc = K.s := β.sc
  refine ⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩
  · rw [hs]; exact e4
  · rw [hs]; exact hx

/- English proof (translation)
Introduce `hL p` and use `((val_sizes_at hL p).and (GlobalTheory.Fam.MemberCount.member_rankMu hL p)).imp fun _ _ β _ _ _ _ _ H => dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2`.
-/
theorem dataNW_at : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := fun hL p =>
  ((val_sizes_at hL p).and (GlobalTheory.Fam.MemberCount.member_rankMu hL p)).imp fun _ _ β _ _ _ _ _ H =>
    dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2

end GlobalTheory.Fam.MemberData

end
