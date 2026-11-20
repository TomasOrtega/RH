import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.LedSize

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨c1, hN⟩` from `GlobalTheory.EX.szRow_numAt eps h0 h1 C hC`. Use `⟨max c1 0, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨c2, hN⟩` from `hN cD ((le_max_left _ _).trans hcD)`. Use `⟨max c2 402, fun ch hch => ?_⟩` and prove the remaining obligations.

Take `⟨x1, hN⟩` from `hN ch ((le_max_left _ _).trans hch)`. Take `⟨x0, hx0⟩` from `GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)`. Use `⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩` and prove the remaining obligations. Introduce and unpack `K rfl rfl rfl hs hx hG X hO heta hA`. Establish `hx'` using `(le_max_left _ _).trans hx`.

Establish `hxL` using `(le_max_right _ _).trans hx`. Establish `hP` using `K.ok`. Establish `hOk` using `hG.ok`. Take `⟨sp, hT, hY, hA', hV, hz, hB, -⟩` from `hO`. Take `⟨B, Cc, W, V, S, N, Gj⟩` from `X`.

Consider the cases of `B`. Simplify using `only at hB`. Substitute `hB` using the available equality. Use `set D := Stages.toD7 _ with hD`. Establish `hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK` using `(Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split`.

Establish `hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ)`. Establish `τ : Tau K.P.R` using `tauPl D (false, 0)`. Establish `hk` using `K.P.R.m_add_three_le_k`. Establish `hm` using `K.P.R.two_le_m`. Establish `hl : 0 + 1 < K.P.R.k - 1` using `by omega`.

Establish `a1` using `D.s.cloud_gap K.P.u₀ τ 0 hl`. Establish `a2` using `congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)`. Establish `a3` using `a1.symm.trans a2`. Establish `e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1` using `by omega`. Simplify using `only at a3`.

Rewrite `a3` using `[e]`. Move the coercions through the operations in `at a3`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨L, e1, -, -, e4⟩` from `hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by`. Establish `e : (D.mem u).A.GamP = K.Lv.GamP` using `Cc.A_GamP u`.

Rewrite using `[e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]`. Use the proof step `rfl)`. Use the proof step `(fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)`. Take `⟨⟨M⟩, -, -⟩` from `hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4 ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩`. Use `⟨L, e1, ?_⟩` and prove the remaining obligations.

Establish `hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X'`. Establish `hmem` using `hOk.small.1`. Break down `hOk.lev _ hmem with ⟨i, hi⟩ | hlt` into its components or cases. Conclude with `absurd hi (hOk.small.2.2.2.1 i)`. Rewrite using `[e1]`.

Conclude with `hlt`. Establish `xe : L.sc.x = K.s.x` using `by rw [e1]`. Establish `ee : L.sc.eps = eps` using `by rw [e1]; exact hs`. Use `GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)` and prove the remaining obligations. Rewrite using `[xe, ee]`.

Establish `e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4)`. Rewrite using `[← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]`. Rewrite using `[e2]`. Conclude with `Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)`.
-/
theorem evG_exists_sizeRows : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩
  rintro K rfl rfl rfl hs hx hG X hO heta hA
  have hx' := (le_max_left _ _).trans hx
  have hxL := (le_max_right _ _).trans hx
  have hP := K.ok
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  refine ⟨L, e1, ?_⟩
  have hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X' := by
    have hmem := hOk.small.1
    rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
    · exact absurd hi (hOk.small.2.2.2.1 i)
    · rw [e1]; exact hlt
  have xe : L.sc.x = K.s.x := by rw [e1]
  have ee : L.sc.eps = eps := by rw [e1]; exact hs
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes
    M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)
  rw [xe, ee]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)

end GlobalTheory.Mem.R3.LedSize

end
