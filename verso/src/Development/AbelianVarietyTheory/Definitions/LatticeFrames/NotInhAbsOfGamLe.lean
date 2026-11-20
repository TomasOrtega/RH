import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def IdE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def TrueE (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ ∃ w : World I l Z, IdE w.S.X

/- English proof (translation)
The claim follows from `let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩`.
-/
theorem TrueE.trueD {D : D7} (h : TrueE D) : TrueD D :=
  let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

/- English proof (translation)
Take `⟨B, X, I, l, Z, rfl, w, hw⟩` from `hD`. Conclude with `h B X I l Z w hw`.
-/
theorem TrueE.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z),
      IdE w.S.X → Q (I.rec7 l Z)) {D : D7} (hD : TrueE D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, w, hw⟩ := hD
  exact h B X I l Z w hw

def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ Deg.DataNW D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def TrivialRankCondition (_D : D7) (_L _C' : ℝ) : Prop := True

def LedE (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C'

def AndE (E E' : D7 → ℝ → ℝ → Prop) (D : D7) (L C' : ℝ) : Prop := E D L C' ∧ E' D L C'

def GapE (D : D7) (_L _C' : ℝ) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def GamLe (D : D7) (L C' : ℝ) : Prop := ∀ u : D.what₂.Word, 8 * Real.log (D.mem u).A.GamP ≤ C' * mfL D L

def CodeE (D : D7) (L C' : ℝ) : Prop :=
  GapE D L C' ∧ GamLe D L C' ∧ (∀ u : D.what₂.Word, C' * (D.mem u).A.GamP ^ 2 ≤ (Fintype.card D.what₂.Word : ℝ)) ∧
    (D.host.g 0 : ℝ) * D.host.g 1 ≤ Real.exp L ^ 19 ∧ C' * Real.log D.R.r ≤ D.R.f

def Row (E : D7 → ℝ → ℝ → Prop) (Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, 1 ≤ C ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (u : D.what₂.Word), TrueE D → E D L C' → HD D L C' Cl Cg cb Cu cT CT → Q D u L C

variable (E : D7 → ℝ → ℝ → Prop)

def RowDiag : Prop := Row E fun D u L C => SDiag D u L C

def RowMI : Prop := Row E fun D u _ _ => MIKerTower D u

def RowOnto : Prop := Row E fun D _ _ _ => OntoTower D

def RowKer : Prop := Row E fun D u _ _ => KerIncl D u

def RowShare : Prop := Row E fun D u _ _ => RamShare D u

def RKRow : Prop := Row E fun D u L C => Small D u L C → RK D u

def RKRowG : Prop := Row E fun D u L C => RankMu D u → C * mfL D L ≤ Real.log (D.mem u).A.GamP → RK D u

def RowAbs : Prop := Row E fun D u L C => SAbs D u (Real.exp (C * D.R.f * D.R.k * L))

def RKRowAbs : Prop := Row E fun D u L C => RankMu D u → C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP → RK D u

def RowRoad2 : Prop := Row E fun D _ L C =>
  (∀ u, RankMu D u ∧ C * mfL D L ≤ Real.log (D.mem u).A.GamP) → ∃ u, Road2At D u

def RKFam : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, ∀ (F : Pts) (L : ℝ → ℝ) (C' Cl : ℝ), C'₀ ≤ C' → Cl₀ ≤ Cl →
    F.EvAll (fun x D u => TrueE D ∧ E D (L x) C' ∧ HD D (L x) C' Cl Cg cb Cu cT CT ∧ RankMu D u ∧
      C * mfL D (L x) ≤ Real.log (D.mem u).A.GamP) → F.RKAll

def Inh (P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, P D u L C

def InhG : Prop := Inh E fun D u L C => RankMu D u ∧ C * mfL D L ≤ Real.log (D.mem u).A.GamP

def InhAbs : Prop := Inh E fun D u L C => RankMu D u ∧ C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP

def RowsInh : Prop := InhG (AndE GapE LedE) ∧ InhG CodeE ∧ InhAbs GapE

variable {E}

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2 ⟨C, a, b, hC, fun C' Cl ha hb D L u hD _ hH => h C' Cl ha hb D L u hD trivial hH⟩`.
-/
theorem Row.of_noE {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Row TrivialRankCondition Q) : Row E Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD _ hH => h C' Cl ha hb D L u hD trivial hH⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2 let ⟨_, a', b', _, h'⟩ := h' Cg cb Cu cT CT h1 h2 ⟨C, max a a', max b b', hC, fun C' Cl ha hb D L u hD hE hH => ⟨h C' Cl (le_trans (le_max_left _ _) ha) (le_trans (le_max_left _ _) hb) D L u hD hE hH, h' C' Cl (le_trans (le_max_right …`.
-/
theorem Row.and {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} {Q' : ∀ D : D7, D.what₂.Word → Prop} (h : Row E Q)
    (h' : Row E fun D u _ _ => Q' D u) : Row E fun D u L C => Q D u L C ∧ Q' D u := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  let ⟨_, a', b', _, h'⟩ := h' Cg cb Cu cT CT h1 h2
  ⟨C, max a a', max b b', hC, fun C' Cl ha hb D L u hD hE hH =>
    ⟨h C' Cl (le_trans (le_max_left _ _) ha) (le_trans (le_max_left _ _) hb) D L u hD hE hH,
      h' C' Cl (le_trans (le_max_right _ _) ha) (le_trans (le_max_right _ _) hb) D L u hD hE hH⟩⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, hC, h⟩ := Row.and (Q' := fun D _ => OntoTower D) h h' Cg cb Cu cT CT h1 h2 ⟨C, a, b, hC, fun C' Cl ha hb D L u hD hE hH => kerIncl_of_tower D u (h C' Cl ha hb D L u hD hE hH).1 (h C' Cl ha hb D L u hD hE hH).2⟩`.
-/
theorem rowKer_of (h : RowMI E) (h' : RowOnto E) : RowKer E := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := Row.and (Q' := fun D _ => OntoTower D) h h' Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD hE hH =>
    kerIncl_of_tower D u (h C' Cl ha hb D L u hD hE hH).1 (h C' Cl ha hb D L u hD hE hH).2⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, _, h⟩ := h Cg cb Cu cT CT h1 h2 ⟨C, a, b, fun _ L C' Cl ha hb ⟨x₀, hF⟩ => ⟨x₀, fun x hx i => let ⟨h3, h4, h5, h6, h7⟩ := hF x hx i (D7.u₀ _) ⟨_, h C' Cl ha hb _ (L x) _ h3 h4 h5 h6 h7⟩⟩⟩`.
-/
theorem rkFam_of (h : RKRowG E) : RKFam E := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, _, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, fun _ L C' Cl ha hb ⟨x₀, hF⟩ => ⟨x₀, fun x hx i =>
    let ⟨h3, h4, h5, h6, h7⟩ := hF x hx i (D7.u₀ _)
    ⟨_, h C' Cl ha hb _ (L x) _ h3 h4 h5 h6 h7⟩⟩⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2 ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩`.
-/
theorem Row.of_imp {E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Row E Q) : Row E' Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT h1 h2` and use `let ⟨C, a, b, h⟩ := h Cg cb Cu cT CT h1 h2 ⟨C, a, b, fun F L C' Cl ha hb ⟨x₀, hF⟩ => h F L C' Cl ha hb ⟨x₀, fun x hx i u => let ⟨h3, h4, h5⟩ := hF x hx i u ⟨h3, hE _ _ _ h4, h5⟩⟩⟩`.
-/
theorem RKFam.of_imp {E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') (h : RKFam E) : RKFam E' :=
  fun Cg cb Cu cT CT h1 h2 =>
    let ⟨C, a, b, h⟩ := h Cg cb Cu cT CT h1 h2
    ⟨C, a, b, fun F L C' Cl ha hb ⟨x₀, hF⟩ => h F L C' Cl ha hb ⟨x₀, fun x hx i u =>
      let ⟨h3, h4, h5⟩ := hF x hx i u
      ⟨h3, hE _ _ _ h4, h5⟩⟩⟩

/- English proof (translation)
The claim follows from `let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h ⟨Cg, cb, Cu, cT, CT, h1, h2, fun C a b => let ⟨C', Cl, L, D, ha, hb, hD, he, hH⟩ := h C a b ⟨C', Cl, L, D, ha, hb, hD, hE _ _ _ he, hH⟩⟩`.
-/
theorem Inh.of_imp {E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E D L C' → E' D L C') {P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Inh E P) : Inh E' P :=
  let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h
  ⟨Cg, cb, Cu, cT, CT, h1, h2, fun C a b =>
    let ⟨C', Cl, L, D, ha, hb, hD, he, hH⟩ := h C a b
    ⟨C', Cl, L, D, ha, hb, hD, hE _ _ _ he, hH⟩⟩

/- English proof (translation)
The claim follows from `let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2 let ⟨C', Cl, L, D, ha, hb, hD, he, hH, hP⟩ := h C a b ⟨D, L, C, hD, hC, fun u => h' C' Cl ha hb D L u hD he hH (hP u)⟩`.
-/
theorem Inh.reach {P Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) (h' : Row E fun D u L C => P D u L C → Q D u L C) :
    ∃ (D : D7) (L C : ℝ), TrueE D ∧ 1 ≤ C ∧ ∀ u, Q D u L C :=
  let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h
  let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2
  let ⟨C', Cl, L, D, ha, hb, hD, he, hH, hP⟩ := h C a b
  ⟨D, L, C, hD, hC, fun u => h' C' Cl ha hb D L u hD he hH (hP u)⟩

/- English proof (translation)
Introduce `h'` and use `let ⟨D, _, _, _, _, h⟩ := h.reach (Q := fun _ _ _ _ => False) h' h D.u₀`.
-/
theorem Inh.not_row_false {P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) :
    ¬ Row E fun D u L C => P D u L C → False := fun h' =>
  let ⟨D, _, _, _, _, h⟩ := h.reach (Q := fun _ _ _ _ => False) h'
  h D.u₀

/- English proof (translation)
The claim follows from `let ⟨D, _, _, hD, _, h⟩ := Inh.reach (Q := fun D u _ _ => RK D u) h fun Cg cb Cu cT CT h1 h2 => let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2 ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH hP => h' C' Cl ha hb D L u hD he hH hP.1 hP.2⟩ ⟨D, hD, h⟩`.
-/
theorem InhG.rk (h : InhG E) (h' : RKRowG E) : ∃ D : D7, TrueE D ∧ ∀ u, RK D u :=
  let ⟨D, _, _, hD, _, h⟩ := Inh.reach (Q := fun D u _ _ => RK D u) h fun Cg cb Cu cT CT h1 h2 =>
    let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2
    ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH hP => h' C' Cl ha hb D L u hD he hH hP.1 hP.2⟩
  ⟨D, hD, h⟩

/- English proof (translation)
Use `⟨D.R.N D.R.m, ?_, fun τ i hi => ?_⟩` and prove the remaining obligations. Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.rankX' Ranks.N Ranks.r`. Rewrite using `[Nat.mul_add]`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `h D.u₀ τ i.1 hi`. Rewrite `h1` using `[D.hcW_b]`. Simplify using `only [Fin.eta] at h1`. Establish `h2 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3` using `by positivity`.

Establish `h3 : (0 : ℝ) ≤ D.R.t` using `by positivity`. Establish `key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ)`. Use `le_trans ?_ h1` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `key` after adjusting the coercions.
-/
theorem GapE.nodeGap {D : D7} {L C' : ℝ} (h : GapE D L C') : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  refine ⟨D.R.N D.R.m, ?_, fun τ i hi => ?_⟩
  · have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    unfold Ranks.rankX' Ranks.N Ranks.r
    rw [Nat.mul_add]
    omega
  · have h1 := h D.u₀ τ i.1 hi
    rw [D.hcW_b] at h1
    simp only [Fin.eta] at h1
    have h2 : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
    have h3 : (0 : ℝ) ≤ D.R.t := by positivity
    have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
        (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
      refine le_trans ?_ h1
      push_cast
      linarith
    exact_mod_cast key

/- English proof (translation)
The claim follows from `P.nodeGap_ge_cubic_rank`.
-/
theorem GapE.of_params {D : D7} {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) (L C' : ℝ) : GapE D L C' := P.nodeGap_ge_cubic_rank

/- English proof (translation)
Take `⟨h1, -, h3, h4, -⟩` from `hH`. Establish `hm` using `D.R.two_le_m`. Establish `h16 : 2 ^ 4 ≤ D.R.m ^ 4` using `Nat.pow_le_pow_left hm 4`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by omega : 1 ≤ D.R.f)`. Establish `hm' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5` using `one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))`.

Use `⟨?_, by omega, by omega⟩` and prove the remaining obligations. Unfold `mfL`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm' hf) h1.le`.
-/
theorem one_le_mfL {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1 ≤ mfL D L ∧ 16 ≤ D.R.k ∧ 1 ≤ D.R.f := by
  obtain ⟨h1, -, h3, h4, -⟩ := hH
  have hm := D.R.two_le_m
  have h16 : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hm' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  refine ⟨?_, by omega, by omega⟩
  unfold mfL
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm' hf) h1.le

/- English proof (translation)
Take `⟨large₂, hL, h8⟩` from `h`. Introduce `u`. Establish `hG` using `large₂.Gam_eq u`. Establish `hL0 : 0 ≤ L` using `hL ▸ Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _`. Rewrite `hG` using `[hL]`.

Establish `hx : 0 ≤ mfL D L` using `by unfold mfL; positivity`. Establish `e : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D L` using `by rw [hG]; unfold mfL; ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem LedE.gamLe {D : D7} {L C' : ℝ} (h : LedE D L C') : GamLe D L C' := by
  obtain ⟨large₂, hL, h8⟩ := h
  intro u
  have hG := large₂.Gam_eq u
  have hL0 : 0 ≤ L := hL ▸ Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _
  rw [hL] at hG
  have hx : 0 ≤ mfL D L := by unfold mfL; positivity
  have e : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D L := by rw [hG]; unfold mfL; ring
  rw [e]
  nlinarith

/- English proof (translation)
Use `(h u).trans (le_trans (le_of_eq ?_) hH.2.1)` and prove the remaining obligations. Unfold `mfL`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GamLe.le_k {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (u : D.what₂.Word) : 8 * Real.log (D.mem u).A.GamP ≤ D.R.k := by
  refine (h u).trans (le_trans (le_of_eq ?_) hH.2.1)
  unfold mfL
  ring

/- English proof (translation)
Establish `h1` using `h.le_k hH u`. Take `⟨-, hk, hf⟩` from `one_le_mfL hH`. Establish `hk' : (16 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hf' : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `a : (1 : ℝ) ≤ C * D.R.f * L` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hf') hH.1.le`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem GamLe.log_lt {D : D7} {L C C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (hC : 1 ≤ C) (u : D.what₂.Word) : Real.log (D.mem u).A.GamP < C * D.R.f * D.R.k * L := by
  have h1 := h.le_k hH u
  obtain ⟨-, hk, hf⟩ := one_le_mfL hH
  have hk' : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have a : (1 : ℝ) ≤ C * D.R.f * L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hf') hH.1.le
  nlinarith

/- English proof (translation)
Introduce `_ _ _ _ _ _ _` and use `⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH _ h => absurd h (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩`.
-/
theorem RKRowAbs.of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : RKRowAbs E :=
  fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH _ h =>
    absurd h (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

/- English proof (translation)
Introduce `h` and use `Inh.not_row_false h fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH h => absurd h.2 (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩`.
-/
theorem not_inhAbs_of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : ¬ InhAbs E := fun h =>
  Inh.not_row_false h fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH h =>
    absurd h.2 (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

/- English proof (translation)
The claim follows from `RKRowAbs.of_gamLe fun _ _ _ => LedE.gamLe`.
-/
example : RKRowAbs LedE := RKRowAbs.of_gamLe fun _ _ _ => LedE.gamLe

/- English proof (translation)
The claim follows from `not_inhAbs_of_gamLe fun _ _ _ => LedE.gamLe`.
-/
example : ¬ InhAbs LedE := not_inhAbs_of_gamLe fun _ _ _ => LedE.gamLe

/- English proof (translation)
Take `⟨hx, hk, -⟩` from `one_le_mfL hH`. Establish `hG : 0 < (D.mem u).A.GamP` using `one_pos.trans (D.mem u).A.one_lt_gammaP`. Break down `le_or_gt C' 0 with h0 | h0` into its components or cases. Conclude with `le_trans (mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)) (by positivity)`. Establish `hC : C' ≤ D.R.k`.

Establish `: C' * mfL D L ≤ D.R.k` using `le_trans (le_of_eq (by unfold mfL; ring)) hH.2.1`. Use the polynomial consequences of the given equalities and inequalities. Establish `he : Real.exp (1 / 4) ≤ 4 / 3`. Establish `h1 : Real.exp (1 / 4) ^ 4 = Real.exp 1` using `by rw [← Real.exp_nat_mul]; norm_num`. Use `le_of_not_gt fun h2 => ?_` and prove the remaining obligations.

Establish `h3 : (4 / 3 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4` using `pow_le_pow_left₀ (by norm_num) h2.le 4`. Use `Real.exp_one_lt_d9` as an intermediate fact. Evaluate the numerical expressions using `at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (D.mem u).A.GamP ^ 2 ≤ (4 / 3 : ℝ) ^ D.R.k`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hG]`. Use `_ ≤ Real.exp ((D.R.k : ℝ) * (1 / 4)) := Real.exp_le_exp.2 (by have := h.le_k hH u; linarith)`. Use `_ = Real.exp (1 / 4) ^ D.R.k := Real.exp_nat_mul _ _`. Use `_ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he _`.

Establish `h3 : ∀ n : ℕ, 16 ≤ n → 8 * ((n : ℝ) * (4 / 3) ^ n) ≤ 2 ^ n`. Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ n hn ih`.

Establish `hn' : (16 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hp : (0 : ℝ) < (4 / 3) ^ n` using `by positivity`. Rewrite using `[pow_succ, pow_succ]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h4` using `h3 _ hk`. Establish `h5 : (2 : ℝ) ^ D.R.k = 8 * 2 ^ (D.R.k - 3)`. Rewrite using `[show D.R.k = 3 + (D.R.k - 3) by omega, pow_add]`. Evaluate the numerical expressions. Establish `h6 : C' * (D.mem u).A.GamP ^ 2 ≤ D.R.k * (4 / 3 : ℝ) ^ D.R.k` using `mul_le_mul hC h2 (by positivity) (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GamLe.code_room {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (u : D.what₂.Word) : C' * (D.mem u).A.GamP ^ 2 ≤ 2 ^ (D.R.k - 3) := by
  obtain ⟨hx, hk, -⟩ := one_le_mfL hH
  have hG : 0 < (D.mem u).A.GamP := one_pos.trans (D.mem u).A.one_lt_gammaP
  rcases le_or_gt C' 0 with h0 | h0
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)) (by positivity)
  have hC : C' ≤ D.R.k := by
    have : C' * mfL D L ≤ D.R.k := le_trans (le_of_eq (by unfold mfL; ring)) hH.2.1
    nlinarith
  have he : Real.exp (1 / 4) ≤ 4 / 3 := by
    have h1 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    refine le_of_not_gt fun h2 => ?_
    have h3 : (4 / 3 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) h2.le 4
    have := Real.exp_one_lt_d9
    norm_num at h3
    linarith
  have h2 : (D.mem u).A.GamP ^ 2 ≤ (4 / 3 : ℝ) ^ D.R.k := by
    calc (D.mem u).A.GamP ^ 2 = Real.exp (2 * Real.log (D.mem u).A.GamP) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hG]
      _ ≤ Real.exp ((D.R.k : ℝ) * (1 / 4)) := Real.exp_le_exp.2 (by have := h.le_k hH u; linarith)
      _ = Real.exp (1 / 4) ^ D.R.k := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he _
  have h3 : ∀ n : ℕ, 16 ≤ n → 8 * ((n : ℝ) * (4 / 3) ^ n) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
      have hp : (0 : ℝ) < (4 / 3) ^ n := by positivity
      rw [pow_succ, pow_succ]
      push_cast
      nlinarith
  have h4 := h3 _ hk
  have h5 : (2 : ℝ) ^ D.R.k = 8 * 2 ^ (D.R.k - 3) := by
    rw [show D.R.k = 3 + (D.R.k - 3) by omega, pow_add]
    norm_num
  have h6 : C' * (D.mem u).A.GamP ^ 2 ≤ D.R.k * (4 / 3 : ℝ) ^ D.R.k := mul_le_mul hC h2 (by positivity) (by positivity)
  linarith

/- English proof (translation)
Establish `h1` using `h.2.2.1 D.u₀`. Establish `h2` using `(D.mem D.u₀).A.one_lt_gammaP`. Establish `h3 : (1 : ℝ) < (Fintype.card D.what₂.Word : ℝ)` using `by nlinarith`. Conclude with `h3` after adjusting the coercions.
-/
theorem CodeE.one_lt_card {D : D7} {L C' : ℝ} (h : CodeE D L C') (hC : 1 ≤ C') : 1 < Fintype.card D.what₂.Word := by
  have h1 := h.2.2.1 D.u₀
  have h2 := (D.mem D.u₀).A.one_lt_gammaP
  have h3 : (1 : ℝ) < (Fintype.card D.what₂.Word : ℝ) := by nlinarith
  exact_mod_cast h3

/- English proof (translation)
Assemble the required witnesses or components as `⟨Inh.of_imp (fun _ _ _ h => h.1) h.1, Inh.of_imp (fun _ _ _ _ => trivial) h.1, Inh.of_imp (fun _ _ _ h => h.2) h.1⟩`.
-/
theorem RowsInh.gap (h : RowsInh) : InhG GapE ∧ InhG TrivialRankCondition ∧ InhG LedE :=
  ⟨Inh.of_imp (fun _ _ _ h => h.1) h.1, Inh.of_imp (fun _ _ _ _ => trivial) h.1, Inh.of_imp (fun _ _ _ h => h.2) h.1⟩

end GlobalTheory.Core.Rk

end
