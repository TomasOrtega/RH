import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPins
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierPOfRepairedModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinRX
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def XLeavesP : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
    u ≠ u' → 0 < cb → 0 < cTf → Formalism.BasicNotions.Ties D → 29 ≤ C' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl →
    1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → ∀ hPl : PlaceTie T.X e,
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j))
      (cc : Fin (nfE D) → ℂ),
      XLeafAt T.X Ch u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1
        (T.Y.FN u) (T.Y.FN u') νq (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN a b ξ ξ' cc

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in

/- English proof (translation)
Introduce `C₆ Cc hC6`. Use `⟨max (max (max Cc Cd) Ce) 1, ?_⟩` and prove the remaining obligations. Introduce `CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7`. Use `set Cq : ℝ := 8400 * (|Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst|) + 48120 with hCq`. Take `⟨k1, hk1⟩` from `lenI_big CDel Cb' Cq a4 a6`.

Use `⟨max k1 1801, fun Cg cb Cw cTf CT C0f hcb hcT => ⟨29, max (max 1000 (25000 + 21 * (|Cc| + |Cd| + |Ce|))) (1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose|), ?_⟩⟩` and prove the remaining obligations. Introduce `C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTies hne hk hH0 hPl hSz hi hPt hNu`. Establish `hClp : 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl` using `le_trans (le_max_right _ _) hCl`. Establish `hk18' : 1801 ≤ D.R.k`. Establish `: 1801 ≤ (gOf D e).k` using `le_trans (le_max_right _ _) hk`.

Conclude with `this`. Take `⟨θ, Ch, a, b, ξ, ξ', cc, hleaf⟩` from `hX CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hne hcb hcT hTies hC' hClp hk18' hH0 hPl hSz hi hPt hNu`. Establish `h5` using `Formalism.MainNotions.BridgeLemma.last_shifted_parameter_eq hH0.2.1`. Take `⟨hG, hw, hw', hl1, hl2, hne', -⟩` from `hSz`. Establish `hOk : ∀ w, ((gOf D e).place w).Ok` using `hG.hplace`.

Establish `hcard : 0 < Fintype.card (InfinitePlace D.host.E)`. Establish `h1 : (gOf D e).m ≤ (gOf D e).f` using `hG.hmf`. Establish `h2 : (gOf D e).f = Fintype.card (InfinitePlace D.host.E)` using `rfl`. Establish `h3 : (gOf D e).m = 2 * (gOf D e).r + 2` using `rfl`. Use linear arithmetic over natural numbers and integers.

Take `⟨w⟩` from `Fintype.card_pos_iff.mp hcard`. Establish `hDel1 : (1 : ℝ) ≤ (D.s.Del : ℝ)` using `(hOk w).hDel`. Establish `hDel0 : (D.s.Del : ℝ) ≠ 0` using `by linarith`. Establish `hde` using `Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u`. Establish `hde'` using `Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u'`.

Establish `hkk : k1 ≤ (gOf D e).k` using `le_trans (le_max_left _ _) hk`. Establish `hlenI` using `hk1 (gOf D e) L.sc.b hkk hG`. Establish `hlenI' : Cq * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2` using `hlenI`. Take `⟨p1, p2, p3⟩` from `polys D.R.k D.R.rS`. Establish `hQ0 : 0 ≤ (D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4` using `by positivity`.

Establish `hCqc : ∀ c : ℝ, |c| ≤ |Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst| → 8400 * |c| * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2`. Introduce `c hc`. Use `le_trans ?_ hlenI'` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ hQ0` to reduce the goal to its premises. Rewrite using `[hCq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ac` using `abs_nonneg Cc`. Establish `ad` using `abs_nonneg Cd`. Establish `a6'` using `abs_nonneg C₆`. Establish `ae` using `abs_nonneg Ce`.

Establish `a6e` using `abs_nonneg fourierDecayLevelZeroConst`. Establish `hLc` using `scale_le (by positivity) p1 (hCqc Cc (by linarith))`. Establish `hLd` using `scale_le (by positivity) p1 (hCqc Cd (by linarith))`. Establish `hC6'` using `scale_le (by positivity) p2 (hCqc C₆ (by linarith))`. Establish `hLe` using `scale_le (by positivity) p1 (hCqc Ce (by linarith))`.

Establish `hC6e` using `scale_le (by positivity) p2 (hCqc fourierDecayLevelZeroConst (by linarith))`. Establish `hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤ (D.s.Del : ℝ) / 2 - 5 / 2`. Use `le_trans p3 (le_trans ?_ hlenI')` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ hQ0` to reduce the goal to its premises. Rewrite using `[hCq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCA' : Cc ≤ CA` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCA`. Establish `hCAd : Cd ≤ CA` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hCA`. Establish `hCAe : Ce ≤ CA` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCA`. Establish `hS0` using `hH0.1`.

Establish `hCl1000 : (1000 : ℝ) ≤ Cl` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl`. Establish `hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)` using `fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 (e (plE D j))`. Establish `hrS : 2 * D.R.rS + 2 = D.R.m` using `Ranks.rS_two D.R`. Establish `hr : D.R.r = 2 * D.R.rS + D.R.k + 1` using `by unfold Ranks.r; omega`. Establish `hkL` using `Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ`.

Establish `hk5 : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hL : (1 / 2 : ℝ) ≤ L.sc.L`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1 : Real.exp (2 * L.sc.L) < Real.exp 1` using `Real.exp_lt_exp.mpr (by linarith)`.

Establish `h2 : Real.exp 1 < 3` using `by have := Real.exp_one_lt_d9; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : (2 : ℝ) ≤ (D.R.f : ℝ)`. Establish `: 2 ≤ D.R.f`. Unfold `Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`.

Conclude with `this` after adjusting the coercions. Establish `hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5`. Establish `: (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5` using `pow_le_pow_left₀ (by norm_num) hf 5`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1`. Establish `: 1801 ≤ (gOf D e).k` using `le_trans (le_max_right _ _) hk`. Establish `e1 : (gOf D e).k = D.R.k` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hn1 : (1 : ℝ) ≤ (D.R.r : ℝ)` using `by rw [hr]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1)`.

Establish `hn19 : 0 ≤ (D.R.r : ℝ) ^ 19` using `by positivity`. Establish `hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L`. Establish `e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5` using `mul_le_mul_of_nonneg_left hf5 (by positivity)`. Establish `e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L` using `mul_le_mul_of_nonneg_left hL (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)`. Use `gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega) hn1801) ?_` and prove the remaining obligations. Establish `: ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ)` using `by rw [hr]`. Rewrite using `[this]`. Establish `h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19` using `mul_le_mul_of_nonneg_right (by linarith) hn19`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAh : decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / 2`. Unfold `decayThreshold`. Establish `habs : |(|Cc| + |Cd| + |Ce|)| = |Cc| + |Cd| + |Ce|` using `abs_of_nonneg (by positivity)`. Rewrite using `[habs]`.

Establish `hn' : (2 * (D.R.rS : ℝ) + D.R.k + 1) = (D.R.r : ℝ)` using `by rw [hr]; push_cast; ring`. Rewrite using `[hn']`. Establish `hCl2 : 25000 + 21 * (|Cc| + |Cd| + |Ce|) ≤ Cl` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl`. Establish `h7 : (D.R.r : ℝ) ^ 7 ≤ (D.R.r : ℝ) ^ 19` using `pow_le_pow_right₀ hn1 (by norm_num)`. Establish `hn7 : 0 ≤ (D.R.r : ℝ) ^ 7` using `by positivity`.

Establish `hn19' : 0 ≤ (D.R.r : ℝ) ^ 19` using `by positivity`. Establish `e1 : (25000 + 21 * (|Cc| + |Cd| + |Ce|)) * (D.R.r : ℝ) ^ 7 ≤ Cl * (D.R.r : ℝ) ^ 19` using `mul_le_mul hCl2 h7 hn7 (by linarith)`. Establish `hc0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19` using `mul_nonneg (by linarith) hn19'`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `carrierDataBuilt_of_hyp T.X Ch Cb hLift capacity_from_hermitian_char hH0.1 hCl1000 (by have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk; exact this) Cc C₆ u u' e hPl CA (deOf D τ u) (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a …`.
-/
theorem carrierXSideP_of_leaves (Cb : ℝ) (hLift : LiftAt3 Cb) (hX : XLeavesP) : CarrierSideBoundPositive Cb := by
  intro C₆ Cc hC6
  refine ⟨max (max (max Cc Cd) Ce) 1, ?_⟩
  intro CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7
  set Cq : ℝ := 8400 * (|Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst|) + 48120 with hCq
  obtain ⟨k1, hk1⟩ := lenI_big CDel Cb' Cq a4 a6
  refine ⟨max k1 1801, fun Cg cb Cw cTf CT C0f hcb hcT => ⟨29, max (max 1000 (25000 + 21 * (|Cc| + |Cd| + |Ce|))) (1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose|), ?_⟩⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTies hne hk hH0 hPl hSz hi hPt hNu
  have hClp : 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl := le_trans (le_max_right _ _) hCl
  have hk18' : 1801 ≤ D.R.k := by
    have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk
    exact this
  obtain ⟨θ, Ch, a, b, ξ, ξ', cc, hleaf⟩ :=
    hX CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hne hcb hcT hTies hC' hClp hk18' hH0 hPl hSz
      hi hPt hNu
  have h5 := Formalism.MainNotions.BridgeLemma.last_shifted_parameter_eq hH0.2.1
  obtain ⟨hG, hw, hw', hl1, hl2, hne', -⟩ := hSz
  have hOk : ∀ w, ((gOf D e).place w).Ok := hG.hplace

  have hcard : 0 < Fintype.card (InfinitePlace D.host.E) := by
    have h1 : (gOf D e).m ≤ (gOf D e).f := hG.hmf
    have h2 : (gOf D e).f = Fintype.card (InfinitePlace D.host.E) := rfl
    have h3 : (gOf D e).m = 2 * (gOf D e).r + 2 := rfl
    omega
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hcard
  have hDel1 : (1 : ℝ) ≤ (D.s.Del : ℝ) := (hOk w).hDel
  have hDel0 : (D.s.Del : ℝ) ≠ 0 := by linarith
  have hde := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u
  have hde' := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u'

  have hkk : k1 ≤ (gOf D e).k := le_trans (le_max_left _ _) hk
  have hlenI := hk1 (gOf D e) L.sc.b hkk hG
  have hlenI' : Cq * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := hlenI
  obtain ⟨p1, p2, p3⟩ := polys D.R.k D.R.rS
  have hQ0 : 0 ≤ (D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4 := by positivity
  have hCqc : ∀ c : ℝ, |c| ≤ |Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst| →
      8400 * |c| * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
    intro c hc
    refine le_trans ?_ hlenI'
    apply mul_le_mul_of_nonneg_right _ hQ0
    rw [hCq]; linarith
  have ac := abs_nonneg Cc
  have ad := abs_nonneg Cd
  have a6' := abs_nonneg C₆
  have ae := abs_nonneg Ce
  have a6e := abs_nonneg fourierDecayLevelZeroConst
  have hLc := scale_le (by positivity) p1 (hCqc Cc (by linarith))
  have hLd := scale_le (by positivity) p1 (hCqc Cd (by linarith))
  have hC6' := scale_le (by positivity) p2 (hCqc C₆ (by linarith))
  have hLe := scale_le (by positivity) p1 (hCqc Ce (by linarith))
  have hC6e := scale_le (by positivity) p2 (hCqc fourierDecayLevelZeroConst (by linarith))
  have hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
    refine le_trans p3 (le_trans ?_ hlenI')
    apply mul_le_mul_of_nonneg_right _ hQ0
    rw [hCq]; linarith

  have hCA' : Cc ≤ CA := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCA
  have hCAd : Cd ≤ CA := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hCA
  have hCAe : Ce ≤ CA := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCA

  have hS0 := hH0.1
  have hCl1000 : (1000 : ℝ) ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) :=
    fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 (e (plE D j))
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hc
    push Not at hc
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    exact_mod_cast this
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
    norm_num at this; linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by
    have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk
    have e1 : (gOf D e).k = D.R.k := rfl
    omega
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1)
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity

  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega) hn1801) ?_
    have : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
    rw [this]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAh : decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / 2 := by
    unfold decayThreshold
    have habs : |(|Cc| + |Cd| + |Ce|)| = |Cc| + |Cd| + |Ce| := abs_of_nonneg (by positivity)
    rw [habs]
    have hn' : (2 * (D.R.rS : ℝ) + D.R.k + 1) = (D.R.r : ℝ) := by rw [hr]; push_cast; ring
    rw [hn']
    have hCl2 : 25000 + 21 * (|Cc| + |Cd| + |Ce|) ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
    have h7 : (D.R.r : ℝ) ^ 7 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have hn7 : 0 ≤ (D.R.r : ℝ) ^ 7 := by positivity
    have hn19' : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have e1 : (25000 + 21 * (|Cc| + |Cd| + |Ce|)) * (D.R.r : ℝ) ^ 7 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
      mul_le_mul hCl2 h7 hn7 (by linarith)
    have hc0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith) hn19'
    linarith
  exact carrierDataBuilt_of_hyp T.X Ch Cb hLift capacity_from_hermitian_char hH0.1 hCl1000
    (by have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk; exact this) Cc C₆ u u' e hPl CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' cc hleaf h5 hde hde' hOk hw hw'
    hl1 hl2 hne' hlen hLc hLd hC6' hCA' hCAd hLe hC6e hCAe _ hgap hok hAh hi hPt one_pos hNu
    (fun Θ TP A₀ hBuilt => energy_compact_test_bound T Ch u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
      (lOf D (deOf D τ u) (deOf D τ u')) a b ξ ξ' cc i0' Θ TP A₀ X0 sd C Th vR Q i0 i0' νq (hleaf.2.2 Θ TP A₀) hBuilt)

def XPinsP : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → 0 < cb → 0 < cTf → Formalism.BasicNotions.Ties D → 29 ≤ C' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl → 1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → PlaceTie T.X e →
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (hB : WuBessel Ch) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)),
      HypTT D u u' ∧ 0 < Tr D u ∧ 0 < Tr D u' ∧
      (∀ j, GoodW D (e (plE D j)) u u' θ (locW Ch u u' (e (plE D j)))) ∧
      (∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j)))) ∧
      (∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1) ∧
      (∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) ∧ (∀ j, cOf hB u (e (plE D j)) ≠ 0)

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
/- English proof (translation)
Introduce `CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz hi hPt hNu`. Take `⟨θ, Ch, hB, a, b, ξ, ξ', hTT, hT, hT', hW, hA, hpin1, hscl, hcO⟩` from `hP CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz hi hPt hNu`. Establish `hCl : (1000 : ℝ) ≤ Cl` using `by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith`. Establish `hS0` using `hH0.1`. Establish `hrS : 2 * D.R.rS + 2 = D.R.m` using `Ranks.rS_two D.R`.

Establish `hr : D.R.r = 2 * D.R.rS + D.R.k + 1` using `by unfold Ranks.r; omega`. Establish `hkL` using `Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ`. Establish `hk5 : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hL : (1 / 2 : ℝ) ≤ L.sc.L`. Assume the negation of the conclusion as `hcn`.

Use `push Not at hcn`. Establish `h1 : Real.exp (2 * L.sc.L) < Real.exp 1` using `Real.exp_lt_exp.mpr (by linarith)`. Establish `h2 : Real.exp 1 < 3` using `by have := Real.exp_one_lt_d9; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : 2 ≤ D.R.f`.

Unfold `Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Establish `hfR : (2 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast hf`. Establish `hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5`. Establish `: (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5` using `pow_le_pow_left₀ (by norm_num) hfR 5`. Evaluate the numerical expressions using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ)` using `by rw [hr]`. Establish `hn1 : (1 : ℝ) ≤ (D.R.r : ℝ)` using `by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith`. Establish `hn19 : 0 ≤ (D.R.r : ℝ) ^ 19` using `by positivity`. Establish `hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L`.

Establish `e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5` using `mul_le_mul_of_nonneg_left hf5 (by positivity)`. Establish `e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L` using `mul_le_mul_of_nonneg_left hL (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1` using `by omega`. Establish `hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L)`.

Use `gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_` and prove the remaining obligations. Rewrite using `[hrr]`. Establish `h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19` using `mul_le_mul_of_nonneg_right (by linarith) hn19`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAch` using `le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])`.

Use `⟨θ, Ch, a, b, ξ, ξ', fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j), ?_⟩` and prove the remaining obligations. Conclude with `xLeafAt_of_pins T.X Ch hB hJ L hCl hH0 u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) (fun j => Formal …`.
-/
theorem xLeavesP_of_pinsP (hJ : PI.BesselMapUniq.BesselMapUniq) (hP : XPinsP) : XLeavesP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hne hcb hcT hTies hC' hClp
    hk18 hH0 hPl hSz hi hPt hNu
  obtain ⟨θ, Ch, hB, a, b, ξ, ξ', hTT, hT, hT', hW, hA, hpin1, hscl, hcO⟩ :=
    hP CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz
      hi hPt hNu
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1

  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  refine ⟨θ, Ch, a, b, ξ, ξ', fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT (hW j)
    (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j), ?_⟩
  exact xLeafAt_of_pins T.X Ch hB hJ L hCl hH0 u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO
    (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
    (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _ (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) _ rfl

def KFinNZ : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    ∃ a : X.B.H (vOf X τ), PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) a ∧ bOf hB u τ a ≠ 0

/- English proof (translation)
Rewrite using `[inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `h : (‖x‖ : ℂ) ^ 2 ≠ 0` using `by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)`. Use `push_cast`. Conclude with `inv_mul_cancel₀ h`.
-/
theorem inner_normalize_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {x : V} (hx : x ≠ 0) :
    ⟪x, (((‖x‖ ^ 2 : ℝ) : ℂ))⁻¹ • x⟫_ℂ = 1 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  have h : (‖x‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  push_cast
  exact inv_mul_cancel₀ h

/- English proof (translation)
Rewrite using `[inner_smul_left, inner_self_eq_norm_sq_to_K]`. Establish `h : (‖y‖ : ℂ) ^ 2 ≠ 0` using `by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)`. Establish `hc : (starRingEnd ℂ) (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ = (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹`. Rewrite using `[map_inv₀, Complex.conj_ofReal]`. Rewrite using `[hc]`.

Use `push_cast`. Conclude with `inv_mul_cancel₀ h`.
-/
theorem inner_normalize_left {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {y : V} (hy : y ≠ 0) :
    ⟪(((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ • y, y⟫_ℂ = 1 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  have h : (‖y‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hc : (starRingEnd ℂ) (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ = (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rw [hc]
  push_cast
  exact inv_mul_cancel₀ h

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

/- English proof (translation)
Introduce `CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz hi hPt hNu`. Use `haveI : Nonempty D.what₂.Word := ⟨u⟩`. Establish `hCl : (1000 : ℝ) ≤ Cl` using `by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith`. Establish `hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D` using `Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH0.1 (by linarith) hC'`. Take `⟨Ch⟩` from `Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos`.

Establish `hB : WuBessel Ch` using `Formalism.L2.SG.Pf.LoopLoc.wuBessel_of hG hJ Ch`. Establish `hLF` using `Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch`. Establish `hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t` using `fun w t => Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2`. Establish `hscl : ∀ t, sclOf hB u u' t ≠ 0`. Introduce `t`.

Establish `h1` using `Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t`. Establish `hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal` using `ENNReal.toReal_pos h1.1 h1.2.ne`. Establish `hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))`. Break down `Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `: Subsingleton (T.X.Vloc u' (vOf T.X t))` using `Module.finrank_zero_iff.1 h`. Apply `h1.1` to reduce the goal to its premises. Unfold `l2SG`. Simplify using `[Subsingleton.elim (phiOf hB u' t _) 0]`. Conclude with `h`.

Unfold `sclOf`. Establish `hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) / (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal` using `div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl`. Conclude with `(Real.sqrt_pos.mpr hpos).ne'` after adjusting the coercions. Establish `ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))), PI.UpqRep.IsKFinHpk (k` using `D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧ bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG`. Establish `hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))), PI.UpqRep.IsKFinHpk (k` using `D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧ bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG`.

Use `choose a ha using ha`. Use `choose b hb using hb`. Use `⟨1, Ch, hB, a, b, fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j), fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j), Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all u u', Nat.cast_ …` and prove the remaining obligations. Rewrite using `[inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul]`.
-/
theorem xPinsP_of (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) : XPinsP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18
    hH0 hPl hSz hi hPt hNu
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH0.1 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.LoopLoc.wuBessel_of hG hJ Ch
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  refine ⟨1, Ch, hB, a, b, fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j),
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j),
    Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all u u', Nat.cast_pos.2 (D.mem u).A.T_prime.pos, Nat.cast_pos.2 (D.mem u').A.T_prime.pos,
    fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j)),
    fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j))),
    fun j => ⟨(ha j).1, (hb j).1, ?_, one_ne_zero⟩, fun j => hscl _, fun j => (hc u _).ne'⟩
  rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul]

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
Take `⟨hPA, hMP, hBB⟩` from `hT`. Take `⟨Cb, hL⟩` from `liftAt3_exists`. Conclude with `Formalism.L2.SG.SpectralTiesReal.carrierP_of_repaired_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))`.
-/
theorem carrierP_of_kFinite (hT : CSTarget) (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := hT
  obtain ⟨Cb, hL⟩ := liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_repaired_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
Take `⟨hPA, hMP, hBB⟩` from `hT`. Take `⟨Cb, hL⟩` from `liftAt3_exists`. Conclude with `Formalism.L2.SG.SpectralTiesReal.carrierP_of_compact_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))`.
-/
theorem carrierP_of_kfin4 (hT : CSTarget4) (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := hT
  obtain ⟨Cb, hL⟩ := liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_compact_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))

def KFinDense : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
Introduce `D X θ C hB u τ hG`. Establish `hLF` using `Formalism.L2.SG.Pf.LocF.locFactor_holds hG C`. Establish `hl` using `(Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ).1`. Take `⟨-, -, hSH, -, -, -, -, -⟩` from `hLF u τ`. Take `⟨hz, hTz⟩` from `Formalism.L2.SG.Pf.zTr C u τ`.

Establish `hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)`. Rewrite using `[hTz]`. Conclude with `Nat.cast_pos.2 (D.mem u).A.T_prime.pos`. Establish `hconc` using `Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) hSH (C.nuS_q u τ)`. Establish `hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)`.

Rewrite using `[ae_iff]`. Conclude with `hconc`. Establish `hex : ∃ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), phiOf hB u τ m ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hl` to reduce the goal to its premises. Unfold `l2SG`. Establish `h0 : (fun x => (‖phiOf hB u τ (Matrix.of x)‖₊ : ENNReal) ^ 2) =ᵐ[C.nuS u τ] 0` using `by filter_upwards [hae] with x hx`. Simplify using `[hcon _ hx]`. Rewrite using `[lintegral_congr_ae h0]`.

Simplify using the standard rewrite rules. Take `⟨m, hm, hΦ⟩` from `hex`. Establish `hds` using `Formalism.L2.SG.Pf.dsTr C τ`. Establish `hlam` using `Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ`. Establish `hv0 : v0Of C τ ∈ smoothVecs (k` using `D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds (Formalism.L2.SG.Pf.isLowUnitH_base_vector C τ)`.

Establish `hv : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) ∈ smoothVecs (k` using `D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hds) hv0 hm`. Establish `hBs` using `(hB u τ).choose_spec.1`. Take `⟨hadd, -, -, Cw, Ws, hWs, hbd⟩` from `hBs`. Establish `hBv : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) ≠ 0` using `hΦ`. Establish `hnB : 0 < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖` using `norm_pos_iff.mpr hBv`.

Use `set δ : ℝ := ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ / (|Cw| + 1) with hδ`. Establish `hδ0 : 0 < δ` using `div_pos hnB (by positivity)`. Take `⟨a, ha, hS⟩` from `hD D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ (sigB X (C.Q τ) (C.Qi τ) τ) hlam hds _ hv Ws hWs δ hδ0`. Use `⟨a, ha, fun hBa => ?_⟩` and prove the remaining obligations. Establish `has : a ∈ smoothVecs (k` using `D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ _ hds a ha`.

Establish `hva : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a ∈ smoothVecs (k` using `D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_sub hv has`. Establish `hsplit : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a) + bOf hB u τ a`. Use `hadd _ hva a has` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this`.

Rewrite `hsplit` using `[hBa, add_zero]`. Establish `hb : ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖ ≤ Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum` using `hbd _ hva`. Rewrite `hb` using `[← hsplit]`. Establish `hS0 : 0 ≤ (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum` using `List.sum_nonneg (fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)`. Establish `h1 : Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum ≤ |Cw| * δ`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : |Cw| * δ < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖`. Rewrite using `[hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]`. Use polynomial arithmetic with `[abs_nonneg Cw]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kFinNZ_of (hD : KFinDense) : KFinNZ := by
  intro D X θ C hB u τ hG
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG C
  have hl := (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ).1
  obtain ⟨-, -, hSH, -, -, -, -, -⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) hSH (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hex : ∃ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), phiOf hB u τ m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hl
    unfold l2SG
    have h0 : (fun x => (‖phiOf hB u τ (Matrix.of x)‖₊ : ENNReal) ^ 2) =ᵐ[C.nuS u τ] 0 := by
      filter_upwards [hae] with x hx
      simp [hcon _ hx]
    rw [lintegral_congr_ae h0]
    simp
  obtain ⟨m, hm, hΦ⟩ := hex
  have hds := Formalism.L2.SG.Pf.dsTr C τ
  have hlam := Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ
  have hv0 : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds (Formalism.L2.SG.Pf.isLowUnitH_base_vector C τ)
  have hv : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hds) hv0 hm
  have hBs := (hB u τ).choose_spec.1
  obtain ⟨hadd, -, -, Cw, Ws, hWs, hbd⟩ := hBs
  have hBv : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) ≠ 0 := hΦ
  have hnB : 0 < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ := norm_pos_iff.mpr hBv
  set δ : ℝ := ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ / (|Cw| + 1) with hδ
  have hδ0 : 0 < δ := div_pos hnB (by positivity)
  obtain ⟨a, ha, hS⟩ := hD D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ (sigB X (C.Q τ) (C.Qi τ) τ) hlam hds _ hv Ws hWs δ hδ0
  refine ⟨a, ha, fun hBa => ?_⟩
  have has : a ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ _ hds a ha
  have hva : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.MainNotions.LowestKTypeMultiplicity.smooth_sub hv has
  have hsplit : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a) + bOf hB u τ a := by
    have := hadd _ hva a has
    rw [sub_add_cancel] at this
    exact this
  rw [hBa, add_zero] at hsplit
  have hb : ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖ ≤
      Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum := hbd _ hva
  rw [← hsplit] at hb
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
  have h1 : Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum ≤
      |Cw| * δ := by
    calc _ ≤ |Cw| * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w
            (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum := mul_le_mul_of_nonneg_right (le_abs_self Cw) hS0
      _ ≤ |Cw| * δ := mul_le_mul_of_nonneg_left hS.le (abs_nonneg Cw)
  have h2 : |Cw| * δ < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ := by
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg Cw]
  linarith

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
The claim follows from `carrierP_of_kFinite hT hJ (kFinNZ_of hD)`.
-/
theorem carrierP_of_dense (hT : CSTarget) (hJ : PI.BesselMapUniq.BesselMapUniq) (hD : KFinDense) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP :=
  carrierP_of_kFinite hT hJ (kFinNZ_of hD)

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
The claim follows from `carrierP_of_kfin4 hT hJ (kFinNZ_of hD)`.
-/
theorem carrierP_of_dense4 (hT : CSTarget4) (hJ : PI.BesselMapUniq.BesselMapUniq) (hD : KFinDense) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP :=
  carrierP_of_kfin4 hT hJ (kFinNZ_of hD)

end Formalism.L2.SG.Pf.CarrierXAll
