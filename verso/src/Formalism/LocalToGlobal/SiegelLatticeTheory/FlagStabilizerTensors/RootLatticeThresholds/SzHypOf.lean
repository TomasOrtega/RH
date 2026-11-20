import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyExponentOfFormalDegree
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypOf

variable (D : D7) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)

/- English proof (translation)
Unfold `Sz.Glob.place Formalism.L2.SG.SpectralTiesReal.gOf Formalism.MainNotions.BridgeLemma.cfgOf`. Use `congr 1`. Conclude with `(Formalism.MainNotions.BridgeLemma.m_eq D).symm`.
-/
theorem gOf_place (w : InfinitePlace D.host.E) :
    (Formalism.L2.SG.SpectralTiesReal.gOf D e).place w = Formalism.MainNotions.BridgeLemma.cfgOf D (e w) := by
  unfold Sz.Glob.place Formalism.L2.SG.SpectralTiesReal.gOf Formalism.MainNotions.BridgeLemma.cfgOf
  congr 1
  exact (Formalism.MainNotions.BridgeLemma.m_eq D).symm

include e in

/- English proof (translation)
Rewrite using `[Fintype.card_congr e]`. Conclude with `Formalism.MainNotions.BridgeLemma.szf_card_Tau D`.
-/
theorem card_places : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [Fintype.card_congr e]; exact Formalism.MainNotions.BridgeLemma.szf_card_Tau D

/- English proof (translation)
The claim follows from `card_places D e`.
-/
theorem gOf_f : (Formalism.L2.SG.SpectralTiesReal.gOf D e).f = D.R.f := card_places D e

/- English proof (translation)
Use function extensionality and compare the values at `l`. Establish `hk` using `Formalism.MainNotions.BridgeLemma.five_le_k D`. Unfold `Formalism.L2.SG.SpectralTiesReal.deOf`. Distinguish the cases in `hl : 1 ≤ l ∧ l + 2 ≤ D.R.k`. Rewrite using `[if_pos hl]`.

Establish `hu` using `Formalism.MainNotions.BridgeLemma.cfg_u D u τ (h5 u τ) (l + 1) (by omega) (by omega)`. Establish `hv` using `Formalism.MainNotions.BridgeLemma.cfg_v D τ l hl.1 (by omega)`. Establish `hne1 : l + 1 ≠ 1` using `by omega`. Establish `hnek : l + 1 ≠ (Formalism.MainNotions.BridgeLemma.cfgOf D τ).k` using `by show l + 1 ≠ D.R.k; omega`. Unfold `Sz.Cfg.u at hu`.

Rewrite `hu` using `[if_neg hne1, if_neg hnek, Nat.add_sub_cancel, hv]`. Establish `hD : (Formalism.MainNotions.BridgeLemma.cfgOf D τ).Del = (D.s.Del : ℝ)` using `rfl`. Rewrite `hu` using `[hD]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg hl]`. Unfold `Formalism.MainNotions.BridgeLemma.deOf`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem deOf_eq (h5 : ∀ (u : D.what₂.Word) τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hDel : (D.s.Del : ℝ) ≠ 0) (τ : D.what₂.Tau) (u : D.what₂.Word) :
    Formalism.L2.SG.SpectralTiesReal.deOf D τ u = Formalism.MainNotions.BridgeLemma.deOf D u := by
  funext l
  have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
  unfold Formalism.L2.SG.SpectralTiesReal.deOf
  by_cases hl : 1 ≤ l ∧ l + 2 ≤ D.R.k
  · rw [if_pos hl]
    have hu := Formalism.MainNotions.BridgeLemma.cfg_u D u τ (h5 u τ) (l + 1) (by omega) (by omega)
    have hv := Formalism.MainNotions.BridgeLemma.cfg_v D τ l hl.1 (by omega)
    have hne1 : l + 1 ≠ 1 := by omega
    have hnek : l + 1 ≠ (Formalism.MainNotions.BridgeLemma.cfgOf D τ).k := by show l + 1 ≠ D.R.k; omega
    unfold Sz.Cfg.u at hu
    rw [if_neg hne1, if_neg hnek, Nat.add_sub_cancel, hv] at hu
    have hD : (Formalism.MainNotions.BridgeLemma.cfgOf D τ).Del = (D.s.Del : ℝ) := rfl
    rw [hD] at hu
    field_simp
    linarith
  · rw [if_neg hl]
    unfold Formalism.MainNotions.BridgeLemma.deOf
    rw [dif_neg (by omega)]

variable {D e}

/- English proof (translation)
Establish `hHc` using `hH`. Take `⟨-, -, a3, a4, -, -, -, -, -, -, -, a12, -, a14, -, a16, -, -, a19, a20, -, -, -, -, -⟩` from `hHc`. Establish `hk5` using `Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (show 1 ≤ D.R.k by omega)`. Establish `hf1` using `Formalism.MainNotions.BridgeLemma.one_le_f D`.

Establish `hL1` using `Formalism.MainNotions.BridgeLemma.one_le_L large₂`. Establish `hm` using `Formalism.MainNotions.BridgeLemma.m_eq D`. Use `⟨fun w => ?_, fun w => ?_, Formalism.MainNotions.BridgeLemma.one_lt_b large₂, ?_, ?_, a19, ?_, a12, a14, ?_, ?_, Formalism.MainNotions.BridgeLemma.szaMass_pos D _⟩` and prove the remaining obligations. Rewrite using `[gOf_place]`. Conclude with `Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)`.

Rewrite using `[gOf_place]`. Conclude with `Formalism.MainNotions.BridgeLemma.cfg_small hH h40 (e w)`. Use `show 2 * D.R.rS + 2 ≤ Fintype.card _`. Rewrite using `[card_places D e, ← hm]`. Establish `h2` using `D.R.two_le_m`.

Combine the equalities or inequalities in the displayed calculation. Use `show Fintype.card _ ≤ D.R.k`. Rewrite using `[card_places D e]`. Conclude with `a4`. Use `show (2 * D.host.v) ^ D.R.f = (2 * D.host.v) ^ Fintype.card _`.

Rewrite using `[card_places D e]`. Introduce `w j hj1 hjm`. Establish `hjm' : j ≤ D.R.m` using `by rw [hm]; exact hjm`. Establish `h` using `(a16 (e w) j hj1 hjm').1`. Use `show (D.R.k : ℝ) ^ (3 : ℝ) ≤ bOne D (e w) j`.

Combine the equalities or inequalities in the displayed calculation. Use `show ((D.R.k : ℝ) * (Fintype.card (InfinitePlace D.host.E) : ℝ) * Real.log large₂.sc.b) ^ (5 : ℝ) ≤ D.s.Del`. Rewrite using `[card_places D e, Formalism.MainNotions.BridgeLemma.log_b]`. Establish `hx : (1 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L`. Use `mul_le_mul hk1 hf1 zero_le_one (by linarith)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gOf_hyp {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h40 : 40 ≤ Cl) : (Formalism.L2.SG.SpectralTiesReal.gOf D e).Hyp large₂.sc.b 5 3 := by
  have hHc := hH
  obtain ⟨-, -, a3, a4, -, -, -, -, -, -, -, a12, -, a14, -, a16, -, -, a19, a20, -, -, -, -, -⟩ := hHc
  have hk5 := Formalism.MainNotions.BridgeLemma.five_le_k D
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hf1 := Formalism.MainNotions.BridgeLemma.one_le_f D
  have hL1 := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hm := Formalism.MainNotions.BridgeLemma.m_eq D
  refine ⟨fun w => ?_, fun w => ?_, Formalism.MainNotions.BridgeLemma.one_lt_b large₂, ?_, ?_, a19, ?_, a12, a14, ?_, ?_,
    Formalism.MainNotions.BridgeLemma.szaMass_pos D _⟩
  · rw [gOf_place]; exact Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)
  · rw [gOf_place]; exact Formalism.MainNotions.BridgeLemma.cfg_small hH h40 (e w)
  · show 2 * D.R.rS + 2 ≤ Fintype.card _
    rw [card_places D e, ← hm]
    have h2 := D.R.two_le_m
    calc D.R.m ≤ D.R.m ^ 4 := Nat.le_self_pow (by norm_num) _
      _ ≤ D.R.f := a3
  · show Fintype.card _ ≤ D.R.k
    rw [card_places D e]; exact a4
  · show (2 * D.host.v) ^ D.R.f = (2 * D.host.v) ^ Fintype.card _
    rw [card_places D e]
  · intro w j hj1 hjm
    have hjm' : j ≤ D.R.m := by rw [hm]; exact hjm
    have h := (a16 (e w) j hj1 hjm').1
    show (D.R.k : ℝ) ^ (3 : ℝ) ≤ bOne D (e w) j
    calc (D.R.k : ℝ) ^ (3 : ℝ) ≤ (D.R.k : ℝ) ^ Cl := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ ≤ _ := le_trans (le_max_left _ _) h
  · show ((D.R.k : ℝ) * (Fintype.card (InfinitePlace D.host.E) : ℝ) * Real.log large₂.sc.b) ^ (5 : ℝ) ≤ D.s.Del
    rw [card_places D e, Formalism.MainNotions.BridgeLemma.log_b]
    have hx : (1 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by
      have := mul_le_mul hk1 hf1 zero_le_one (by linarith)
      nlinarith
    calc ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ (5 : ℝ) ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ _ := a20

/- English proof (translation)
Establish `hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f` using `card_places D e`. Establish `hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f` using `Formalism.MainNotions.BridgeLemma.szaData_f D u`. Unfold `Sz.SizeData.MassRatios at h ⊢`. Rewrite using `[hf1]`. Rewrite `h` using `[hf2]`.

Conclude with `h`.
-/
theorem massRatios_of (de : ℕ → ℝ) (T : ℕ) (du : ℝ) (u : D.what₂.Word)
    (h : (Formalism.MainNotions.BridgeLemma.szaData D u).MassRatios) : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).MassRatios := by
  have hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f := card_places D e
  have hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f := Formalism.MainNotions.BridgeLemma.szaData_f D u
  unfold Sz.SizeData.MassRatios at h ⊢
  rw [hf1]
  rw [hf2] at h
  exact h

/- English proof (translation)
Establish `h` using `Formalism.MainNotions.BridgeLemma.szaData_LBound D u`. Establish `hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f` using `card_places D e`. Establish `hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f` using `Formalism.MainNotions.BridgeLemma.szaData_f D u`. Unfold `Sz.SizeData.LBound at h ⊢`. Rewrite using `[hf1]`.

Rewrite `h` using `[hf2]`. Conclude with `h`.
-/
theorem lBound_of (de : ℕ → ℝ) (T : ℕ) (du : ℝ) (u : D.what₂.Word) :
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).LBound := by
  have h := Formalism.MainNotions.BridgeLemma.szaData_LBound D u
  have hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f := card_places D e
  have hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f := Formalism.MainNotions.BridgeLemma.szaData_f D u
  unfold Sz.SizeData.LBound at h ⊢
  rw [hf1]
  rw [hf2] at h
  exact h

/- English proof (translation)
Rewrite using `[← Equiv.prod_comp e]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Unfold `Sz.SizeData.dimPi`. Use `congr 1`. Use `show Sz.Vand D.R.k (((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).u (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u)) = vand (uS D u (e w))`.

Rewrite using `[deOf_eq D h5 hDel τ0 u, gOf_place, Formalism.MainNotions.BridgeLemma.Vand_u D u (e w) (h5 u (e w))]`.
-/
theorem prod_dimPi (h5 : ∀ (u : D.what₂.Word) τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hDel : (D.s.Del : ℝ) ≠ 0) (τ0 : D.what₂.Tau) (u : D.what₂.Word) (T : ℕ) (du : ℝ) :
    ∏ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u) T du).dimPi w =
      ∏ τ, (Formalism.MainNotions.BridgeLemma.szaData D u).dimPi τ := by
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold Sz.SizeData.dimPi
  congr 1
  show Sz.Vand D.R.k (((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).u (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u)) = vand (uS D u (e w))
  rw [deOf_eq D h5 hDel τ0 u, gOf_place, Formalism.MainNotions.BridgeLemma.Vand_u D u (e w) (h5 u (e w))]

/- English proof (translation)
Establish `hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u) (D.mem u).A.T (D.duS u)).f = D.R.f` using `card_places D e`. Establish `hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f` using `Formalism.MainNotions.BridgeLemma.szaData_f D u`. Establish `hp` using `prod_dimPi (e := e) h5 hDel τ0 u (D.mem u).A.T (D.duS u)`. Unfold `Sz.SizeData.ColumnCount Sz.SizeData.idxCol at h ⊢`. Rewrite using `[hp, hf1]`.

Rewrite `h` using `[hf2]`. Conclude with `h`.
-/
theorem columnCount_of (h5 : ∀ (u : D.what₂.Word) τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hDel : (D.s.Del : ℝ) ≠ 0) (τ0 : D.what₂.Tau) (u : D.what₂.Word)
    (h : (Formalism.MainNotions.BridgeLemma.szaData D u).ColumnCount) :
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u) (D.mem u).A.T (D.duS u)).ColumnCount := by
  have hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size (Formalism.L2.SG.SpectralTiesReal.deOf D τ0 u) (D.mem u).A.T (D.duS u)).f = D.R.f :=
    card_places D e
  have hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f := Formalism.MainNotions.BridgeLemma.szaData_f D u
  have hp := prod_dimPi (e := e) h5 hDel τ0 u (D.mem u).A.T (D.duS u)
  unfold Sz.SizeData.ColumnCount Sz.SizeData.idxCol at h ⊢
  rw [hp, hf1]
  rw [hf2] at h
  exact h

/- English proof (translation)
Establish `hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f` using `card_places D e`. Establish `hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f` using `Formalism.MainNotions.BridgeLemma.szaData_f D u`. Establish `hd : ∏ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).dsig w = ∏ τ, (Formalism.MainNotions.BridgeLemma.szaData D u).dsig τ`. Rewrite using `[← Equiv.prod_comp e]`. Both sides reduce to the same expression.

Unfold `Sz.SizeData.Dstar Sz.SizeData.idxRow`. Rewrite using `[hd, hf1, hf2]`. Both sides reduce to the same expression.
-/
theorem dstar_eq (de : ℕ → ℝ) (T : ℕ) (du : ℝ) (u : D.what₂.Word) :
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).Dstar = (Formalism.MainNotions.BridgeLemma.szaData D u).Dstar := by
  have hf1 : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).f = D.R.f := card_places D e
  have hf2 : (Formalism.MainNotions.BridgeLemma.szaData D u).f = D.R.f := Formalism.MainNotions.BridgeLemma.szaData_f D u
  have hd : ∏ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de T du).dsig w = ∏ τ, (Formalism.MainNotions.BridgeLemma.szaData D u).dsig τ := by
    rw [← Equiv.prod_comp e]; rfl
  unfold Sz.SizeData.Dstar Sz.SizeData.idxRow
  rw [hd, hf1, hf2]
  rfl

/- English proof (translation)
Establish `hk` using `Formalism.MainNotions.BridgeLemma.five_le_k D`. Take `⟨a, ha⟩` from `Function.ne_iff.1 (hne u u' huu τ)`. Establish `ha' : uOne D u τ (a.1 + 1) ≠ uOne D u' τ (a.1 + 1)`. Rewrite using `[Formalism.MainNotions.BridgeLemma.uOne_succ D u τ a.1 a.2, Formalism.MainNotions.BridgeLemma.uOne_succ D u' τ a.1 a.2]`. Conclude with `ha`.

Establish `h0 : a.1 ≠ 0`. Introduce `h`. Apply `ha'` to reduce the goal to its premises. Rewrite using `[h, Formalism.MainNotions.BridgeLemma.uOne_one D u τ, Formalism.MainNotions.BridgeLemma.uOne_one D u' τ]`. Establish `hl : a.1 + 1 ≠ D.R.k`.

Introduce `h`. Apply `ha'` to reduce the goal to its premises. Rewrite using `[h, Formalism.MainNotions.BridgeLemma.uOne_last D u τ, Formalism.MainNotions.BridgeLemma.uOne_last D u' τ]`. Establish `hak` using `a.2`. Conclude with `⟨a.1, by omega, by omega, Formalism.MainNotions.BridgeLemma.deOf_ne D u u' τ (fun w => h5 w τ) a.1 (by omega) (by omega) ha'⟩`.
-/
theorem exists_continuousLinearMap_tens_update (h5 : ∀ (u : D.what₂.Word) τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hne : ∀ u u' : D.what₂.Word, u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) {u u' : D.what₂.Word} (huu : u ≠ u')
    (τ : D.what₂.Tau) : ∃ l, 1 ≤ l ∧ l + 2 ≤ D.R.k ∧ Formalism.MainNotions.BridgeLemma.deOf D u l ≠ Formalism.MainNotions.BridgeLemma.deOf D u' l := by
  have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
  obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne u u' huu τ)
  have ha' : uOne D u τ (a.1 + 1) ≠ uOne D u' τ (a.1 + 1) := by
    rw [Formalism.MainNotions.BridgeLemma.uOne_succ D u τ a.1 a.2, Formalism.MainNotions.BridgeLemma.uOne_succ D u' τ a.1 a.2]
    exact ha
  have h0 : a.1 ≠ 0 := by
    intro h
    apply ha'
    rw [h, Formalism.MainNotions.BridgeLemma.uOne_one D u τ, Formalism.MainNotions.BridgeLemma.uOne_one D u' τ]
  have hl : a.1 + 1 ≠ D.R.k := by
    intro h
    apply ha'
    rw [h, Formalism.MainNotions.BridgeLemma.uOne_last D u τ, Formalism.MainNotions.BridgeLemma.uOne_last D u' τ]
  have hak := a.2
  exact ⟨a.1, by omega, by omega,
    Formalism.MainNotions.BridgeLemma.deOf_ne D u u' τ (fun w => h5 w τ) a.1 (by omega) (by omega) ha'⟩

def SzRowsAt (D : D7) : Prop :=
  LocalBesselAndTopKernel.FamilySchurFormalDegree D ∧ LocalBesselAndTopKernel.FamilyMidVolume D ∧ Formalism.MainNotions.BridgeLemma.SzaSpl D ∧
    ∀ τ, Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ)

def ThresholdAtPlaces (CA : ℝ) (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∃ Th : ℝ, 0 < Th ∧ IsGreatest ((Formalism.L2.SG.SpectralTiesReal.gOf D (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm).thrSet CA
    (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') (D.mem u).A.T (D.mem u').A.T
    (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')))
    ((Th ^ (Formalism.L2.SG.SpectralTiesReal.gOf D (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm).f)⁻¹)

/- English proof (translation)
Establish `hk5` using `Formalism.MainNotions.BridgeLemma.five_le_k D`. Establish `hDc` using `hD`. Take `⟨-, -, -, -, d5, -, -, d8, d9, d10, -⟩` from `hDc`. Establish `hHc` using `hH`. Take `⟨a1, a2, a3, -, -, a6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a23, -, -⟩` from `hHc`.

Establish `hL1` using `Formalism.MainNotions.BridgeLemma.one_le_L large₂`. Establish `hm` using `Formalism.MainNotions.BridgeLemma.m_eq D`. Establish `hfpos : 0 < D.R.f`. Establish `h2` using `D.R.two_le_m`. Establish `: 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (by omega)`.

Use linear arithmetic over natural numbers and integers. Use `haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.BridgeLemma.szf_card_Tau]; exact hfpos)`. Take `⟨τ0⟩` from `(inferInstance : Nonempty D.what₂.Tau)`. Establish `hDel : (D.s.Del : ℝ) ≠ 0`. Use `(Formalism.MainNotions.BridgeLemma.cfg_ok hD hH τ0).hDel` as an intermediate fact.

Conclude with `ne_of_gt (lt_of_lt_of_le one_pos this)`. Use `set e := (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm with he`. Establish `hdu` using `deOf_eq D d5 hDel τ0 u`. Establish `hdu'` using `deOf_eq D d5 hDel τ0 u'`. Establish `hfR : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) = (D.R.f : ℝ)` using `by exact_mod_cast card_places D e`.

Establish `hmR : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) = (D.R.m : ℝ)` using `by show ((2 * D.R.rS + 2 : ℕ) : ℝ) = _`. Rewrite using `[hm]`. Establish `hlogb` using `Formalism.MainNotions.BridgeLemma.log_b large₂`. Establish `cc` using `columnCount_of (e := e) d5 hDel τ0 u (Formalism.MainNotions.BridgeLemma.szaData_ColumnCount D u hR.2.1 hR.2.2.1)`. Establish `cc'` using `columnCount_of (e := e) d5 hDel τ0 u' (Formalism.MainNotions.BridgeLemma.szaData_ColumnCount D u' hR.2.1 hR.2.2.1)`.

Rewrite `cc` using `[hdu]`. Rewrite `cc'` using `[hdu']`. Establish `hDs : ∀ (w : D.what₂.Word) (de : ℕ → ℝ) (Tw : ℕ) (dw : ℝ), ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de Tw dw).Dstar = D.what₂.Dstar` using `fun w de Tw dw => (dstar_eq de Tw dw w).trans (Formalism.MainNotions.BridgeLemma.szaData_Dstar D w hR.2.1 hR.2.2.1)`. Establish `hΓ : ∀ w : D.what₂.Word, Real.exp (large₂.CGam * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) ^ 5 * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) * Real.log large₂.sc.b) = (D.mem w).A.GamP`. Introduce `w`.

Rewrite using `[hmR, hfR, hlogb, ← Formalism.MainNotions.S.gamOf_eq large₂ w]`. Both sides reduce to the same expression. Establish `hcho : ∀ (w : D.what₂.Word) (de : ℕ → ℝ), ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de (D.mem w).A.T (D.duS w)).ChoiceOfT C0 (Real.exp (large₂.CGam * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) ^ 5 * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) * Real.log larg …`. Introduce `w de`. Unfold `Sz.SizeData.ChoiceOfT`.

Rewrite using `[hΓ w, hDs w de]`. Take `⟨l1, l2⟩` from `d10 w`. Rewrite `l1` using `[zpow_neg, zpow_ofNat, div_eq_mul_inv]`. Rewrite `l2` using `[zpow_neg, zpow_ofNat]`. Conclude with `⟨l1, l2⟩`.

Establish `hfdl : ∀ (w : InfinitePlace D.host.E) (de : ℕ → ℝ) (Tw : ℕ) (dw : ℝ), Sz.FormalDegreeLower ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w) (1 / 2) (((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de Tw dw).VV w)`. Introduce `w de Tw dw`. Rewrite using `[gOf_place]`. Establish `hn : D.R.k + (2 * D.R.rS + 2) - 1 = D.R.r` using `by rw [Formalism.MainNotions.BridgeLemma.sza_r_eq]; omega`. Establish `h` using `hR.2.2.2 (e w)`.

Unfold `VV at h`. Unfold `Sz.SizeData.VV Sz.SizeData.n Sz.SizeData.m`. Use `show _ ≤ D.dsig (e w) * ((Sz.sfac (D.R.k + (2 * D.R.rS + 2) - 1) : ℕ) : ℝ)`. Rewrite using `[hn, Sz.sfac, Nat.cast_prod]`. Conclude with `h`.

Establish `hex` using `exists_continuousLinearMap_tens_update d5 d8 huu τ0`. Establish `hlOf : Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') = Nat.find hex`. Unfold `Formalism.L2.SG.SpectralTiesReal.lOf`. Conclude with `dif_pos hex`. Establish `hsl` using `Nat.find_spec hex`.

Take `⟨Th, hTh, hG⟩` from `hThr`. Use `⟨e, τ0, C', Th, 256, fun x => Formalism.L2.SG.Pf.CarrierTop.placeTie_ePl T.X x, hk0, ?_, ?_, ?_, ?_, ?_, hDs u _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hdu, hdu']`. Use `⟨gOf_hyp hD hH (by linarith), Formalism.MainNotions.BridgeLemma.isWord_deOf D u, Formalism.MainNotions.BridgeLemma.isWord_deOf D u', ?_, ?_, ?_, ?_, ?_, a1, ?_, massRatios_of _ _ _ u (Formalism.MainNotions.BridgeLemma.szaData_MassRatios D u hR.1), lBound_of _ _ _ u, cc, cc', hcho …` and prove the remaining obligations. Rewrite using `[hlOf]`.

Conclude with `hsl.1`. Rewrite using `[hlOf]`. Conclude with `hsl.2.1`. Rewrite using `[hlOf]`. Conclude with `hsl.2.2`.

Rewrite using `[hmR]`. Conclude with `(a23 u).1`. Rewrite using `[hmR]`. Conclude with `(a23 u').1`. Rewrite using `[hmR, hfR, hlogb]`.

Conclude with `a2`. Unfold `Sz.cExp`. Evaluate the numerical expressions. Use `show (256 : ℝ) * Real.log large₂.sc.b ≤ ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) * Real.log (D.R.k : ℝ)`. Rewrite using `[hfR, hlogb]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hkR : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k` using `a2`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hmf : (D.R.m : ℝ) ≤ D.R.f`. Establish `h` using `D.R.two_le_m`.

Establish `: D.R.m ≤ D.R.f` using `le_trans (Nat.le_self_pow (by norm_num) _) a3`. Conclude with `this` after adjusting the coercions. Establish `hf1` using `Formalism.MainNotions.BridgeLemma.one_le_f D`. Establish `hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : (7 : ℝ) * D.R.f ≤ D.R.k`. Establish `: (70 * 32 : ℝ) * D.R.f * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : ((2 * D.R.rS + 2 + D.R.f + 5 : ℕ) : ℝ) ≤ D.R.k`. Use `push_cast`.

Establish `: (2 * (D.R.rS : ℝ) + 2) = D.R.m` using `by exact_mod_cast hm.symm`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h2` after adjusting the coercions. Establish `hSN` using `Formalism.L2.SG.ThmSOwn.size_numbers_of_hypotheses hH (by linarith) h70 hCn show Formalism.FourierDecayAlt.PB.SizeNumbers D.R.k D.R.rS (Fintype.card _) large₂.sc.b (D.host.g 0) (D.host.g 1) (1 / 3) Cn`. Rewrite using `[card_places D e]`.

Conclude with `hSN`. Establish `e1 : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (D.host.g 0 * D.host.g 1) ^ 2]` using `((d9 u).2 : _ ≡ 1 [MOD _]).trans ((d9 u').2 : _ ≡ 1 [MOD _]).symm`. Conclude with `e1`.
-/
theorem sizesAt_of {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu CT CA Cn : ℝ} {k0 : ℕ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu (1 / 2) CT) (h256 : 256 ≤ Cl) (h70 : 70 ≤ C') (hCn : 8 * Cn ≤ C')
    (hk0 : k0 ≤ D.R.k) (hR : SzRowsAt D) (T : Formalism.L2.SG.SpectralTiesReal.STies D) {u u' : D.what₂.Word} (huu : u ≠ u')
    (hThr : ThresholdAtPlaces CA D u u') :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 large₂.CGam 5 (1 / 2) 3 Cn k0 D large₂ T u u' := by
  have hk5 := Formalism.MainNotions.BridgeLemma.five_le_k D
  have hDc := hD
  obtain ⟨-, -, -, -, d5, -, -, d8, d9, d10, -⟩ := hDc
  have hHc := hH
  obtain ⟨a1, a2, a3, -, -, a6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a23, -, -⟩ := hHc
  have hL1 := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hm := Formalism.MainNotions.BridgeLemma.m_eq D
  have hfpos : 0 < D.R.f := by
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.BridgeLemma.szf_card_Tau]; exact hfpos)
  obtain ⟨τ0⟩ := (inferInstance : Nonempty D.what₂.Tau)
  have hDel : (D.s.Del : ℝ) ≠ 0 := by
    have := (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH τ0).hDel
    exact ne_of_gt (lt_of_lt_of_le one_pos this)
  set e := (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm with he
  have hdu := deOf_eq D d5 hDel τ0 u
  have hdu' := deOf_eq D d5 hDel τ0 u'
  have hfR : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) = (D.R.f : ℝ) := by exact_mod_cast card_places D e
  have hmR : ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) = (D.R.m : ℝ) := by
    show ((2 * D.R.rS + 2 : ℕ) : ℝ) = _
    rw [hm]
  have hlogb := Formalism.MainNotions.BridgeLemma.log_b large₂
  have cc := columnCount_of (e := e) d5 hDel τ0 u (Formalism.MainNotions.BridgeLemma.szaData_ColumnCount D u hR.2.1 hR.2.2.1)
  have cc' := columnCount_of (e := e) d5 hDel τ0 u' (Formalism.MainNotions.BridgeLemma.szaData_ColumnCount D u' hR.2.1 hR.2.2.1)
  rw [hdu] at cc
  rw [hdu'] at cc'
  have hDs : ∀ (w : D.what₂.Word) (de : ℕ → ℝ) (Tw : ℕ) (dw : ℝ),
      ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de Tw dw).Dstar = D.what₂.Dstar := fun w de Tw dw =>
    (dstar_eq de Tw dw w).trans (Formalism.MainNotions.BridgeLemma.szaData_Dstar D w hR.2.1 hR.2.2.1)
  have hΓ : ∀ w : D.what₂.Word, Real.exp (large₂.CGam * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) ^ 5 *
      ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) * Real.log large₂.sc.b) = (D.mem w).A.GamP := by
    intro w
    rw [hmR, hfR, hlogb, ← Formalism.MainNotions.S.gamOf_eq large₂ w]
    rfl
  have hcho : ∀ (w : D.what₂.Word) (de : ℕ → ℝ), ((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de (D.mem w).A.T (D.duS w)).ChoiceOfT C0
      (Real.exp (large₂.CGam * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).m : ℝ) ^ 5 * ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) *
        Real.log large₂.sc.b)) := by
    intro w de
    unfold Sz.SizeData.ChoiceOfT
    rw [hΓ w, hDs w de]
    obtain ⟨l1, l2⟩ := d10 w
    rw [zpow_neg, zpow_ofNat, div_eq_mul_inv] at l1
    rw [zpow_neg, zpow_ofNat] at l2
    exact ⟨l1, l2⟩
  have hfdl : ∀ (w : InfinitePlace D.host.E) (de : ℕ → ℝ) (Tw : ℕ) (dw : ℝ),
      Sz.FormalDegreeLower ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w) (1 / 2)
        (((Formalism.L2.SG.SpectralTiesReal.gOf D e).size de Tw dw).VV w) := by
    intro w de Tw dw
    rw [gOf_place]
    have hn : D.R.k + (2 * D.R.rS + 2) - 1 = D.R.r := by rw [Formalism.MainNotions.BridgeLemma.sza_r_eq]; omega
    have h := hR.2.2.2 (e w)
    unfold VV at h
    unfold Sz.SizeData.VV Sz.SizeData.n Sz.SizeData.m
    show _ ≤ D.dsig (e w) * ((Sz.sfac (D.R.k + (2 * D.R.rS + 2) - 1) : ℕ) : ℝ)
    rw [hn, Sz.sfac, Nat.cast_prod]
    exact h
  have hex := exists_continuousLinearMap_tens_update d5 d8 huu τ0
  have hlOf : Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') = Nat.find hex := by
    unfold Formalism.L2.SG.SpectralTiesReal.lOf
    exact dif_pos hex
  have hsl := Nat.find_spec hex
  obtain ⟨Th, hTh, hG⟩ := hThr
  refine ⟨e, τ0, C', Th, 256, fun x => Formalism.L2.SG.Pf.CarrierTop.placeTie_ePl T.X x, hk0, ?_, ?_, ?_, ?_, ?_, hDs u _ _ _, ?_⟩
  · rw [hdu, hdu']
    refine ⟨gOf_hyp hD hH (by linarith), Formalism.MainNotions.BridgeLemma.isWord_deOf D u, Formalism.MainNotions.BridgeLemma.isWord_deOf D u', ?_, ?_, ?_,
      ?_, ?_, a1, ?_, massRatios_of _ _ _ u (Formalism.MainNotions.BridgeLemma.szaData_MassRatios D u hR.1), lBound_of _ _ _ u, cc, cc',
      hcho u _, hcho u' _, fun w => hfdl w _ _ _, hTh, hG⟩
    · rw [hlOf]; exact hsl.1
    · rw [hlOf]; exact hsl.2.1
    · rw [hlOf]; exact hsl.2.2
    · rw [hmR]; exact (a23 u).1
    · rw [hmR]; exact (a23 u').1
    · rw [hmR, hfR, hlogb]; exact a2
  · unfold Sz.cExp; norm_num
  · show (256 : ℝ) * Real.log large₂.sc.b ≤ ((Formalism.L2.SG.SpectralTiesReal.gOf D e).f : ℝ) * Real.log (D.R.k : ℝ)
    rw [hfR, hlogb]
    nlinarith
  · have hkR : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := a2
    have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have hmf : (D.R.m : ℝ) ≤ D.R.f := by
      have h := D.R.two_le_m
      have : D.R.m ≤ D.R.f := le_trans (Nat.le_self_pow (by norm_num) _) a3
      exact_mod_cast this
    have hf1 := Formalism.MainNotions.BridgeLemma.one_le_f D
    have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hm2 5
    have h1 : (7 : ℝ) * D.R.f ≤ D.R.k := by
      have : (70 * 32 : ℝ) * D.R.f * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by gcongr
      nlinarith
    have h2 : ((2 * D.R.rS + 2 + D.R.f + 5 : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      have : (2 * (D.R.rS : ℝ) + 2) = D.R.m := by exact_mod_cast hm.symm
      nlinarith
    exact_mod_cast h2
  · have hSN := Formalism.L2.SG.ThmSOwn.size_numbers_of_hypotheses hH (by linarith) h70 hCn
    show Formalism.FourierDecayAlt.PB.SizeNumbers D.R.k D.R.rS (Fintype.card _) large₂.sc.b (D.host.g 0) (D.host.g 1) (1 / 3) Cn
    rw [card_places D e]
    exact hSN
  · have e1 : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (D.host.g 0 * D.host.g 1) ^ 2] :=
      ((d9 u).2 : _ ≡ 1 [MOD _]).trans ((d9 u').2 : _ ≡ 1 [MOD _]).symm
    exact e1

/- English proof (translation)
Unfold `Sz.FormalDegreeLower`. Rewrite using `[Formalism.MainNotions.BridgeLemma.Vand_lam D τ]`. Establish `h` using `(hg τ).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdl_of_cTvG {large₂ : SizeData₂ D} {CV : ℝ} (hg : Formalism.MainNotions.S.UnitaryVolumeMass.cTvG D large₂ (1 / 2) CV) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ]
  have h := (hg τ).1
  linarith

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD, hFD⟩`.
-/
theorem szRowsAt_of {C0 : ℝ} (hD : StandingNumericalData D C0) (hR : LocalBesselAndTopKernel.FamilyMidVolume D)
    (hFD : ∀ τ, Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ)) : SzRowsAt D :=
  ⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD, hFD⟩

section Row

open Formalism.L2.SG.ThmSOwn

variable (C0 : ℝ)

/- English proof (translation)
Introduce `CA hCA k0 cn`. Use `closed_with (hRw.and (hThr CA hCA)) (fun _ => 0) (fun l => max 256 (8 * cn l)) fun Fm CH _ hQ _ h1 h2 hc => ?_` and prove the remaining obligations. Take `⟨⟨xa, Ha⟩, ⟨xb, Hb⟩⟩` from `hQ`. Take `⟨xk, -, Hk⟩` from `Formalism.MainNotions.BridgeLemma.ev_k Fm (k0 (Fm.cOut ++ Fm.cMid CH) : ℝ)`. Use `⟨max (max xa xb) xk, fun x hx i hH hx1 h0 u u' huu => ?_⟩` and prove the remaining obligations.

Establish `hxa : xa ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb : xb ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxk : xk ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `h1' : max 256 (8 * cn (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm` using `h1`. Establish `h2' : max 256 (8 * cn (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm` using `h2`.

Establish `h256 : 256 ≤ sCl Fm` using `le_trans (le_max_left _ _) h2'`. Establish `h70 : 70 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1')`. Establish `hCn : 8 * cn (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm` using `le_trans (le_max_right _ _) h1'`. Establish `hk0 : k0 (Fm.cOut ++ Fm.cMid CH) ≤ (Fm.D x i).R.k` using `by exact_mod_cast Hk x hxk i`. Establish `h` using `sizesAt_of hH.1 hH.2.1 h256 h70 hCn hk0 (Ha x hxa i hH) ((sel Fm hc).2 x hx1 h0 i) huu (Hb x hxb i hH u u' huu)`.

Rewrite `h` using `[Fm.CGam_eq x i]`. Then use the resulting hypothesis.
-/
theorem sizesRowS_of {𝒞 : FamClass} (sel : SSel 𝒞)
    (hRw : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → SzRowsAt (Fm.D x i))
    (hThr : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → ThresholdAtPlaces CA (Fm.D x i) u u') :
    SizesRowS C0 𝒞 sel := by
  intro CA hCA k0 cn
  refine closed_with (hRw.and (hThr CA hCA)) (fun _ => 0) (fun l => max 256 (8 * cn l)) fun Fm CH _ hQ _ h1 h2 hc => ?_
  obtain ⟨⟨xa, Ha⟩, ⟨xb, Hb⟩⟩ := hQ
  obtain ⟨xk, -, Hk⟩ := Formalism.MainNotions.BridgeLemma.ev_k Fm (k0 (Fm.cOut ++ Fm.cMid CH) : ℝ)
  refine ⟨max (max xa xb) xk, fun x hx i hH hx1 h0 u u' huu => ?_⟩
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxk : xk ≤ x := le_trans (le_max_right _ _) hx
  have h1' : max 256 (8 * cn (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm := h1
  have h2' : max 256 (8 * cn (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := h2
  have h256 : 256 ≤ sCl Fm := le_trans (le_max_left _ _) h2'
  have h70 : 70 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1')
  have hCn : 8 * cn (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm := le_trans (le_max_right _ _) h1'
  have hk0 : k0 (Fm.cOut ++ Fm.cMid CH) ≤ (Fm.D x i).R.k := by exact_mod_cast Hk x hxk i
  have h := sizesAt_of hH.1 hH.2.1 h256 h70 hCn hk0 (Ha x hxa i hH) ((sel Fm hc).2 x hx1 h0 i) huu
    (Hb x hxb i hH u u' huu)
  rwa [Fm.CGam_eq x i] at h

end Row

end Formalism.L2.SG.Pf.SzHypOf
