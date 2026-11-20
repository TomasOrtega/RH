import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCountStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y)` using `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)`. Establish `a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y)` using `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)`. Establish `a3 : (2 : ℝ) ≤ Real.exp y`. Use `Real.add_one_le_exp y` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[e]`.

Establish `hp` using `Real.exp_pos (max C₁ C₂ * y)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_add_exp_le_exp_max_succ {C₁ C₂ y : ℝ} (hy : 1 ≤ y) :
    Real.exp (C₁ * y) + Real.exp (C₂ * y) ≤ Real.exp ((max C₁ C₂ + 1) * y) := by
  have hy0 : 0 ≤ y := by linarith
  have a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  have a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
  have a3 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (max C₁ C₂ * y)
  nlinarith

/- English proof (translation)
Introduce `hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT`. Take `⟨C₁, hC₁, t₁, H₁⟩` from `h1 Cg cb Cu cT CT hcb hcT`. Take `⟨C₂, _, t₂, H₂⟩` from `h2 Cg cb Cu cT CT hcb hcT`. Take `⟨tG, HG⟩` from `hG Cg cb Cu cT CT hcb hcT`. Take `⟨tC, HC⟩` from `hCo Cg cb Cu cT CT hcb hcT`.

Use `⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29, by linarith [le_max_left C₁ C₂], ?_⟩` and prove the remaining obligations. Introduce `C' Cl hC' hCl D L u hT hE hD`. Take `⟨⟨large₂, hL, h8, h1G⟩, hR⟩` from `hE`. Take `⟨hTies, hAdm, hHL, hNW, hTF⟩` from `hD`. Substitute `hL` using the available equality.

Establish `hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT` using `⟨h8, hHL.2⟩`. Establish `hD0 : StandingNumericalData D 3` using `GlobalTheory.T.columnDimension_window_three_of_columnCount D hNW hR`. Establish `hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3` using `⟨hS0, hD0, by norm_num⟩`. Take `⟨S, hF, hLT⟩` from `hT.trueD.sTies`. Establish `m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e → a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e`.

Introduce `a b c d e h`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp`. Take `⟨a1, a2, a3, a4, a5⟩` from `m1 hC'`. Take `⟨b1, b2, b3, b4, b5⟩` from `m1 hCl`. Take `⟨c⟩` from `GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0`.

Establish `hAC : (c.Y.tO u u).AbsConv` using `kExp_absConv_tied.2 D c.X c.Y u u c.tie`. Establish `g0` using `HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC`. Establish `gc` using `HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC`. Establish `o1` using `H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC`. Establish `o2` using `H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC`.

Simplify using `only [if_true, Bool.false_eq_true, if_false] at o1 o2`. Establish `hf : (1 : ℝ) ≤ D.R.f`. Establish `h4 : D.R.m ^ 4 ≤ D.R.f` using `hHL.2.2.1`. Establish `: 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)`. Conclude with `le_trans this h4` after adjusting the coercions.

Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hL1 : 1 < large₂.sc.L` using `hHL.1`. Establish `hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L`. Establish `: (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5` using `one_le_pow₀ hm`. Establish `h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f` using `one_le_mul_of_one_le_of_one_le this hf`.

Conclude with `one_le_mul_of_one_le_of_one_le h2' hL1.le`. Establish `hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L))`. Introduce `C`. Unfold `gamL`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1)`. Rewrite using `[hg, hg, hg]`. Conclude with `exp_add_exp_le_exp_max_succ hy`. Establish `key` using `GlobalTheory.T.diagonalTheorem_of_fourPointBounds D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂) (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2`.

Unfold `SDiagAt at key`. Use `show TwoTerm D u _ _`. Unfold `TwoTerm`. Rewrite using `[d0_eq]`. Establish `e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L)`.

Rewrite using `[hg]`. Both sides reduce to the same expression. Establish `e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2))`. Unfold `kfk`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D)`. Unfold `kfk`. Both sides reduce to the same expression. Rewrite `key` using `[e1, e2, e3]`.

Use `le_trans key (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diagonalRow_bound_from_windowWidthThree : Formalism.L2.SG.Pf.WuDecayOfGap → On {3} VanishingGramTermsBound → On {3} CollS → OneOn {3} true →
    OneOn {3} false →
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  intro hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₁, hC₁, t₁, H₁⟩ := h1 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₂, _, t₂, H₂⟩ := h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨tG, HG⟩ := hG Cg cb Cu cT CT hcb hcT
  obtain ⟨tC, HC⟩ := hCo Cg cb Cu cT CT hcb hcT
  refine ⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29,
    by linarith [le_max_left C₁ C₂], ?_⟩
  intro C' Cl hC' hCl D L u hT hE hD
  obtain ⟨⟨large₂, hL, h8, h1G⟩, hR⟩ := hE
  obtain ⟨hTies, hAdm, hHL, hNW, hTF⟩ := hD
  subst hL
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := ⟨h8, hHL.2⟩
  have hD0 : StandingNumericalData D 3 := GlobalTheory.T.columnDimension_window_three_of_columnCount D hNW hR
  have hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3 := ⟨hS0, hD0, by norm_num⟩
  obtain ⟨S, hF, hLT⟩ := hT.trueD.sTies
  have m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e →
      a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e := by
    intro a b c d e h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := m1 hC'
  obtain ⟨b1, b2, b3, b4, b5⟩ := m1 hCl
  obtain ⟨c⟩ := GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0
  have hAC : (c.Y.tO u u).AbsConv := kExp_absConv_tied.2 D c.X c.Y u u c.tie
  have g0 := HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have gc := HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have o1 := H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  have o2 := H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := hHL.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast le_trans this h4
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 < large₂.sc.L := hHL.1
  have hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm
    have h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := one_le_mul_of_one_le_of_one_le this hf
    exact one_le_mul_of_one_le_of_one_le h2' hL1.le
  have hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) := by
    intro C; unfold gamL; congr 1; ring
  have hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1) := by
    rw [hg, hg, hg]; exact exp_add_exp_le_exp_max_succ hy
  have key := GlobalTheory.T.diagonalTheorem_of_fourPointBounds D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂)
    (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2
  unfold SDiagAt at key
  show TwoTerm D u _ _
  unfold TwoTerm
  rw [d0_eq]
  have e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L) := by
    rw [hg]; rfl
  have e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2)) := by
    unfold kfk; congr 1; ring
  have e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D) := by
    unfold kfk; rfl
  rw [e1, e2, e3] at key
  refine le_trans key (le_of_eq ?_)
  ring

end GlobalTheory.Core.Rk
