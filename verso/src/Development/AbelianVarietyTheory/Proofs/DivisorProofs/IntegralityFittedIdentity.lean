import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittedTiesBoundEventualStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

/- English proof (translation)
Take `⟨CF0, h⟩` from `h`. Use `⟨max CF0 1, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x0, h⟩` from `h ε CF (le_of_max_le_left hCF)`. Conclude with `⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G => ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩`.
-/
theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

/- English proof (translation)
Take `⟨a, h⟩` from `h`. Take `⟨a', h'⟩` from `h'`. Use `⟨max a a', fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x0, h⟩` from `h ε CF (le_of_max_le_left hCF)`. Take `⟨C1, x1, h'⟩` from `h' ε CF (le_of_max_le_right hCF)`.

Conclude with `⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G => ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G, h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩`.
-/
theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩`.
-/
theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie

open GlobalTheory.BigTop.Fun.IntTie in

/- English proof (translation)
Establish `hQ` using `GlobalTheory.T.fitted_ties_bound_eventual _ hS hd (gBig_dep (gBig_and hB hN))`. Use `Lf.mono hQ ?_` and prove the remaining obligations. Introduce `D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd`. Use `⟨hd, fun hq => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩` from `hq`.

Express the relevant statement in the definitionally equal form `1 ≤ CF at h1`. Express the relevant statement in the definitionally equal form `CF ≤ C at h2`. Take `⟨a, ha⟩` from `hd.2`. Establish `hsq` using `ha.sq`. Take `⟨S, del, -, -, hNI, hdl⟩` from `hsq.int`.

Take `⟨δ, t0, hP⟩` from `hsq.norms`. Use `choose P P' hb hz hz' using hP`. Establish `hI` using `hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA' (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij)) (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij)) (fun ij => ⟨hz ij, hz' ij⟩)`. Rewrite `hI` using `[← hdl]`. Use `show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)`.

Use `integralNormBound_mono hI ?_` and prove the remaining obligations. Use `clear hQ hne hsmall hb hz hz' hNI`. Establish `eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ)`. Use `D.R.m_add_three_le_k` as an intermediate fact. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Use `norm_cast`. Use `show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)`. Unfold `GlobalTheory.ChiGrid.sLen`. Rewrite using `[hr]`. Use `congr 3`.

Use linear arithmetic over natural numbers and integers. Establish `eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ)` using `hsq.weight`. Establish `eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl)`. Rewrite using `[GlobalTheory.FunObj.SqNum.log_levQ]`. Both sides reduce to the same expression.

Establish `ef : (d.O.f : ℝ) = D.R.f` using `rfl`. Take `⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) + D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b + D.R.f * (2 * (GlobalTheory.Ch …` from `⟨_, rfl⟩`. Establish `e1 : d.O.bDel C p.Z.b = C * X`. Unfold `FunData.bDel`. Rewrite using `[eN, eB, eS, ef, hX]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b) (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X`. Unfold `GlobalTheory.NormSum.intBound`. Rewrite using `[hX]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0` using `hI.2.1 ∅`. Rewrite `h0` using `[Finset.sum_empty]`. Express the relevant statement in the definitionally equal form `0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b) (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0`. Express the relevant statement in the definitionally equal form `GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b) (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _`. Rewrite using `[e1, e2]`.

Rewrite `h0` using `[e2]`. Establish `hX0 : 0 ≤ X` using `(mul_nonneg_iff_of_pos_left (by linarith)).1 h0`. Conclude with `mul_le_mul_of_nonneg_right h2 hX0`.
-/
theorem GlobalTheory.BigTop.Fun.int_tie (hS : SetAt)
    (hd : Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hB : BotSmall) (hN : BotNe) : GlobalTheory.BigTop.Fun.Int @Comparison₂ := by
  have hQ := GlobalTheory.T.fitted_ties_bound_eventual _ hS hd (gBig_dep (gBig_and hB hN))
  refine Lf.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩ := hq
  change 1 ≤ CF at h1
  change CF ≤ C at h2
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  obtain ⟨S, del, -, -, hNI, hdl⟩ := hsq.int
  obtain ⟨δ, t0, hP⟩ := hsq.norms
  choose P P' hb hz hz' using hP
  have hI := hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA'
    (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij))
    (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij))
    (fun ij => ⟨hz ij, hz' ij⟩)
  rw [← hdl] at hI
  show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)
  refine integralNormBound_mono hI ?_
  clear hQ hne hsmall hb hz hz' hNI
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) ^ 2 * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := ⟨_, rfl⟩
  have e1 : d.O.bDel C p.Z.b = C * X := by
    unfold FunData.bDel
    rw [eN, eB, eS, ef, hX]
    ring
  have e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X := by
    unfold GlobalTheory.NormSum.intBound
    rw [hX]
    ring
  have h0 := hI.2.1 ∅
  rw [Finset.sum_empty] at h0
  change 0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0
  change GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _
  rw [e1, e2]
  rw [e2] at h0
  have hX0 : 0 ≤ X := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
  exact mul_le_mul_of_nonneg_right h2 hX0
