import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlongFamilyOfMassRatio
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

/- English proof (translation)
Establish `hanti : StrictAnti (lamSH D.R (D.hc τ))` using `(GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1`. Establish `hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))` using `hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ`. Establish `hN : 2 * D.R.rS + D.R.k + 1 = D.R.r` using `dimS_eq D.R`. Establish `hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ)` using `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i`. Unfold `VV`.

Rewrite using `[hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

/- English proof (translation)
Introduce `_ hH _ Cg cb Cu cT CT C0`. Use `⟨40, fun eps Fm _ hCl _ => ?_⟩` and prove the remaining obligations. Unfold `VanishingOnXAndXPlusBranching.admF5 OwnEv`. Use `⟨Fm.x1 + 1, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x` using `by linarith`.

Take `⟨hxk, hb⟩` from `GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)`. Establish `hL1 : 1 ≤ (Fm.L x i).sc.L` using `by show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps`. Conclude with `Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le`. Establish `hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L` using `by nlinarith`. Introduce `h0`.

Conclude with `GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0`.
-/
theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
