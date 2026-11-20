import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

open GlobalTheory.ChainOnto

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

/- English proof (translation)
Unfold `cH`. Conclude with `ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)`.
-/
theorem cH_ne_zero (W : RealPack ex) : cH W ≠ 0 := by
  unfold cH
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

/- English proof (translation)
Unfold `cH`. Establish `hpos : 0 < Nat.card (lvP W).H` using `Nat.card_pos`. Conclude with `ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')`.
-/
theorem cH_ne_top (W : RealPack ex) : cH W ≠ ⊤ := by
  unfold cH
  have hpos : 0 < Nat.card (lvP W).H := Nat.card_pos
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')

/- English proof (translation)
The claim follows from `Finset.eq_empty_of_forall_notMem (GlobalTheory.MiTop.not_mem_Q_base (W := W))`.
-/
theorem Q_base_empty (W : RealPack ex) : (pk W).Q W.P.A3.A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem (GlobalTheory.MiTop.not_mem_Q_base (W := W))

/- English proof (translation)
Establish `lev` using `W.Q.charW.base.lev`. Establish `hM` using `(W.Q.charW.base.models.νX W.P.A3.A.μ0)`. Take `⟨c, hc⟩` from `lev.βX`. Use `⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (pk W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show D.sp.X'.sig τ = _`.

Rewrite using `[D.X'_posDef τ, D.sp.X'_rank]`. Simplify using `[sigYD, Ranks.rankY, Ranks.rankX']`. Rewrite `hN` using `[one_pow, Nat.cast_one]`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)`. Use `show Lev.datY _ _ _ _ _ _ ((pk W).Q W.P.A3.A.μ0) _ _ _ _ = _`.

Rewrite using `[Q_base_empty W]`. Both sides reduce to the same expression. Conclude with `@MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ (cH_ne_zero W) (cH_ne_top W)`. Conclude with `hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)`.
-/
theorem stageX_is (W : RealPack ex) (_ : PkHyp W) : (stageX W).Is (com W) D.R.m := by
  have lev := W.Q.charW.base.lev
  have hM := (W.Q.charW.base.models.νX W.P.A3.A.μ0)
  obtain ⟨c, hc⟩ := lev.βX
  refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (pk W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show D.sp.X'.sig τ = _
    rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
  · rw [one_pow, Nat.cast_one] at hN
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
  · show Lev.datY _ _ _ _ _ _ ((pk W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [Q_base_empty W]; rfl
  · exact @MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ (cH_ne_zero W) (cH_ne_top W)
  · exact hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)

end GlobalTheory.BaseChain

end
