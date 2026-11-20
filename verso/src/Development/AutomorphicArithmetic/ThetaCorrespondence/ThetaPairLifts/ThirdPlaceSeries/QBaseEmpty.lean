import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageXValid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
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
Unfold `_root_.GlobalTheory.BaseChain.inverseLevelCardinality`. Conclude with `ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)`.
-/
theorem cH_ne_zero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ 0 := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
/- English proof (translation)
Unfold `_root_.GlobalTheory.BaseChain.inverseLevelCardinality`. Establish `hpos : 0 < Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H` using `Nat.card_pos`. Conclude with `ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')`.
-/
theorem inverse_level_cardinality_ne_infinity (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  have hpos : 0 < Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Nat.card_pos
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')
/- English proof (translation)
The claim follows from `Finset.eq_empty_of_forall_notMem (_root_.GlobalTheory.MiTop.not_mem_Q_base' (W := W))`.
-/
theorem Q_base_eq_empty (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem (_root_.GlobalTheory.MiTop.not_mem_Q_base' (W := W))
/- English proof (translation)
Establish `lev` using `W.Q.charW.base.lev`. Establish `hM` using `(W.Q.charW.base.models.νX W.P.A3.A.μ0)`. Take `⟨c, hc⟩` from `lev.βX`. Use `⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show D.sp.X'.sig τ = _`.

Rewrite using `[D.X'_posDef τ, D.sp.X'_rank]`. Simplify using `[sigYD, Ranks.rankY, Ranks.rankX']`. Rewrite `hN` using `[one_pow, Nat.cast_one]`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)`. Use `show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _`.

Rewrite using `[_root_.GlobalTheory.BaseChain.Q_base_eq_empty W]`. Both sides reduce to the same expression. Conclude with `@MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W)`. Conclude with `hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)`.
-/
theorem stageX_is_at_m (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (_ : _root_.GlobalTheory.Fam.PackageHypotheses W) : (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) D.R.m := by
  have lev := W.Q.charW.base.lev
  have hM := (W.Q.charW.base.models.νX W.P.A3.A.μ0)
  obtain ⟨c, hc⟩ := lev.βX
  refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show D.sp.X'.sig τ = _
    rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
  · rw [one_pow, Nat.cast_one] at hN
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [_root_.GlobalTheory.BaseChain.Q_base_eq_empty W]; rfl
  · exact @MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W)
  · exact hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
