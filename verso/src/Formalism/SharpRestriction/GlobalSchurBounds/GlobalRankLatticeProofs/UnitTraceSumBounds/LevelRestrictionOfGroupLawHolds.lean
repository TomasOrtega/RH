import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawAlt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubeRelationOfParallelogram
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhGram
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GramUnit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GramIso
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhDualGram
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPhSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.JetsPhW

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

/- English proof (translation)
Unfold `G1.ph`. Rewrite using `[map_neg, neg_eq_zero]`. Use `show logMv _ 0 = 0`. Unfold `logMv`. Simplify using the standard rewrite rules.
-/
theorem ph0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.ph = 0 := by
  unfold G1.ph
  rw [map_neg, neg_eq_zero]
  show logMv _ 0 = 0
  unfold logMv
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.2.2.1, h.2.2.2, ph0 g⟩`.
-/
theorem fglData {p : ℕ} [Fact p.Prime] (g : G1 p) (h : g.Ok) : PI.FglGram.Data g.l g.ex g.ph :=
  ⟨h.2.2.1, h.2.2.2, ph0 g⟩

/- English proof (translation)
Introduce `p _ g h`. Conclude with `cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)`.
-/
theorem cube_of_two_identities_holds : CubeOfTwoIdentities := by
  intro p _ g h
  exact cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)

/- English proof (translation)
Use `first`. Consider the case `exact phase_gram'`. Consider the case `(intro p _ g; intros; apply phase_gram' <;> first | exact fglData g ‹_› | assumption)`. Consider the case `(unfold PhGramG; done)`.
-/
theorem phGramG_holds : PhGramG := by
  first
  | exact phase_gram'
  | (intro p _ g; intros; apply phase_gram' <;> first | exact fglData g ‹_› | assumption)
  | (unfold PhGramG; done)

/- English proof (translation)
Use `first`. Consider the case `exact gramExpansion_orthonormal`. Consider the case `(intro p _ g; intros; apply gramExpansion_orthonormal <;> first | exact fglData g ‹_› | assumption)`. Consider the case `(unfold GramUnitEq; done)`.
-/
theorem gramUnitEq_holds : GramUnitEq := by
  first
  | exact gramExpansion_orthonormal
  | (intro p _ g; intros; apply gramExpansion_orthonormal <;> first | exact fglData g ‹_› | assumption)
  | (unfold GramUnitEq; done)

/- English proof (translation)
Use `first`. Consider the case `exact flag_gram_iso`. Consider the case `(intro p _ g; intros; apply flag_gram_iso <;> first | exact fglData g ‹_› | assumption)`. Consider the case `(unfold GramIsoEq; done)`.
-/
theorem gramIsoEq_holds : GramIsoEq := by
  first
  | exact flag_gram_iso
  | (intro p _ g; intros; apply flag_gram_iso <;> first | exact fglData g ‹_› | assumption)
  | (unfold GramIsoEq; done)

/- English proof (translation)
Introduce `p hp g S hOk`. Conclude with `PI.Final.PhDualGram.phase_dual_gram p g.l g.ex g.ph S (fglData g hOk)`.
-/
theorem phDualOfGram_holds : PhDualOfGram := by
  intro p hp g S hOk; exact PI.Final.PhDualGram.phase_dual_gram p g.l g.ex g.ph S (fglData g hOk)

/- English proof (translation)
Introduce `p _ g S hg H1 H2 κ ι ι' _ _ _ b b' b'' hb hb' hb'' hd h1 h2`. Conclude with `PI.Final.FglPhSplit.norm_units_of_calculation ℂ_[p] (Wp p) ⟨g.l, g.ex, g.ph⟩ S hg.2.2.1 hg.2.2.2 (ph0 g) H1 H2 κ ι ι' b b' b'' hb hb' hb'' hd h1 h2`.
-/
theorem level_restriction_of_group_law_holds : LevelRestrictionOfGroupLaw := by
  intro p _ g S hg H1 H2 κ ι ι' _ _ _ b b' b'' hb hb' hb'' hd h1 h2
  exact PI.Final.FglPhSplit.norm_units_of_calculation ℂ_[p] (Wp p) ⟨g.l, g.ex, g.ph⟩ S hg.2.2.1 hg.2.2.2 (ph0 g) H1 H2 κ ι ι' b b' b'' hb hb' hb''
    hd h1 h2

/- English proof (translation)
Introduce `p _ g hOk` and use `jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2`.
-/
theorem jetsHigh_holds : JetsHigh :=
  fun p _ g hOk => jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

/- English proof (translation)
Introduce `p _ g hOk` and use `jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2`.
-/
theorem jetsOne_holds : JetsOne :=
  fun p _ g hOk => jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

/- English proof (translation)
Introduce `p _ g a b hOk` and use `jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2`.
-/
theorem jetsTwo_holds : JetsTwo :=
  fun p _ g a b hOk => jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1
    hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
