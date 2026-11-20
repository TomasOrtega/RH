import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FExistsTrivialAtLevelUnitaryTransportSelfDual.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  first | exact @GlobalTheory.KerOntoStd.exists_trivAt_isMov | exact GlobalTheory.KerOntoStd.exists_trivAt_isMov | (intros; apply GlobalTheory.KerOntoStd.exists_trivAt_isMov <;> assumption)
