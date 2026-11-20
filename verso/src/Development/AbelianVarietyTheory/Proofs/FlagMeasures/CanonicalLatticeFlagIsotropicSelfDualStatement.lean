import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCanonicalLatticeFlagIsotropicSelfDual.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  first | exact @GlobalTheory.FlagIso.flag_isotropic | exact GlobalTheory.FlagIso.flag_isotropic | (intros; apply GlobalTheory.FlagIso.flag_isotropic <;> assumption)
