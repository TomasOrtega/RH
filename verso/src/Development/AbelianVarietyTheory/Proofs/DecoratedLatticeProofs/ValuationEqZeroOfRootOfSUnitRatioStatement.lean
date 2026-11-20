import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fam.vw_eq_zero_of_unitRatio` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FValuationEqZeroOfRootOfSUnitRatio.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  first | exact @GlobalTheory.Fam.vw_eq_zero_of_unitRatio | exact GlobalTheory.Fam.vw_eq_zero_of_unitRatio | (intros; apply GlobalTheory.Fam.vw_eq_zero_of_unitRatio <;> assumption)
