import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocMod.normalFrames_exist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBesselFourierJacobiNormalFramesExistSplitPlace.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  first | exact @GlobalTheory.LocMod.normalFrames_exist | exact GlobalTheory.LocMod.normalFrames_exist | (intros; apply GlobalTheory.LocMod.normalFrames_exist <;> assumption)
