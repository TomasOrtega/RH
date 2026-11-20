import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatio
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TowerDifferent.relDifferent_order_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRelativeDifferentOrderBoundedAbsoluteRamificatio.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.relative_different_order_bounded_absolute_ramification : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  first | exact @GlobalTheory.TowerDifferent.relDifferent_order_bounded | exact GlobalTheory.TowerDifferent.relDifferent_order_bounded | (intros; apply GlobalTheory.TowerDifferent.relDifferent_order_bounded <;> assumption)
