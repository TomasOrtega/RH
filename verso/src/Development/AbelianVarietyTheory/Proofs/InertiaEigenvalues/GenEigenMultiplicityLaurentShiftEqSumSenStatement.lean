import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PhiGam.Range.qmult_sh_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGenEigenMultiplicityLaurentShiftEqSumSen.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  first | exact @GlobalTheory.PhiGam.Range.qmult_sh_range | exact GlobalTheory.PhiGam.Range.qmult_sh_range | (intros; apply GlobalTheory.PhiGam.Range.qmult_sh_range <;> assumption)
