import Mathlib
import Formalism.PeriodIntegrals.FglPtW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

variable {K : Type*} [CommRing K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Treat this case separately.

Treat this case separately. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem serOver_iff (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by
  constructor
  · intro h
    refine ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, ?_⟩
    ext n
    first
    | rfl
    | simp [MvPowerSeries.coeff_map]
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

abbrev law (l ex : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst
    (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex

abbrev mulSer (l ex : PowerSeries K) (c : K) : MvPowerSeries Unit K :=
  PowerSeries.subst
    (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex

end PI.FglPtW.Wk

end
