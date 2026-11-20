import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.SplitWeil.nabs_map_of_homeomorph | exact GlobalTheory.SplitWeil.nabs_map_of_homeomorph | (intros; apply GlobalTheory.SplitWeil.nabs_map_of_homeomorph <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.normalizedAbsValueLocalFieldUnit_map_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  first | exact @GlobalTheory.SplitWeil.nabs_map_of_homeomorph | exact GlobalTheory.SplitWeil.nabs_map_of_homeomorph | (intros; apply GlobalTheory.SplitWeil.nabs_map_of_homeomorph <;> assumption)
