import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open MeasureTheory

namespace GlobalTheory.SplitWeil

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ i hi hi' x`. Use `haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1`. Use `haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2`. Use `haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1`. Use `haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2`.

Set `e : k ≃ₜ+ k'` to `{ i.toAddEquiv with continuous_toFun := hi continuous_invFun := hi' }`. Unfold `nabs`. Use `congr 1`. Conclude with `GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by`. Express the relevant statement in the definitionally equal form `i ((x : k) * y) = i x * i y`.

Conclude with `map_mul i _ _)`.
-/
theorem nabs_map_of_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' x
  haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1
  haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1
  haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2
  let e : k ≃ₜ+ k' :=
    { i.toAddEquiv with
      continuous_toFun := hi
      continuous_invFun := hi' }
  unfold nabs
  congr 1
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by
    change i ((x : k) * y) = i x * i y
    exact map_mul i _ _)

end GlobalTheory.SplitWeil
