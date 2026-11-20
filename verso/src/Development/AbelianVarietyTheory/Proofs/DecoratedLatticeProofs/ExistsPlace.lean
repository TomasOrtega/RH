import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod

namespace GlobalTheory.PlaceOfIdem

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.SplitIdem

/- English proof (translation)
Introduce `D e h`. Take `⟨v, he⟩` from `(isSplitIdem_iff e).1 h`. Set `` to `GlobalTheory.LocalData.complRel v`. Use `GlobalTheory.LocalData.isLocalField v` as an intermediate fact. Establish `: IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D)` using `⟨rfl⟩`.

Establish `: IsTopologicalRing (Formalism.L2.Theta.AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Establish `hev : Continuous (evalV D.host.F v)` using `RestrictedProduct.continuous_eval v`. Establish `hal : Continuous (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (Formalism.L2.Theta.AE D))`. Establish `hp : Continuous fun a : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v a)` using `Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)`. Use `⟨v.adicCompletion D.host.F, inferInstance, inferInstance, inferInstance, inferInstance, { e := e split := h π := comp he ι := AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun a b => by` and prove the remaining obligations.

Rewrite using `[singleV_sub, map_sub, sub_mul]`. Use `π_ι := fun x => ?_`. Use `ι_π := fun a => (sc_spec he a).symm`. Use `cont_π := ?_`. Use `cont_ι := (hal.comp hp).mul continuous_const }, rfl⟩`.

Use `show comp he (fj D (singleV D.host.F v x) * e) = x`. Rewrite using `[map_mul, comp_fj, comp_self, evalV_singleV_same, mul_one]`. Use `IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (comp he) ?_` and prove the remaining obligations. Establish `: ⇑((comp he).comp (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D))) = fun y => evalV D.host.F v y.2`. Use function extensionality and compare the values at `(comp_algebraMap he)`.

Rewrite using `[this]`. Conclude with `hev.comp continuous_snd`.
-/
theorem exists_place : ∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
      (p : Place D k), p.e = e := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  let := GlobalTheory.LocalData.complRel v
  have := GlobalTheory.LocalData.isLocalField v
  have : IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D) := ⟨rfl⟩
  have : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : Continuous (evalV D.host.F v) := RestrictedProduct.continuous_eval v
  have hal : Continuous (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (Formalism.L2.Theta.AE D))
  have hp : Continuous fun a : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v a) :=
    Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)
  refine ⟨v.adicCompletion D.host.F, inferInstance, inferInstance, inferInstance, inferInstance,
    { e := e
      split := h
      π := comp he
      ι := AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun a b => by
        rw [singleV_sub, map_sub, sub_mul]
      π_ι := fun x => ?_
      ι_π := fun a => (sc_spec he a).symm
      cont_π := ?_
      cont_ι := (hal.comp hp).mul continuous_const }, rfl⟩
  · show comp he (fj D (singleV D.host.F v x) * e) = x
    rw [map_mul, comp_fj, comp_self, evalV_singleV_same, mul_one]
  · refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (comp he) ?_
    have : ⇑((comp he).comp (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D))) = fun y => evalV D.host.F v y.2 :=
      funext (comp_algebraMap he)
    rw [this]
    exact hev.comp continuous_snd

end GlobalTheory.PlaceOfIdem
end
