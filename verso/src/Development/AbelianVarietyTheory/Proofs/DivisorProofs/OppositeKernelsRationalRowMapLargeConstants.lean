import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

/- English proof (translation)
Use `⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK`. Introduce `Φ β d hd c i`. Take `⟨hβ, τ, hτ, hdτ⟩` from `hd`. Establish `hr` using `(hK.isRatAt hβ hτ hdτ c).2 i`.

Use `GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _) (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ …` and prove the remaining obligations. Introduce `k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CoefModel.mapVV_coe, bVV_coe]`. Conclude with `((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm`.

Introduce `k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CoefModel.mapVV_coe, bVV_coe]`. Conclude with `((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm`. Introduce `k l`.

Establish `h` using `hr k l`. Rewrite `h` using `[Normal.kkIn, LinearMap.toMatrix_apply]`. Then use the resulting hypothesis.
-/
theorem ratRowAt_big : BigC fun _ ch _ _ => RatRowAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c i
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).2 i
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k l
    have h := hr k l
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
