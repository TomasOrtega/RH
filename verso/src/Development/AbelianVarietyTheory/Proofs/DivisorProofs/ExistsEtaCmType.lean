import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacteStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.EtaCMType

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) = (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))`. Rewrite using `[AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`.
-/
theorem idFF_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Fˣ) :
    idFF F E (Units.map (algebraMap F (AF F)).toMonoidHom a) =
      Units.map (incAF F E).toMonoidHom (Units.map (algebraMap F E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) =
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Use `haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)`. Conclude with `Continuous.units_map _ (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))`.
-/
theorem continuous_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Continuous (idFF F E) := by
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))

/- English proof (translation)
Introduce `u hu`. Establish `e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1)`. Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Rewrite using `[e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]`.
-/
theorem at_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : (AF F)ˣ)
    (h : At (evI F) ((a : AF F) - 1)) :
    At (evI F) (((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
  intro u hu
  have e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB`. Take `⟨ξ, hξ, hξe⟩` from `GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm F E σ B hB`. Take `⟨η₀, hη₀, huniq⟩` from `GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1`. Establish `hη₀' : IsEtaF E η₀` using `hη₀`. Set `lam : (AF F)ˣ →* Circle` to `ξ.comp (idFF F E) * η₀⁻¹`.

Establish `hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹` using `fun a => rfl`. Establish `hlc : Continuous lam`. Establish `: Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹` using `(hξ.1.comp continuous_idFF).mul (hη₀.1.inv)`. Conclude with `this`. Establish `hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1`.

Introduce `a`. Rewrite using `[hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]`. Establish `hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1`. Introduce `a ha`. Establish `e1` using `hξe _ (at_idFF a ha)`.

Establish `e2` using `GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns F E σ B hB η₀ hη₀' a ha`. Establish `e3 : ξ (idFF F E a) = η₀ a`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[e1, e2]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[zpow_one]`. Rewrite using `[hlam, e3, mul_inv_cancel]`. Take `⟨lam', hl'H, hl'inf, hl'res⟩` from `GlobalTheory.T.exists_unitaryHeckeCharacter_extending_baseCharacter F E σ B hB lam hlc hlF hlinf`. Use `⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ξ _ * (lam' _)⁻¹ = 1`.

Rewrite using `[hξ.2, hl'H.2, inv_one, one_mul]`. Express the relevant statement in the definitionally equal form `ξ _ * (lam' _)⁻¹ = _`. Rewrite using `[huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]`. Express the relevant statement in the definitionally equal form `((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _`. Rewrite using `[hl'inf z hz, inv_one, mul_one]`.

Conclude with `hξe z hz`.
-/
theorem exists_eta_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := GlobalTheory.T.exists_unitaryHeckeCharacter_extending_baseCharacter F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz

end GlobalTheory.EtaCMType
