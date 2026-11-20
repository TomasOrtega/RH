import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdeleCocompactExt

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Use `haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop`. Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)`. Use `haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)`. Take `⟨K, hK, hK'⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele F`.

Set `b` to `Module.finBasis F E`. Set `B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E)` to `Algebra.TensorProduct.basis (AF F) b`. Set `φ : (Fin (Module.finrank F E) → AF F) → AE F E` to `fun c => ∑ i, c i • B i`. Establish `hφ : Continuous φ` using `continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const`. Use `⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩` and prove the remaining obligations.

Use `choose x hx using fun i => hK' (B.repr a i)`. Use `⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩` and prove the remaining obligations. Establish `hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i` using `fun i => Algebra.TensorProduct.basis_apply _ _`. Establish `hincl : inclR (F` using `F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by`. Simplify using `only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul, Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]`.

Simplify using `only [φ, sub_smul, Finset.sum_sub_distrib, hincl]`. Rewrite using `[B.sum_repr a]`.
-/
theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
