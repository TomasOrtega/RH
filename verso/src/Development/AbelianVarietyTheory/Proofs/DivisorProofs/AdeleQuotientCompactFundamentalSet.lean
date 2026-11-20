import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨K₀, hK₀, hK⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele F`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Set `b` to `Module.finBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) b`. Establish `hφ : Continuous B.equivFun.symm` using `IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap`. Use `⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩` and prove the remaining obligations. Introduce `a`.

Use `choose x hx using fun k => hK (B.equivFun a k)`. Use `⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `k`. Establish `h1 : B.equivFun (inclR (F` using `F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by`.

Rewrite using `[Module.Basis.equivFun_apply]`. Use `show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _`. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `[b, Module.Basis.repr_sum_self]`. Rewrite using `[Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]`.

Simplify using the standard rewrite rules. Simplify using `only [map_sub, Pi.sub_apply, h1]`.
-/
theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ a : AE F E, ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
