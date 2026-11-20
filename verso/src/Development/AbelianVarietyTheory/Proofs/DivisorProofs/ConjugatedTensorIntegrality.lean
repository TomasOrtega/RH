import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventuallyStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntSpan

/- English proof (translation)
Introduce `C _ _ _ L _ _ ι hι κ b κ' bL`. Take `⟨S₁, h₁⟩` from `GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul C κ b`. Take `⟨S₂, h₂⟩` from `GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul L κ' bL`. Take `⟨S₃, h₃⟩` from `GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually L κ' bL`. Use `⟨S₁ ∪ S₂ ∪ S₃, fun v hv X E hE => ?_⟩` and prove the remaining obligations.

Simplify using `only [Finset.mem_union, not_or] at hv`. Take `⟨⟨hv1, hv2⟩, hv3⟩` from `hv`. Establish `hint` using `GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v C κ b (h₁ v hv1).1 (h₁ v hv1).2 _ hE`. Establish `hE'` using `isIntegral_of_isIntegral_conj X _ hint`. Set `F : v.adicCompletion ℚ ⊗[ℚ] L →ₐ[v.adicCompletion ℚ] v.adicCompletion ℚ ⊗[ℚ] C` to `Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion ℚ) (v.adicCompletion ℚ)) ι`.

Establish `hF : ∀ x, F x = Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι x` using `fun x => rfl`. Establish `hinj : Function.Injective (F.restrictScalars (v.adicCompletionIntegers ℚ))`. Introduce `x y hxy`. Conclude with `map_id_injective (v.adicCompletion ℚ) ι hι (by simpa [hF] using hxy)`. Establish `hE'' : IsIntegral (v.adicCompletionIntegers ℚ) E` using `(isIntegral_algHom_iff (F.restrictScalars (v.adicCompletionIntegers ℚ)) hinj).1 (by simpa [hF] using hE')`.

Use `h₃ v hv3 E fun i => mem_of_isIntegral v ?_` and prove the remaining obligations. Establish `hb : IsIntegral (v.adicCompletionIntegers ℚ) ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)` using `GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v L κ' bL (h₂ v hv2).1 (h₂ v hv2).2 _ (isIntB_tmul_basis v bL i)`. Conclude with `GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral _ _ _ _ (hE''.mul hb)`.
-/
theorem isIntB_of_isIntB_conj : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  intro C _ _ _ L _ _ ι hι κ b κ' bL
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul C κ b
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul L κ' bL
  obtain ⟨S₃, h₃⟩ := GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually L κ' bL
  refine ⟨S₁ ∪ S₂ ∪ S₃, fun v hv X E hE => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hint := GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v C κ b (h₁ v hv1).1 (h₁ v hv1).2 _ hE
  have hE' := isIntegral_of_isIntegral_conj X _ hint
  let F : v.adicCompletion ℚ ⊗[ℚ] L →ₐ[v.adicCompletion ℚ] v.adicCompletion ℚ ⊗[ℚ] C :=
    Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion ℚ) (v.adicCompletion ℚ)) ι
  have hF : ∀ x, F x = Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι x := fun x => rfl
  have hinj : Function.Injective (F.restrictScalars (v.adicCompletionIntegers ℚ)) := by
    intro x y hxy
    exact map_id_injective (v.adicCompletion ℚ) ι hι (by simpa [hF] using hxy)
  have hE'' : IsIntegral (v.adicCompletionIntegers ℚ) E :=
    (isIntegral_algHom_iff (F.restrictScalars (v.adicCompletionIntegers ℚ)) hinj).1 (by simpa [hF] using hE')
  refine h₃ v hv3 E fun i => mem_of_isIntegral v ?_
  have hb : IsIntegral (v.adicCompletionIntegers ℚ) ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i) :=
    GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v L κ' bL (h₂ v hv2).1 (h₂ v hv2).2 _ (isIntB_tmul_basis v bL i)
  exact GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral _ _ _ _ (hE''.mul hb)

end GlobalTheory.LocIntSpan
