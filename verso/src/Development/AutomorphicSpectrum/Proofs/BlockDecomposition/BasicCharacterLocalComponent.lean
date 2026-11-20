import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicCharLocal

open NumberField IsDedekindDomain

/- English proof (translation)
Establish `hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))` using `Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite`. Set `f : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal {v}ᶜ)` to `fun a => ⟨Pi.single v a, fun u hu => by`. Rewrite using `[Set.mem_setOf_eq, Pi.single_eq_of_ne hu]`. Conclude with `zero_mem _⟩`. Establish `hf : Continuous f` using `RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)`.

Conclude with `(RestrictedProduct.continuous_inclusion hS).comp hf`.
-/
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (HeckeCharacterZeroLocus.SiegelWeilU.singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/- English proof (translation)
Introduce `F _ _ ψ hψ v`. Use `⟨fun x y => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Use `Prod.ext (add_zero _).symm ?_` and prove the remaining obligations.

Conclude with `Subtype.ext (Pi.single_add v x y)`. Establish `h0 : HeckeCharacterZeroLocus.SiegelWeilU.pairA F 0 (HeckeCharacterZeroLocus.SiegelWeilU.singleV F v 0) = 0`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Conclude with `Subtype.ext (Pi.single_zero v)`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, h0]`.

Conclude with `AddChar.map_zero_eq_one ψ`. Conclude with `hψ.1.comp (Continuous.prodMk continuous_const (continuous_singleV F v))`.
-/
theorem psiBasic : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  intro F _ _ ψ hψ v
  classical
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · simp only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, ← AddChar.map_add_eq_mul]
    congr 1
    refine Prod.ext (add_zero _).symm ?_
    exact Subtype.ext (Pi.single_add v x y)
  · have h0 : HeckeCharacterZeroLocus.SiegelWeilU.pairA F 0 (HeckeCharacterZeroLocus.SiegelWeilU.singleV F v 0) = 0 := by
      refine Prod.ext rfl ?_
      exact Subtype.ext (Pi.single_zero v)
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, h0]
    exact AddChar.map_zero_eq_one ψ
  · exact hψ.1.comp (Continuous.prodMk continuous_const (continuous_singleV F v))

end GlobalTheory.CompanionTheory.AdelicCharLocal

end
