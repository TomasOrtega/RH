import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

/- English proof (translation)
Establish `hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}` using `by haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)`. Establish `h` using `isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous`. Rewrite `h` using `[RestrictedProduct.range_structureMap]`. Conclude with `h`. Set `g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F)` to `fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i`.

Establish `hg : Continuous g` using `continuous_pi fun i => continuous_const.mul (continuous_apply i)`. Establish `hP : IsCompact (Set.pi Set.univ fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F})` using `isCompact_univ_pi fun _ => hO`. Use `(hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_` and prove the remaining obligations. Introduce `z hz`. Use `⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩` and prove the remaining obligations.

Establish `h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v = (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v`. Establish `h1` using `map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)`. Rewrite `h1` using `[AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))]`. Conclude with `h1`. Use `show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _`.

Rewrite using `[h]`. Conclude with `hz i v`. Use function extensionality and compare the values at `i`. Simplify using `only [g]`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]`.
-/
theorem isCompact_scaledInt_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Finite κ] {a : F} (ha : a ≠ 0) :
    IsCompact (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    exact h
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have hP : IsCompact (Set.pi Set.univ fun _ : κ =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) := isCompact_univ_pi fun _ => hO
  refine (hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_
  intro z hz
  refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
  · have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
    rw [h]
    exact hz i v
  · funext i
    simp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

/- English proof (translation)
Introduce `F _ _ κ _ a ha r`. Establish `hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r` using `continuous_id.sub continuous_const`. Establish `hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}` using `⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩`. Establish `hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}` using `(Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)`. Generalize the expression as in `{y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`. Use `filter_upwards [hcl.isOpen.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use `filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)`.
-/
theorem indicator_coset_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a ha r
  have hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    ⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩
  have hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)
  generalize {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

end GlobalTheory.EvAdm
