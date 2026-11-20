import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleDecay

open scoped Classical

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Express the relevant statement in the definitionally equal form `Continuous fun x : InfiniteAdeleRing F => ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)), (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))`. Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.

Conclude with `h.comp continuous_fst`.
-/
theorem continuous_evI : Continuous (evI F) := by
  have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact h.comp continuous_fst

def intAdeles : AddSubgroup (AF F) where
  carrier := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
  add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

/- English proof (translation)
The claim follows from `(RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd`.
-/
theorem isOpen_intAdeles : IsOpen (intAdeles F : Set (AF F)) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
    Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd

/- English proof (translation)
Assemble the required witnesses or components as `⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_intAdeles F), isOpen_intAdeles F⟩`.
-/
theorem isClopen_intAdeles : IsClopen (intAdeles F : Set (AF F)) :=
  ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_intAdeles F), isOpen_intAdeles F⟩

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap`.
-/
theorem continuous_coord : Continuous (coord F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap

/- English proof (translation)
Unfold `size`. Conclude with `continuous_finset_sum _ fun i _ => ((continuous_evI F).comp ((continuous_apply i).comp (continuous_coord F E))).norm`.
-/
theorem continuous_size : Continuous (size F E) := by
  unfold size
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_evI F).comp ((continuous_apply i).comp (continuous_coord F E))).norm

/- English proof (translation)
Establish `hS : IsClopen {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F}`. Establish `: {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F} = ⋂ i, (fun l : (AE F E)ˣ => (m : AF F) * coord F E l.1 i) ⁻¹' (intAdeles F : Set (AF F))`. Use extensionality with `l`. Simplify using `[intAdeles]`. Rewrite using `[this]`.

Use `isClopen_iInter_of_finite fun i => (isClopen_intAdeles F).preimage ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply i).comp ((continuous_coord F E).comp Units.continuous_val))`. Establish `hf : Continuous fun l : (AE F E)ˣ => ((1 + size F E l.1) ^ N)⁻¹` using `((continuous_const.add ((continuous_size F E).comp Units.continuous_val)).pow N).inv₀ fun l => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (size_nonneg _)).ne'`. Unfold `decay`. Use `continuous_if ?_ hf.continuousOn continuous_const.continuousOn` and prove the remaining obligations.

Introduce `a ha`. Rewrite `ha` using `[hS.frontier_eq]`. Conclude with `absurd ha (Set.notMem_empty a)`.
-/
theorem continuous_decay (N m : ℕ) : Continuous (decay F E N m) := by
  have hS : IsClopen {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F} := by
    have : {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun l : (AE F E)ˣ => (m : AF F) * coord F E l.1 i) ⁻¹' (intAdeles F : Set (AF F)) := by
      ext l; simp [intAdeles]
    rw [this]
    refine isClopen_iInter_of_finite fun i => (isClopen_intAdeles F).preimage ?_
    exact continuous_const.mul ((continuous_apply i).comp ((continuous_coord F E).comp Units.continuous_val))
  have hf : Continuous fun l : (AE F E)ˣ => ((1 + size F E l.1) ^ N)⁻¹ :=
    ((continuous_const.add ((continuous_size F E).comp Units.continuous_val)).pow N).inv₀ fun l =>
      pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (size_nonneg _)).ne'
  unfold decay
  refine continuous_if ?_ hf.continuousOn continuous_const.continuousOn
  intro a ha
  rw [hS.frontier_eq] at ha
  exact absurd ha (Set.notMem_empty a)

/- English proof (translation)
Use `letI : BorelSpace (AE F E)ˣ := ⟨rfl⟩`. Conclude with `(continuous_decay F E N m).measurable`.
-/
theorem measurable_decay (N m : ℕ) : Measurable (decay F E N m) := by
  letI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact (continuous_decay F E N m).measurable

end GlobalTheory.IdeleDecay
