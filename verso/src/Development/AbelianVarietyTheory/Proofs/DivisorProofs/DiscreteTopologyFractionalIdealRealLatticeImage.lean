import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

noncomputable def toMixedTR (F : Type) [Field F] [NumberField F] (x : RSp F) :
    mixedEmbedding.mixedSpace F :=
  (fun w => x (InfinitePlace.embedding_of_isReal w.prop), fun _ => 0)

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun w => ?_) continuous_const` and prove the remaining obligations. Conclude with `(PiLp.continuous_apply 2 _ _)`.
-/
theorem continuous_toMixedTR (F : Type) [Field F] [NumberField F] :
    Continuous (toMixedTR F) := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (PiLp.continuous_apply 2 _ _)

/- English proof (translation)
Use `Prod.ext (funext fun w => ?_) (funext fun w => ?_)` and prove the remaining obligations. Simplify using `[toMixedTR, mixedEmbedding.mixedEmbedding_apply_isReal]`. Conclude with `absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)`.
-/
theorem toMixedTR_remb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : F) :
    toMixedTR F (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simp [toMixedTR, mixedEmbedding.mixedEmbedding_apply_isReal]
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)

/- English proof (translation)
Introduce `F _ _ _ N`. Distinguish the cases in `hN : N = 0`. Establish `: Subsingleton (latOf N)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩`.

Take `⟨a, ha, rfl⟩` from `(mem_latOf N x).1 hx`. Take `⟨b, hb, rfl⟩` from `(mem_latOf N y).1 hy`. Substitute `hN` using the available equality. Rewrite `ha`, `hb` using `[FractionalIdeal.mem_zero_iff]`. Substitute `ha` using the available equality.

Substitute `hb` using the available equality. Both sides reduce to the same expression. Use `infer_instance`. Set `I : (FractionalIdeal (𝓞 F)⁰ F)ˣ` to `Units.mk0 N hN`. Establish `hmem : ∀ x : latOf N, toMixedTR F x ∈ mixedEmbedding.idealLattice F I`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨a, ha, rfl⟩` from `(mem_latOf N x).1 hx`. Rewrite using `[mixedEmbedding.mem_idealLattice]`. Conclude with `⟨a, ha, (toMixedTR_remb F a).symm⟩`. Set `h : latOf N → mixedEmbedding.idealLattice F I` to `fun x => ⟨toMixedTR F x, hmem x⟩`.

Use `DiscreteTopology.of_continuous_injective (f := h) ?_ ?_` and prove the remaining obligations. Conclude with `Continuous.subtype_mk ((continuous_toMixedTR F).comp continuous_subtype_val) _`. Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩ hxy`. Take `⟨a, ha, rfl⟩` from `(mem_latOf N x).1 hx`. Take `⟨b, hb, rfl⟩` from `(mem_latOf N y).1 hy`.

Establish `: toMixedTR F (remb F a) = toMixedTR F (remb F b)` using `congrArg Subtype.val hxy`. Rewrite `this` using `[toMixedTR_remb, toMixedTR_remb]`. Establish `hab` using `NumberField.mixedEmbedding_injective F this`. Substitute `hab` using the available equality. Both sides reduce to the same expression.
-/
theorem discrete_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  intro F _ _ _ N
  by_cases hN : N = 0
  · have : Subsingleton (latOf N) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      subst hN
      rw [FractionalIdeal.mem_zero_iff] at ha hb
      subst ha; subst hb; rfl
    infer_instance
  · let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hmem : ∀ x : latOf N, toMixedTR F x ∈ mixedEmbedding.idealLattice F I := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      rw [mixedEmbedding.mem_idealLattice]
      exact ⟨a, ha, (toMixedTR_remb F a).symm⟩
    let h : latOf N → mixedEmbedding.idealLattice F I := fun x => ⟨toMixedTR F x, hmem x⟩
    refine DiscreteTopology.of_continuous_injective (f := h) ?_ ?_
    · exact Continuous.subtype_mk ((continuous_toMixedTR F).comp continuous_subtype_val) _
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      have : toMixedTR F (remb F a) = toMixedTR F (remb F b) := congrArg Subtype.val hxy
      rw [toMixedTR_remb, toMixedTR_remb] at this
      have hab := NumberField.mixedEmbedding_injective F this
      subst hab; rfl

end GlobalTheory.LipschitzTR
