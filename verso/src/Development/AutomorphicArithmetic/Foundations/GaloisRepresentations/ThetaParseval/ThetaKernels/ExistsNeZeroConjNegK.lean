import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.CMTraceZero
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB`. Take `⟨_, hc, _, hτ⟩` from `hB.cm`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => τ.injective (by rw [hτ, hτ, star_star])`. Establish `hne : ∃ x, σ x ≠ x`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hw` using `hc.isComplex w`. Rewrite `hw` using `[InfinitePlace.isComplex_iff]`.

Apply `hw` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `hτ w.embedding x` as an intermediate fact. Rewrite `this` using `[hall x]`.

Simplify using `using this.symm`. Take `⟨x, hx⟩` from `hne`. Use `⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hinv, neg_sub]`.
-/
theorem exists_ne_zero_conj_neg_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]
end GlobalTheory.CMTraceZero
end
