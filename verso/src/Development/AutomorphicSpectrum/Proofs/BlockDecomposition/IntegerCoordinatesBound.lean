import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.NumberFieldCoord

/- English proof (translation)
Introduce `E _ _ I _ τ hτ`. Use `set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap with hLc`. Use `⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩` and prove the remaining obligations. Establish `hR0 : 0 ≤ R`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`.

Take `⟨i, -⟩` from `hτ w`. Conclude with `(norm_nonneg _).trans (hR i)`. Establish `hw : ∀ w : InfinitePlace E, w (e : E) ≤ R`. Introduce `w`. Take `⟨i, rfl⟩` from `hτ w`.

Simplify `hR i` using `only [InfinitePlace.apply]`. Establish `hn : ‖mixedEmbedding E (e : E)‖ ≤ R`. Rewrite using `[Prod.norm_def]`. Use `max_le ?_ ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_` and prove the remaining obligations.

Establish `h` using `hw w.1`. Rewrite `h` using `[← InfinitePlace.norm_embedding_of_isReal w.2]`. Simplify `h` using `[mixedEmbedding]`. Use `(pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_` and prove the remaining obligations. Establish `h` using `hw w.1`.

Rewrite `h` using `[← InfinitePlace.norm_embedding_eq]`. Simplify `h` using `[mixedEmbedding]`. Establish `hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)`. Express the relevant statement in the definitionally equal form `(mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _`. Rewrite using `[Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]`.

Use `integralBasis_repr_apply E e k` as an intermediate fact. Rewrite using `[show (e : E) = algebraMap (𝓞 E) E e from rfl, this]`. Simplify using the standard rewrite rules. Rewrite using `[← hval, ← Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith

end GlobalTheory.CompanionTheory.NumberFieldCoord
