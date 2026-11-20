import Mathlib
import Formalism.PeriodIntegrals.EmbTraceSum

namespace PI.EmbTraceSumWork

/- English proof (translation)
Introduce `E _ _ K φ₀ S _ emb hinj hext hcard y`. Set `_ : Algebra K ℂ` to `(φ₀.comp (algebraMap K E)).toAlgebra`. Establish `: FiniteDimensional K E` using `FiniteDimensional.right ℚ K E`. Establish `: Algebra.IsSeparable K E` using `inferInstance`. Establish `hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a` using `fun s a => hext s a`.

Set `f : S → (E →ₐ[K] ℂ)` to `fun s => { emb s with commutes' := hcomm s }`. Establish `hf : Function.Injective f`. Introduce `s t h`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `x`.

Conclude with `DFunLike.congr_fun h x`. Establish `hbij : Function.Bijective f`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite using `[hcard, AlgHom.card]`.

Establish `htr` using `trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have : Algebra.IsSeparable K E := inferInstance
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a :=
    fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t h
    apply hinj
    ext x
    exact DFunLike.congr_fun h x
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    rw [hcard, AlgHom.card]
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl

end PI.EmbTraceSumWork
