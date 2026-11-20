import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleFinite

/- English proof (translation)
Introduce `hT a ha n x y hrel htf`. Use `set b : R := algebraMap A R a with hb`. Establish `key : ∀ c : C, b • c = ∑ i, T (y i * c) • x i`. Introduce `c`. Establish `h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c`.

Introduce `i`. Rewrite using `[Algebra.smul_def, hT, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, hrel]`. Simplify using `[Algebra.smul_def]`. Set `S : Submodule R C` to `Submodule.span R (Set.range x)`.

Establish `hmem : ∀ c : C, b • c ∈ S`. Introduce `c`. Rewrite using `[key c]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `f : C →ₗ[R] S` to `LinearMap.codRestrict S (b • LinearMap.id) (fun c => by simpa using hmem c)`.

Establish `hf : Function.Injective f`. Introduce `c d hcd`. Establish `: b • c = b • d` using `by simpa [f] using congrArg Subtype.val hcd`. Establish `h0 : b • (c - d) = 0` using `by rw [smul_sub, this, sub_self]`. Conclude with `sub_eq_zero.mp (htf a ha _ h0)`.

Use `haveI : Module.Finite R S := Module.Finite.span_of_finite R (Set.finite_range x)`. Use `haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S`. Conclude with `Module.Finite.of_injective f hf`.
-/
theorem finite_of_trace_relation (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R) :
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  intro hT a ha n x y hrel htf
  set b : R := algebraMap A R a with hb

  have key : ∀ c : C, b • c = ∑ i, T (y i * c) • x i := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i
      rw [Algebra.smul_def, hT, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hrel]
    simp [Algebra.smul_def]
  let S : Submodule R C := Submodule.span R (Set.range x)
  have hmem : ∀ c : C, b • c ∈ S := by
    intro c
    rw [key c]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : C →ₗ[R] S := LinearMap.codRestrict S (b • LinearMap.id) (fun c => by simpa using hmem c)
  have hf : Function.Injective f := by
    intro c d hcd
    have : b • c = b • d := by simpa [f] using congrArg Subtype.val hcd
    have h0 : b • (c - d) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf a ha _ h0)
  haveI : Module.Finite R S := Module.Finite.span_of_finite R (Set.finite_range x)
  haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S
  exact Module.Finite.of_injective f hf

end GlobalTheory.GoodEtaleFinite
