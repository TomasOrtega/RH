import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Set `b` to `Module.finBasis K V`. Break down `isEmpty_or_nonempty (Fin (Module.finrank K V)) with hE | hNE` into its components or cases. Use `⟨0, fun z => ?_⟩` and prove the remaining obligations. Establish `hz : z = 0` using `by rw [← b.sum_repr z]; simp`. Simplify using `[hz]`.

Establish `hli : LinearIndependent K (fun i => B (b i))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1 : B (∑ j, star (g j) • b j) = 0`. Rewrite using `[map_sum]`.

Simplify using `only [map_smulₛₗ, starRingEnd_apply, star_star]`. Conclude with `hg`. Establish `h2 : ∑ j, star (g j) • b j = 0` using `hnd _ (fun y => by rw [h1, LinearMap.zero_apply])`. Establish `h3` using `(Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2 i`. Conclude with `star_eq_zero.mp h3`.

Establish `hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K (V →ₗ[K] K)`. Rewrite using `[Fintype.card_fin]`. Conclude with `(Subspace.dual_finrank_eq).symm`. Set `b'` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Use `⟨∑ i, star (b'.repr φ i) • b i, fun z => ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← b'.sum_repr φ]`. Rewrite using `[map_sum, LinearMap.sum_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, starRingEnd_apply, star_star, coe_basisOfLinearIndependentOfCardEqFinrank]`.
-/
theorem riesz [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (φ : V →ₗ[K] K) : ∃ v, ∀ z, B v z = φ z := by
  classical
  let b := Module.finBasis K V
  rcases isEmpty_or_nonempty (Fin (Module.finrank K V)) with hE | hNE
  · refine ⟨0, fun z => ?_⟩
    have hz : z = 0 := by rw [← b.sum_repr z]; simp
    simp [hz]
  have hli : LinearIndependent K (fun i => B (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : B (∑ j, star (g j) • b j) = 0 := by
      rw [map_sum]
      simp only [map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h2 : ∑ j, star (g j) • b j = 0 := hnd _ (fun y => by rw [h1, LinearMap.zero_apply])
    have h3 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2 i
    exact star_eq_zero.mp h3
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K (V →ₗ[K] K) := by
    rw [Fintype.card_fin]; exact (Subspace.dual_finrank_eq).symm
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨∑ i, star (b'.repr φ i) • b i, fun z => ?_⟩
  conv_rhs => rw [← b'.sum_repr φ]
  rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
    coe_basisOfLinearIndependentOfCardEqFinrank]

end PI.Witt
