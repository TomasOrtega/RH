import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGenerators

open scoped TensorProduct Polynomial
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ n t hspan hdim`. Establish `htm : ∀ i, t i ∈ maximalIdeal A` using `fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩`. Establish `hn : n = (maximalIdeal A).spanFinrank`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `ringKrullDim_le_spanFinrank_maximalIdeal A`.

Rewrite `h` using `[← hdim]`. Conclude with `h` after adjusting the coercions. Rewrite using `[← hspan]`. Use `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range t)).trans ?_` and prove the remaining obligations. Rewrite using `[← Set.image_univ]`.

Use `(Set.ncard_image_le Set.finite_univ).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A` using `ker_residue`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`.

Use `choose b hb using fun j => residue_surjective (R := A) (g j)`. Establish `hx : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A))`. Rewrite using `[hker]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (htm j)`. Establish `htk : ∀ j, algebraMap A (ResidueField A) (t j) = 0` using `fun j => by`.

Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `htm j`. Establish `h0 : KaehlerDifferential.kerCotangentToTensor k A (ResidueField A) ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨_, hx⟩) = 0`. Rewrite using `[KaehlerDifferential.kerCotangentToTensor_toCotangent, map_sum, tmul_sum, ← hg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one, Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[← hb j]`. Both sides reduce to the same expression. Establish `hinj` using `kerCotangentToTensor_injective_of_formallySmooth k A (ResidueField A) residue_surjective`. Establish `h2 : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) ^ 2` using `(Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))`.

Rewrite `h2` using `[hker]`. Use `coeffs_mem_maximalIdeal_of_sum_mem_sq t hspan hn b h2 i` as an intermediate fact. Rewrite using `[← hb i]`. Conclude with `(residue_eq_zero_iff _).2 this`.
-/
theorem linearIndependent_tmul_D_of_regular_system :
    ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  intro k A _ _ _ _ _ _ n t hspan hdim
  classical
  have htm : ∀ i, t i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n = (maximalIdeal A).spanFinrank := by
    apply le_antisymm
    · have h := ringKrullDim_le_spanFinrank_maximalIdeal A
      rw [← hdim] at h
      exact_mod_cast h
    · rw [← hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range t)).trans ?_
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j => residue_surjective (R := A) (g j)
  have hx : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [hker]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (htm j)
  have htk : ∀ j, algebraMap A (ResidueField A) (t j) = 0 := fun j => by
    rw [← RingHom.mem_ker, hker]; exact htm j
  have h0 : KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨_, hx⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_sum, tmul_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
      Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, smul_tmul', smul_eq_mul, mul_one]
    rw [← hb j]; rfl
  have hinj := kerCotangentToTensor_injective_of_formallySmooth k A (ResidueField A)
    residue_surjective
  have h2 : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker] at h2
  have := coeffs_mem_maximalIdeal_of_sum_mem_sq t hspan hn b h2 i
  rw [← hb i]
  exact (residue_eq_zero_iff _).2 this

end GlobalTheory
