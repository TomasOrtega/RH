import Mathlib

noncomputable section

open Module

namespace Formalism.L2.N.ExtNRows

section Generic

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/- English proof (translation)
Set `b` to `Module.finBasis K A`. Establish `hle : Submodule.span ℂ (j '' (A : Set (Fin n → K))) ≤ Submodule.span ℂ (Set.range fun k => j (b k : Fin n → K))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `e : x = ∑ k, (b.repr ⟨x, hx⟩ k) • (b k : Fin n → K)`.

Establish `h0` using `congrArg (fun v : A => (v : Fin n → K)) (b.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h0`. Conclude with `h0.symm`. Rewrite using `[e, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Use `le_trans (Submodule.finrank_mono hle) ?_` and prove the remaining obligations. Use `finrank_range_le_card (R := ℂ) (fun k => j (b k : Fin n → K))` as an intermediate fact. Simplify `this` using `[Set.finrank]`.
-/
theorem finrank_span_image_le {n : ℕ} (σ : K →+* ℂ) (j : (Fin n → K) →ₛₗ[σ] W) (A : Submodule K (Fin n → K)) :
    finrank ℂ (Submodule.span ℂ (j '' (A : Set (Fin n → K)))) ≤ finrank K A := by
  classical
  let b := Module.finBasis K A
  have hle : Submodule.span ℂ (j '' (A : Set (Fin n → K))) ≤ Submodule.span ℂ (Set.range fun k => j (b k : Fin n → K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have e : x = ∑ k, (b.repr ⟨x, hx⟩ k) • (b k : Fin n → K) := by
      have h0 := congrArg (fun v : A => (v : Fin n → K)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h0
      exact h0.symm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine le_trans (Submodule.finrank_mono hle) ?_
  have := finrank_range_le_card (R := ℂ) (fun k => j (b k : Fin n → K))
  simpa [Set.finrank] using this

/- English proof (translation)
Establish `hinj : Function.Injective (DirectSum.coeLinearMap B)` using `hi.dfinsupp_lsum_injective`. Rewrite using `[← Module.finrank_directSum, ← LinearMap.finrank_range_of_inj hinj, DirectSum.range_coeLinearMap]`.
-/
theorem sum_finrank_indep {ι : Type} [Fintype ι] (B : ι → Submodule ℂ W) (hi : iSupIndep B) :
    ∑ i, finrank ℂ (B i) = finrank ℂ (⨆ i, B i : Submodule ℂ W) := by
  classical
  have hinj : Function.Injective (DirectSum.coeLinearMap B) := hi.dfinsupp_lsum_injective
  rw [← Module.finrank_directSum, ← LinearMap.finrank_range_of_inj hinj, DirectSum.range_coeLinearMap]

/- English proof (translation)
Establish `hr : LinearMap.range (DirectSum.coeLinearMap B) = ⊤` using `by rw [DirectSum.range_coeLinearMap, ht]`. Establish `hs : Function.Surjective (DirectSum.coeLinearMap B)` using `LinearMap.range_eq_top.1 hr`. Establish `h1 : finrank ℂ W ≤ finrank ℂ (DirectSum ι fun i => B i)`. Use `LinearMap.finrank_range_le (DirectSum.coeLinearMap B)` as an intermediate fact. Rewrite `this` using `[hr, finrank_top]`. Then use the resulting hypothesis.

Establish `h2 : finrank ℂ (DirectSum ι fun i => B i) = finrank ℂ W` using `le_antisymm (by rw [Module.finrank_directSum]; exact hle) h1`. Conclude with `⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h2).2 hs, hs⟩`.
-/
theorem internal_of_top_le {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → Submodule ℂ W) (ht : (⨆ i, B i) = ⊤)
    (hle : ∑ i, finrank ℂ (B i) ≤ finrank ℂ W) : DirectSum.IsInternal B := by
  have hr : LinearMap.range (DirectSum.coeLinearMap B) = ⊤ := by rw [DirectSum.range_coeLinearMap, ht]
  have hs : Function.Surjective (DirectSum.coeLinearMap B) := LinearMap.range_eq_top.1 hr
  have h1 : finrank ℂ W ≤ finrank ℂ (DirectSum ι fun i => B i) := by
    have := LinearMap.finrank_range_le (DirectSum.coeLinearMap B)
    rwa [hr, finrank_top] at this
  have h2 : finrank ℂ (DirectSum ι fun i => B i) = finrank ℂ W :=
    le_antisymm (by rw [Module.finrank_directSum]; exact hle) h1
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h2).2 hs, hs⟩

end Generic

end Formalism.L2.N.ExtNRows

end
