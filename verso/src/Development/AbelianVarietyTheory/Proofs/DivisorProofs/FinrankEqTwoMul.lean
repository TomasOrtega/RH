import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAndMean
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PlaceWeights

open Classical in

/- English proof (translation)
Establish `h1 : (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)) = ∑ f : K →+* ℂ, (if InfinitePlace.mk f = v then (1 : ℝ) else 0)` using `(Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)).symm`. Rewrite using `[h1, Finset.sum_boole, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]`. Evaluate the numerical expressions.
-/
theorem sum_ind_algHom (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (v : InfinitePlace K) :
    (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)) = 2 := by
  have h1 : (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0))
      = ∑ f : K →+* ℂ, (if InfinitePlace.mk f = v then (1 : ℝ) else 0) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)).symm
  rw [h1, Finset.sum_boole, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
  norm_num

/- English proof (translation)
Rewrite using `[← InfinitePlace.sum_mult_eq]`. Simplify using `[IsTotallyComplex.mult_eq, mul_comm]`.
-/
theorem finrank_eq_two_mul (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [IsTotallyComplex.mult_eq, mul_comm]

open Classical in

/- English proof (translation)
Set `_ : Algebra K M` to `(σ₀.codRestrict M h).toAlgebra`. Establish `: IsScalarTower ℚ K M` using `IsScalarTower.of_algebraMap_eq (fun x => by simp)`. Establish `key` using `(GlobalTheory.EmbeddingMean.tower (K := ℚ) (A := K) (B := M) (C := ℂ)).2 (fun f => if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)`. Rewrite `key` using `[sum_ind_algHom, finrank_eq_two_mul K]`. Establish `hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Use `Eq.trans ?_ (key.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_ind_placeUnder (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ₀ : K →+* ℂ)
    (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M) (v : InfinitePlace K) :
    (∑ ρ : M →ₐ[ℚ] ℂ, (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0)) / (Module.finrank ℚ M : ℝ)
      = 1 / (Fintype.card (InfinitePlace K) : ℝ) := by
  let _ : Algebra K M := (σ₀.codRestrict M h).toAlgebra
  have : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  have key := (GlobalTheory.EmbeddingMean.tower (K := ℚ) (A := K) (B := M) (C := ℂ)).2
    (fun f => if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)
  rw [sum_ind_algHom, finrank_eq_two_mul K] at key
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · push_cast
    field_simp

/- English proof (translation)
Introduce `K _ _ _ σ₀ M _ h`. Establish `hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hM : (Module.finrank ℚ M : ℝ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℚ) (M := M)).ne'` after adjusting the coercions. Use `⟨fun v ρ => (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0) * ((Fintype.card (InfinitePlace K) : ℝ) / (Module.finrank ℚ M : ℝ)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v ρ`. Use `mul_nonneg ?_ (by positivity)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> norm_num`. Introduce `v`. Establish `key` using `sum_ind_placeUnder K σ₀ M h v`.

Rewrite using `[← Finset.sum_mul]`. Rewrite `key` using `[div_eq_div_iff hM hc]`. Rewrite using `[← mul_div_assoc, div_eq_one_iff_eq hM]`. Use `key using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Introduce `v ρ hw`. Assume the negation of the conclusion as `hne`. Conclude with `hw (by simp [hne])`. Introduce `ρ`. Rewrite using `[← Finset.sum_mul, Finset.sum_ite_eq]`.

Simplify using `only [Finset.mem_univ, if_true]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_weights : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M), ∃ wt : InfinitePlace K → (M →ₐ[ℚ] ℂ) → ℝ, (∀ v ρ, 0 ≤ wt v ρ) ∧ (∀ v, ∑ ρ, wt v ρ = 1) ∧ (∀ v ρ, wt v ρ ≠ 0 → placeUnder σ₀ h ρ = v) ∧ ∀ ρ, (∑ v, wt v ρ) / (Fintype.card (InfinitePlace K) : ℝ) = 1 / (Module.finrank ℚ M : ℝ) := by
  classical
  intro K _ _ _ σ₀ M _ h
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  refine ⟨fun v ρ => (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0) *
    ((Fintype.card (InfinitePlace K) : ℝ) / (Module.finrank ℚ M : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro v ρ
    refine mul_nonneg ?_ (by positivity)
    split_ifs <;> norm_num
  · intro v
    have key := sum_ind_placeUnder K σ₀ M h v
    rw [← Finset.sum_mul]
    rw [div_eq_div_iff hM hc] at key
    rw [← mul_div_assoc, div_eq_one_iff_eq hM]
    convert key using 1
    ring
  · intro v ρ hw
    by_contra hne
    exact hw (by simp [hne])
  · intro ρ
    rw [← Finset.sum_mul, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    field_simp

end GlobalTheory.PlaceWeights
