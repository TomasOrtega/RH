import Formalism.FilteredPoleLength.ReducedBasisBounds.TransvectionIsometry

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

section aux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- English proof (translation)
Establish `: CompleteSpace K` using `FiniteDimensional.complete ℝ K`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by`. Conclude with `K.exists_add_mem_mem_orthogonal a`. Use `⟨w, hw, z, fun p hp => ?_, h⟩` and prove the remaining obligations. Conclude with `Submodule.inner_right_of_mem_orthogonal hp hz`.
-/
private theorem exists_orth_decomp_of_finiteDimensional (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (a : V) : ∃ w ∈ K, ∃ z : V, (∀ p ∈ K, inner ℝ p z = 0) ∧ a = w + z := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  obtain ⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by
    exact K.exists_add_mem_mem_orthogonal a
  refine ⟨w, hw, z, fun p hp => ?_, h⟩
  exact Submodule.inner_right_of_mem_orthogonal hp hz

/- English proof (translation)
Establish `: FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι)))` using `FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)`. Take `⟨w, hw, z, hz, hwz⟩` from `exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a`. Use `⟨w, hw, z, hz, hwz, ?_⟩` and prove the remaining obligations. Rewrite using `[hwz, norm_add_sq_real, hz w hw]`. Use polynomial arithmetic with `[sq_nonneg ‖w‖]`.
-/
theorem exists_orth_split {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a
  refine ⟨w, hw, z, hz, hwz, ?_⟩
  rw [hwz, norm_add_sq_real, hz w hw]
  nlinarith [sq_nonneg ‖w‖]

/- English proof (translation)
Set `S : Submodule R M` to `{ carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i} add_mem' := by`. Introduce and unpack `y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩`. Conclude with `⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c y ⟨r, rfl⟩`. Conclude with `⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }`. Establish `hle : Submodule.span R (v '' (T : Set ι)) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, hj, rfl⟩`.

Use `show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i`. Use `⟨fun i => if i = j then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `i _ hij`.

Simplify using `[hij]`. Introduce `hjT`. Conclude with `absurd (Finset.mem_coe.mp hj) hjT`. Conclude with `hle hx`.
-/
private theorem exists_sum_repr_of_mem_span_image {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : ι → M) (T : Finset ι) (x : M) (hx : x ∈ Submodule.span R (v '' (T : Set ι))) :
    ∃ r : ι → R, x = ∑ i ∈ T, r i • v i := by
  classical
  let S : Submodule R M :=
    { carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i}
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩
        exact ⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c y ⟨r, rfl⟩
        exact ⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }
  have hle : Submodule.span R (v '' (T : Set ι)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hjT
      exact absurd (Finset.mem_coe.mp hj) hjT
  exact hle hx

/- English proof (translation)
Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `at hx`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Introduce `a s ha ih x hx`. Take `⟨r, hr⟩` from `exists_sum_repr_of_mem_span_image v (insert a s) x hx`. Rewrite `hr` using `[Finset.sum_insert ha]`. Take `⟨w, hw, z, hz, hwz, hzle⟩` from `exists_orth_split v s (v a)`.

Establish `hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι))` using `Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))`. Take `⟨k, hk⟩ : ∃ k : ℤ, k = round (r a)` from `⟨_, rfl⟩`. Establish `hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι))` using `Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)`. Take `⟨c', hc'⟩` from `ih _ hy'K`. Establish `hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι))` using `Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))`.

Establish `heK` using `Submodule.sub_mem _ hy'K hSK`. Use `⟨fun i => if i = a then k else c' i, ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i = ∑ i ∈ s, (c' i : ℝ) • v i`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hia : i ≠ a` using `fun h => ha (by rw [← h]; exact hi)`.

Rewrite using `[if_neg hia]`. Use `show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]`. Establish `hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) = (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i)`. Rewrite using `[hr, hwz]`.

Use `module`. Establish `horth : inner ℝ ((r a - k) • z) ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0`. Rewrite using `[real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]`. Establish `hround : (r a - k) ^ 2 ≤ 1 / 4`. Establish `h1 : |r a - k| ≤ 1 / 2`.

Rewrite using `[hk]`. Conclude with `abs_sub_round (r a)`. Use polynomial arithmetic with `[sq_abs (r a - k), abs_nonneg (r a - k), mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]`. Rewrite using `[hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]`. Establish `h2` using `mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)`.

Establish `h3` using `mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nearestPlane_finset {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  refine Finset.induction_on T ?_ ?_
  · intro x hx
    refine ⟨0, ?_⟩
    simp at hx
    subst hx
    simp
  · intro a s ha ih x hx
    obtain ⟨r, hr⟩ := exists_sum_repr_of_mem_span_image v (insert a s) x hx
    rw [Finset.sum_insert ha] at hr
    obtain ⟨w, hw, z, hz, hwz, hzle⟩ := exists_orth_split v s (v a)
    have hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (r a) := ⟨_, rfl⟩
    have hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)
    obtain ⟨c', hc'⟩ := ih _ hy'K
    have hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    have heK := Submodule.sub_mem _ hy'K hSK
    refine ⟨fun i => if i = a then k else c' i, ?_⟩
    have hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i
        = ∑ i ∈ s, (c' i : ℝ) • v i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (by rw [← h]; exact hi)
      rw [if_neg hia]
    show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2
      ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2
    rw [Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]
    have hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) =
        (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) := by
      rw [hr, hwz]
      module
    have horth : inner ℝ ((r a - k) • z)
        ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]
    have hround : (r a - k) ^ 2 ≤ 1 / 4 := by
      have h1 : |r a - k| ≤ 1 / 2 := by
        rw [hk]
        exact abs_sub_round (r a)
      nlinarith [sq_abs (r a - k), abs_nonneg (r a - k),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]
    rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)
    have h3 := mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith

end aux

/- English proof (translation)
Unfold `NearestPlane`. Introduce `V _ _ n v _ x hx`. Establish `hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n)))`. Rewrite using `[Finset.coe_univ, Set.image_univ]` and apply the resulting hypothesis. Conclude with `nearestPlane_finset v Finset.univ x hx'`.
-/
theorem nearestPlane : NearestPlane := by
  unfold NearestPlane
  intro V _ _ n v _ x hx
  have hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rwa [Finset.coe_univ, Set.image_univ]
  exact nearestPlane_finset v Finset.univ x hx'

end Formalism.LatticeBaseChangeAlt
