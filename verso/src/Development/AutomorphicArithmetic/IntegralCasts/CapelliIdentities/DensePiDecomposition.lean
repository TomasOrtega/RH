import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open MvPowerSeries in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`. Establish `h0 : f = 0`. Use extensionality with `n`.

Simplify using `using hf n (by simp)`. Simplify using `[h0]`. Consider the case `insert i s _ ih`. Introduce `f hf`. Set `h : MvPowerSeries σ O` to `fun n => if n i = 0 then coeff n f else 0`.

Establish `hh : ∀ n, coeff n h = if n i = 0 then coeff n f else 0` using `fun _ => rfl`. Establish `h1 : h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O))`. Use `ih h fun n hn => ?_` and prove the remaining obligations. Rewrite using `[hh]`. Use `split_ifs with hi`.

Use `hf n fun j hj => ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 hj with rfl | hj` into its components or cases. Conclude with `hi`. Conclude with `hn j hj`. Both sides reduce to the same expression.

Establish `h2 : (X i : MvPowerSeries σ O) ∣ f - h`. Use `X_dvd_iff.2 fun n hn => ?_` and prove the remaining obligations. Rewrite using `[map_sub, hh, if_pos hn, sub_self]`. Establish `h3 : f - h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O))` using `Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨i, rfl⟩)`. Simplify using `using Ideal.add_mem _ h3 h1`.
-/
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff {σ O : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    simp [h0]
  | insert i s _ ih =>
    intro f hf
    let h : MvPowerSeries σ O := fun n => if n i = 0 then coeff n f else 0
    have hh : ∀ n, coeff n h = if n i = 0 then coeff n f else 0 := fun _ => rfl
    have h1 : h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
      refine ih h fun n hn => ?_
      rw [hh]
      split_ifs with hi
      · refine hf n fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hi
        · exact hn j hj
      · rfl
    have h2 : (X i : MvPowerSeries σ O) ∣ f - h := by
      refine X_dvd_iff.2 fun n hn => ?_
      rw [map_sub, hh, if_pos hn, sub_self]
    have h3 : f - h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨i, rfl⟩)
    simpa using Ideal.add_mem _ h3 h1

open MvPowerSeries in
/- English proof (translation)
Establish `h` using `UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff Finset.univ (f - algebraMap O (MvPowerSeries σ O) (coeff 0 f)) (by`. Introduce `n hn`. Establish `h0 : n = 0`. Use extensionality with `i`. Simplify using `using hn i (Finset.mem_univ i)`.

Substitute `h0` using the available equality. Simplify using `[MvPowerSeries.algebraMap_apply])`. Take `⟨g, hg⟩` from `Ideal.mem_span_range_iff_exists_fun.1 h`. Conclude with `⟨coeff 0 f, g, by rw [hg]; ring⟩`.
-/
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp {σ O : Type} [CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O) :
    ∃ (c : O) (g : σ → MvPowerSeries σ O),
      f = algebraMap O (MvPowerSeries σ O) c + ∑ i, g i * X i := by
  classical
  have h := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff Finset.univ
    (f - algebraMap O (MvPowerSeries σ O) (coeff 0 f)) (by
      intro n hn
      have h0 : n = 0 := by
        ext i
        simpa using hn i (Finset.mem_univ i)
      subst h0
      simp [MvPowerSeries.algebraMap_apply])
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨coeff 0 f, g, by rw [hg]; ring⟩

/- English proof (translation)
Introduce `O _ _ X _ R _ _ _ W hz N`. Proceed by induction on `N with`. Consider the case `zero => intro x; exact ⟨0, W.A.zero_mem, by simp⟩`. Consider the case `succ N ih`. Introduce `x`.

Take `⟨f, rfl⟩` from `W.surj x`. Take `⟨c, g, rfl⟩` from `UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp f`. Use `choose a ha hm using fun i => ih (W.π (g i))`. Use `⟨algebraMap O R c + ∑ i, a i * W.z i, ?_, ?_⟩` and prove the remaining obligations. Conclude with `W.A.add_mem (W.A.algebraMap_mem c) (W.A.sum_mem fun i _ => W.A.mul_mem (ha i) (W.part_le_A (W.z_mem i)))`.

Establish `he : W.π (algebraMap O _ c + ∑ i, g i * MvPowerSeries.X i) - (algebraMap O R c + ∑ i, a i * W.z i) = ∑ i, (W.π (g i) - a i) * W.z i`. Rewrite using `[map_add, AlgHom.commutes, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, sub_mul]`. Both sides reduce to the same expression.

Rewrite using `[he, pow_succ]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hm i) (hz i)`.
-/
theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {X : Type} [inst_2 : AddCommGroup X] {R : Type}
      [inst_3 : CommRing R] [inst_4 : Algebra O R] [inst_5 : UpperTheory.V.Alg.IsCO O R] (W : UpperTheory.V.Alg.WPres O X R),
      (∀ (s : W.σ), W.z s ∈ IsLocalRing.maximalIdeal R) →
        ∀ (N : ℕ) (x : R), ∃ a ∈ W.A, x - a ∈ IsLocalRing.maximalIdeal R ^ N := by
  intro O _ _ X _ R _ _ _ W hz N
  induction N with
  | zero => intro x; exact ⟨0, W.A.zero_mem, by simp⟩
  | succ N ih =>
    intro x
    obtain ⟨f, rfl⟩ := W.surj x
    obtain ⟨c, g, rfl⟩ := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp f
    choose a ha hm using fun i => ih (W.π (g i))
    refine ⟨algebraMap O R c + ∑ i, a i * W.z i, ?_, ?_⟩
    · exact W.A.add_mem (W.A.algebraMap_mem c)
        (W.A.sum_mem fun i _ => W.A.mul_mem (ha i) (W.part_le_A (W.z_mem i)))
    · have he : W.π (algebraMap O _ c + ∑ i, g i * MvPowerSeries.X i)
          - (algebraMap O R c + ∑ i, a i * W.z i) = ∑ i, (W.π (g i) - a i) * W.z i := by
        rw [map_add, AlgHom.commutes, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, sub_mul]
        rfl
      rw [he, pow_succ]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hm i) (hz i)
