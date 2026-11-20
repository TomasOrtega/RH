import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)

/- English proof (translation)
Unfold `rA`. Conclude with `Algebra.subset_adjoin ⟨i, hi, a, rfl⟩`.
-/
private theorem ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

/- English proof (translation)
Unfold `omG`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun l _ => div_ne_zero (Units.ne_zero _) (Units.ne_zero _))`.
-/
private theorem omG_ne (i : Fin (d + 1)) : omG x i ≠ 0 := by
  unfold omG
  exact Finset.prod_ne_zero_iff.mpr (fun l _ => div_ne_zero (Units.ne_zero _) (Units.ne_zero _))

/- English proof (translation)
Unfold `omG`. Rewrite using `[← Finset.prod_mul_distrib]`. Establish `h : ∀ j, (x i' : F) / x j * (x j / x i) = x i' / x i` using `fun j => by`. Establish `h1` using `(x j).ne_zero`. Establish `h2` using `(x i).ne_zero`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
private theorem prod_eq (i i' : Fin (d + 1)) :
    (∏ j, (x i' : F) / x j) * omG x i = ((x i' : F) / x i) ^ (d + 1) := by
  unfold omG
  rw [← Finset.prod_mul_distrib]
  have h : ∀ j, (x i' : F) / x j * (x j / x i) = x i' / x i := fun j => by
    have h1 := (x j).ne_zero
    have h2 := (x i).ne_zero
    field_simp
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `hG` using `omG_ne x i`. Establish `key : ∀ i', (∏ j, (x i' : F) / x j) = ((x i' : F) / x i) ^ (d + 1) / omG x i` using `fun i' => by`. Rewrite using `[eq_div_iff hG, prod_eq]`. Simplify using `only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule, xv]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Establish `h1` using `hy i hi`. Rewrite `h1` using `[key, div_self (Units.ne_zero (x i)), one_pow]`. Rewrite `h1` using `[one_div, inv_mul_eq_div]`. Then use the resulting hypothesis. Introduce `hy i' hi'`.

Rewrite using `[key, div_mul_eq_mul_div, mul_div_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem x hi i') _) hy`.
-/
private theorem mem_omA_iff' {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (y : F) :
    y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I := by
  have hG := omG_ne x i
  have key : ∀ i', (∏ j, (x i' : F) / x j) = ((x i' : F) / x i) ^ (d + 1) / omG x i := fun i' => by
    rw [eq_div_iff hG, prod_eq]
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule, xv]
  constructor
  · intro hy
    have h1 := hy i hi
    rw [key, div_self (Units.ne_zero (x i)), one_pow] at h1
    rwa [one_div, inv_mul_eq_div] at h1
  · intro hy i' hi'
    rw [key, div_mul_eq_mul_div, mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem x hi i') _) hy

/- English proof (translation)
Establish `hs : (x j : F) / x i ∈ rA ℂ (xv x) I` using `ratio_mem x hi j`. Unfold `rA at hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, b, rfl⟩` from `hz`.

Break down `Finset.mem_insert.1 ha with h | h` into its components or cases. Rewrite using `[h]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `e : ((x j : F) / x i) ^ 1 * (xv x b / xv x j) = x b / x i`. Establish `h1` using `(x j).ne_zero`.

Establish `h2` using `(x i).ne_zero`. Simplify using `only [xv, pow_one]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `ratio_mem x hi b`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_mul]`. Conclude with `ratio_mem x h b`. Consider the case `algebraMap r`. Conclude with `⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨N1, h1⟩` from `hy`. Take `⟨N2, h2⟩` from `hz`. Use `⟨N1 + N2, ?_⟩` and prove the remaining obligations. Establish `e : ((x j : F) / x i) ^ (N1 + N2) * (y + z) = ((x j : F) / x i) ^ N2 * (((x j : F) / x i) ^ N1 * y) + ((x j : F) / x i) ^ N1 * (((x j : F) / x i) ^ N2 * z)` using `by ring`.

Rewrite using `[e]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h1) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h2)`. Consider the case `mul y z _ _ hy hz`. Take `⟨N1, h1⟩` from `hy`. Take `⟨N2, h2⟩` from `hz`.

Use `⟨N1 + N2, ?_⟩` and prove the remaining obligations. Establish `e : ((x j : F) / x i) ^ (N1 + N2) * (y * z) = (((x j : F) / x i) ^ N1 * y) * (((x j : F) / x i) ^ N2 * z)` using `by ring`. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ h1 h2`.
-/
private theorem loc_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) (y : F)
    (hy : y ∈ rA ℂ (xv x) (insert j I)) : ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ rA ℂ (xv x) I := by
  have hs : (x j : F) / x i ∈ rA ℂ (xv x) I := ratio_mem x hi j
  unfold rA at hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, rfl⟩ := hz
    rcases Finset.mem_insert.1 ha with h | h
    · rw [h]
      refine ⟨1, ?_⟩
      have e : ((x j : F) / x i) ^ 1 * (xv x b / xv x j) = x b / x i := by
        have h1 := (x j).ne_zero
        have h2 := (x i).ne_zero
        simp only [xv, pow_one]
        field_simp
      rw [e]
      exact ratio_mem x hi b
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact ratio_mem x h b
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y + z) = ((x j : F) / x i) ^ N2 * (((x j : F) / x i) ^ N1 * y) + ((x j : F) / x i) ^ N1 * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h1) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h2)
  | mul y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y * z) = (((x j : F) / x i) ^ N1 * y) * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.mul_mem _ h1 h2

end

/- English proof (translation)
Introduce `F _ _ d x _ I i hi`. Use `⟨?_, mem_omA_iff' x hi, ?_⟩` and prove the remaining obligations. Unfold `UpperTheory.Gal.productCup_of_system.Lat`. Use `⟨?_, 1, fun _ => omG x i, fun _ => LinearMap.mulLeft F (omG x i)⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha m hm`.

Rewrite using `[smul_eq_mul, mem_omA_iff' x hi, mul_div_assoc]`. Conclude with `Subalgebra.mul_mem _ ha ((mem_omA_iff' x hi m).1 hm)`. Introduce `_`. Rewrite using `[mem_omA_iff' x hi, div_self (omG_ne x i)]`. Conclude with `Subalgebra.one_mem _`.

Introduce `_ m hm`. Rewrite using `[LinearMap.mulLeft_apply, inv_mul_eq_div]`. Conclude with `(mem_omA_iff' x hi m).1 hm`. Introduce `m _`. Rewrite using `[Fin.sum_univ_one, LinearMap.mulLeft_apply, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (omG_ne x i), one_mul]`.

Introduce `j y hy`. Take `⟨N, hN⟩` from `loc_mem x hi j _ ((mem_omA_iff' x (Finset.mem_insert_of_mem hi) y).1 hy)`. Conclude with `⟨N, (mem_omA_iff' x hi _).2 (by rwa [mul_div_assoc])⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.latA_of :
    LatA := by
  intro F _ _ d x _ I i hi
  refine ⟨?_, mem_omA_iff' x hi, ?_⟩
  · unfold UpperTheory.Gal.productCup_of_system.Lat
    refine ⟨?_, 1, fun _ => omG x i, fun _ => LinearMap.mulLeft F (omG x i)⁻¹, ?_, ?_, ?_⟩
    · intro a ha m hm
      rw [smul_eq_mul, mem_omA_iff' x hi, mul_div_assoc]
      exact Subalgebra.mul_mem _ ha ((mem_omA_iff' x hi m).1 hm)
    · intro _
      rw [mem_omA_iff' x hi, div_self (omG_ne x i)]
      exact Subalgebra.one_mem _
    · intro _ m hm
      rw [LinearMap.mulLeft_apply, inv_mul_eq_div]
      exact (mem_omA_iff' x hi m).1 hm
    · intro m _
      rw [Fin.sum_univ_one, LinearMap.mulLeft_apply, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (omG_ne x i), one_mul]
  · intro j y hy
    obtain ⟨N, hN⟩ := loc_mem x hi j _ ((mem_omA_iff' x (Finset.mem_insert_of_mem hi) y).1 hy)
    exact ⟨N, (mem_omA_iff' x hi _).2 (by rwa [mul_div_assoc])⟩
