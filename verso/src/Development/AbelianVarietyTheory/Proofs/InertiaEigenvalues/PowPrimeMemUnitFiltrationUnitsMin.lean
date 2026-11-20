import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨w, hw⟩` from `ih`. Use `⟨(1 + y) * w + k, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_one_add_pow_eq y k`. Establish `h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w` using `by rw [hw]; ring`. Rewrite using `[h]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Use `Ideal.pow_le_pow_right (min_le_right _ _) ?_` and prove the remaining obligations.

Rewrite using `[add_comm n e, pow_add]`. Conclude with `Ideal.mul_mem_mul hk hy`. Use `Ideal.pow_le_pow_right (min_le_left _ _) ?_` and prove the remaining obligations. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Rewrite using `[two_mul, pow_add, pow_two]`.

Conclude with `Ideal.mul_mem_mul hy hy`.
-/
theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]`. Rewrite `h` using `[OrdIs]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

/- English proof (translation)
Introduce and unpack `_ ⟨u, hu, rfl⟩`. Use `⟨u ^ p, ?_, by simp⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[SetLike.mem_coe, mem_unitFiltration]`. Use `one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)` as an intermediate fact. Simplify using `using this`.
-/
theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
