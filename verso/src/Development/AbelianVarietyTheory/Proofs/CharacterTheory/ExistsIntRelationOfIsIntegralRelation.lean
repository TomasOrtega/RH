import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn`. Establish `hq : x = algebraMap ℚ ℂ ((k : ℚ) / n)`. Simplify using `only [eq_ratCast, Rat.cast_div, Rat.cast_intCast]`. Rewrite using `[eq_div_iff hn', mul_comm, h]`. Rewrite `hx` using `[hq, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective]`.

Take `⟨j, hj⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hx`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, ← hj]`. Simplify using the standard rewrite rules.
-/
theorem exists_int_eq_of_isIntegral_of_mul_eq_int {x : ℂ} (hx : IsIntegral ℤ x) {n k : ℤ}
    (hn : n ≠ 0) (h : (n : ℂ) * x = k) : ∃ j : ℤ, (j : ℂ) = x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hq : x = algebraMap ℚ ℂ ((k : ℚ) / n) := by
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_intCast]
    rw [eq_div_iff hn', mul_comm, h]
  rw [hq, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hx
  obtain ⟨j, hj⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  refine ⟨j, ?_⟩
  rw [hq, ← hj]
  simp

/- English proof (translation)
Introduce `ι _ r hr`. Set `f : (ι → ℤ) →ₗ[ℤ] ℂ` to `Fintype.linearCombination ℤ r`. Establish `hf : ∀ m, f m = ∑ i, r i * (m i : ℂ)`. Introduce `m`. Simplify using `[f, Fintype.linearCombination_apply, mul_comm]`.

Establish `hfi : ∀ m, IsIntegral ℤ (f m)`. Introduce `m`. Rewrite using `[hf]`. Use `IsIntegral.sum _ fun i _ => (hr i).mul ?_` and prove the remaining obligations. Conclude with `isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := m i)`.

Set `K : Submodule ℤ (ι → ℤ)` to `(LinearMap.range (Algebra.linearMap ℤ ℂ)).comap f`. Establish `hK : ∀ m, m ∈ K ↔ ∃ j : ℤ, (j : ℂ) = f m`. Introduce `m`. Simplify using `[K]`. Establish `: Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ K)`.

Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `n x hx`. Distinguish the cases in `hn : n = 0`. Conclude with `Or.inl hn`. Use `right`.

Take `⟨m, rfl⟩` from `K.mkQ_surjective x`. Rewrite `hx` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]`. Take `⟨k, hk⟩` from `hx`. Use `exists_int_eq_of_isIntegral_of_mul_eq_int (hfi m) hn (k := k) ?_` and prove the remaining obligations.

Rewrite using `[hk, map_smul, zsmul_eq_mul]`. Take `⟨s, hs⟩` from `Module.projective_lifting_property K.mkQ (LinearMap.id) K.mkQ_surjective`. Set `p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)` to `LinearMap.id - s ∘ₗ K.mkQ`. Establish `hp : ∀ m, p m ∈ K`. Introduce `m`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]`. Use `LinearMap.congr_fun hs (K.mkQ m)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Simplify using `only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]`. Establish `hp' : ∀ m ∈ K, p m = m`.

Introduce `m hm`. Establish `: K.mkQ m = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hm`. Simplify using `only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, this, map_zero, sub_zero]`.

Use `choose c hc using fun i : ι => (hK _).mp (hp (Pi.single i 1))`. Use `⟨c, fun m d h => ?_⟩` and prove the remaining obligations. Establish `hm : m ∈ K` using `(hK m).mpr ⟨d, by rw [hf, h]⟩`. Establish `hdec : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ)`. Use extensionality with `j`.

Simplify using `[Pi.single_apply]`. Establish `key : ((∑ i, c i * m i : ℤ) : ℂ) = f (p m)` using `by conv_rhs => rw [hdec]`. Rewrite using `[map_sum, map_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, map_smul, ← hc, zsmul_eq_mul, mul_comm]`. Rewrite `key` using `[hp' m hm, hf, h]`. Conclude with `key` after adjusting the coercions.
-/
theorem exists_int_retraction_of_isIntegral :
    ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) →
      ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  intro ι _ r hr
  classical
  let f : (ι → ℤ) →ₗ[ℤ] ℂ := Fintype.linearCombination ℤ r
  have hf : ∀ m, f m = ∑ i, r i * (m i : ℂ) := by
    intro m
    simp [f, Fintype.linearCombination_apply, mul_comm]
  have hfi : ∀ m, IsIntegral ℤ (f m) := by
    intro m
    rw [hf]
    refine IsIntegral.sum _ fun i _ => (hr i).mul ?_
    exact isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := m i)
  let K : Submodule ℤ (ι → ℤ) := (LinearMap.range (Algebra.linearMap ℤ ℂ)).comap f
  have hK : ∀ m, m ∈ K ↔ ∃ j : ℤ, (j : ℂ) = f m := by
    intro m
    simp [K]
  have : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ K) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    obtain ⟨m, rfl⟩ := K.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]
    obtain ⟨k, hk⟩ := hx
    refine exists_int_eq_of_isIntegral_of_mul_eq_int (hfi m) hn (k := k) ?_
    rw [hk, map_smul, zsmul_eq_mul]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id) K.mkQ_surjective
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s ∘ₗ K.mkQ
  have hp : ∀ m, p m ∈ K := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (K.mkQ m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this,
      sub_self]
  have hp' : ∀ m ∈ K, p m = m := by
    intro m hm
    have : K.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hm
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, this, map_zero,
      sub_zero]
  choose c hc using fun i : ι => (hK _).mp (hp (Pi.single i 1))
  refine ⟨c, fun m d h => ?_⟩
  have hm : m ∈ K := (hK m).mpr ⟨d, by rw [hf, h]⟩
  have hdec : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
    ext j
    simp [Pi.single_apply]
  have key : ((∑ i, c i * m i : ℤ) : ℂ) = f (p m) := by
    conv_rhs => rw [hdec]
    rw [map_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← hc, zsmul_eq_mul, mul_comm]
  rw [hp' m hm, hf, h] at key
  exact_mod_cast key

end GlobalTheory.CuspGL
