import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

/- English proof (translation)
Introduce `l _ γ u y z N e δ hy hu hz he hT hδ`. Establish `hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c` using `fun _ => rfl`. Establish `hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖` using `fun c => by`. Rewrite using `[← hca, PadicComplex.norm_extends, norm_algebraMap']`. Establish `he0 : 0 ≤ e` using `(norm_nonneg _).trans he`.

Use `set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU`. Establish `hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e`. Rewrite using `[← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul, hca, ← GlobalTheory.RingBasics.σC_coe]`. Establish `h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l]) = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l]))`. Rewrite using `[map_sub, hy]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hU, h1]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hU, hn, hu, one_mul]`. Conclude with `he`.

Rewrite using `[norm_neg, GlobalTheory.RingBasics.norm_σC]`. Conclude with `he`. Establish `hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => simp [GlobalTheory.RingBasics.σC_one]`. Consider the case `succ i ih`. Rewrite using `[pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]`. Expand and normalize the polynomial expressions, which then agree. Establish `htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z`.

Establish `h` using `Finset.sum_range_sub (fun i => (γ ^ i) z) N`. Rewrite `h` using `[Finset.sum_sub_distrib]`. Simplify using `only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h`. Conclude with `sub_eq_zero.1 h`. Establish `hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z) = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z`.

Simplify using `only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS`. Establish `hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l])`. Simplify using `only [GlobalTheory.RingBasics.σC_coe]`.

Conclude with `map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _`. Establish `hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e`. Establish `h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l])`. Rewrite using `[UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, norm_neg, PadicComplex.norm_extends, ← hTv]`. Conclude with `hT.trans (mul_le_mul_of_nonneg_left hv hδ)`. Establish `hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by`. Rewrite using `[GlobalTheory.RingBasics.norm_σC]`. Conclude with `he`.

Establish `hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l])`. Rewrite using `[hSc, ← mul_add, ← Finset.sum_add_distrib]`. Simplify using `only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]`. Rewrite using `[← Finset.sum_mul, ← mul_assoc, mul_geom_sum]`. Rewrite using `[← hn, ← norm_mul, hmain]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)` and prove the remaining obligations. Establish `h3 : ‖U - 1‖ = ‖u - 1‖` using `by rw [← hn, map_sub, map_one]`. Rewrite using `[norm_mul, h3]`. Conclude with `mul_le_mul_of_nonneg_left hA (norm_nonneg _)`.
-/
theorem tate_eigenvector_estimate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  intro l _ γ u y z N e δ hy hu hz he hT hδ
  have hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c :=
    fun _ => rfl
  have hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖ := fun c => by
    rw [← hca, PadicComplex.norm_extends, norm_algebraMap']
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU
  have hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e := by
    rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
      hca, ← GlobalTheory.RingBasics.σC_coe]
    have h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l])
        = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l])) := by
      rw [map_sub, hy]; ring
    rw [← hU, h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hU, hn, hu, one_mul]; exact he
    · rw [norm_neg, GlobalTheory.RingBasics.norm_σC]; exact he
  have hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y := by
    intro i
    induction i with
    | zero => simp [GlobalTheory.RingBasics.σC_one]
    | succ i ih =>
      rw [pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]
      ring
  have htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z := by
    have h := Finset.sum_range_sub (fun i => (γ ^ i) z) N
    rw [Finset.sum_sub_distrib] at h
    simp only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h
    exact sub_eq_zero.1 h
  have hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)
      = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z := by
    simp only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one,
      ← Finset.mul_sum]
    ring
  set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS
  have hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l]) := by
    simp only [GlobalTheory.RingBasics.σC_coe]
    exact map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _
  have hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e := by
    have h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]; ring
    rw [h2, norm_neg, PadicComplex.norm_extends, ← hTv]
    exact hT.trans (mul_le_mul_of_nonneg_left hv hδ)
  have hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by
      rw [GlobalTheory.RingBasics.norm_σC]; exact he
  have hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y
      = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l]) := by
    rw [hSc, ← mul_add, ← Finset.sum_add_distrib]
    simp only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]
    rw [← Finset.sum_mul, ← mul_assoc, mul_geom_sum]
  rw [← hn, ← norm_mul, hmain]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)
  have h3 : ‖U - 1‖ = ‖u - 1‖ := by rw [← hn, map_sub, map_one]
  rw [norm_mul, h3]
  exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)

end GlobalTheory.InertiaEigenvalues
