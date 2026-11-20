import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexColengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernelStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/- English proof (translation)
Distinguish the cases in `hx : v.1 x = 0`. Rewrite using `[hx]`. Conclude with `zero_le'`. Rewrite using `[← WithZero.exp_log hx, WithZero.exp_le_exp]`. Unfold `ord at h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem val_le_exp_of_ord (v : Place k F) (x : F) (d : ℤ) (hd : 0 ≤ d) (h : -d ≤ ord v x) :
    v.1 x ≤ WithZero.exp d := by
  by_cases hx : v.1 x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    unfold ord at h; omega

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Conclude with `(v.2.2 c hc).le`.
-/
theorem val_algebraMap_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

/- English proof (translation)
Apply `v.1.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[Algebra.smul_def, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_comb_le (v : Place k F) {m : ℕ} (f : Fin m → F) (c : Fin m → k)
    (B : WithZero (Multiplicative ℤ)) (h : ∀ j, v.1 (f j) ≤ B) : v.1 (∑ j, c j • f j) ≤ B := by
  apply v.1.map_sum_le
  intro j _
  rw [Algebra.smul_def, map_mul]
  calc v.1 (algebraMap k F (c j)) * v.1 (f j) ≤ 1 * B := mul_le_mul' (val_algebraMap_le_one v _) (h j)
    _ = B := one_mul B

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `v.1.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_mulVec_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, v.1 (M i j) ≤ 1) (p : Fin n → F) (hp : ∀ i, v.1 (p i) ≤ 1) (i : Fin n) :
    v.1 (M.mulVec p i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply v.1.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (M i j) * v.1 (p j) ≤ 1 * 1 := mul_le_mul' (hM i j) (hp j)
    _ = 1 := one_mul 1

/- English proof (translation)
Use `⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat, fun i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : v.1 (M i j) = 0`. Rewrite using `[hx]`. Conclude with `zero_le'`. Rewrite using `[← WithZero.exp_log hx, WithZero.exp_le_exp]`.

Use `Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat) (Finset.mem_univ (i, j))` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_exp_bound (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ d : ℕ, ∀ i j, v.1 (M i j) ≤ WithZero.exp (d : ℤ) := by
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat,
    fun i j => ?_⟩
  by_cases hx : v.1 (M i j) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat)
      (Finset.mem_univ (i, j))
    simp only at this
    omega

/- English proof (translation)
Introduce `k F _ _ _ _ _ hFF`. Take `⟨γ, hγ⟩` from `GlobalTheory.T.riemann_inequality_cofinal_functionField k F hFF`. Use `⟨γ, fun n g hg hdeg => ?_⟩` and prove the remaining obligations. Use `set B := hg.2.toFinset with hBdef`. Use `choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹`.

Set `D : Place k F →₀ ℤ` to `Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0) (by intro v hv; by_contra h; exact hv (if_neg h))`. Take `⟨D', hDD', m, f, hf, hm, hford⟩` from `hγ D`. Apply the tactic sequence `have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)`. Establish `hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧ ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 → ∀ i, v.1 ((g v).mulVec p i) ≤ 1`. Introduce `v`.

Use `GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser k F hFF v n (g v) _ (hg.1 v) ?_` and prove the remaining obligations. Introduce `i j`. Distinguish the cases in `hv : v ∈ B`. Establish `hDv : D v = d0 v` using `by simp [D, Finsupp.onFinset_apply, hv]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[WithZero.exp_le_exp]`. Use `hDD' v` as an intermediate fact. Rewrite `this` using `[hDv]`. Use linear arithmetic over natural numbers and integers. Establish `hU : Unimod v (g v)` using `by simpa [B] using hv`.

Establish `hU'` using `((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2`. Combine the equalities or inequalities in the displayed calculation. Use `choose N φ hN hφ using hloc`. Use `set S := B ∪ D'.support with hS`. Establish `hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v`.

Unfold `Finsupp.sum`. Apply `Finset.sum_subset Finset.subset_union_right` to reduce the goal to its premises. Introduce `v _ hv`. Simplify using `using hv`. Establish `hdegS : deg g = ∑ v ∈ S, ord v (g v).det`.

Unfold `deg`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[Finset.coe_union]`. Use `left`.

Simplify using `only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Introduce `hU`. Apply `hv` to reduce the goal to its premises. Simplify using `[ord, hU.2]`. Establish `hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m`.

Use `push_cast`. Rewrite using `[Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]`. Establish `: ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v` using `fun v => Int.toNat_of_nonneg (hD0 v)`. Repeatedly rewrite using `[this]`. Rewrite using `[← hsumD, ← hdegS]`.

Use `mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨c, hp0, hpψ⟩` from `GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)`. Use `⟨_, hp0, fun v i => ?_⟩` and prove the remaining obligations. Establish `hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)` using `fun i => val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega) (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))`.

Distinguish the cases in `hv : v ∈ S`. Conclude with `hφ v _ hpb (hpψ v hv) i`. Establish `hvB : v ∉ B` using `fun h => hv (Finset.mem_union_left _ h)`. Establish `hD'v : D' v = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))`. Establish `hU : Unimod v (g v)` using `by simpa [B] using hvB`. Apply `val_mulVec_le_one v _ hU.1` to reduce the goal to its premises. Introduce `i`. Use `hpb i` as an intermediate fact.

Rewrite `this` using `[hD'v]`. Simplify using `using this`.
-/
theorem exists_section_of_large_deg : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.riemann_inequality_cofinal_functionField k F hFF
  refine ⟨γ, fun n g hg hdeg => ?_⟩
  classical
  set B := hg.2.toFinset with hBdef
  choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹
  let D : Place k F →₀ ℤ := Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0)
    (by intro v hv; by_contra h; exact hv (if_neg h))
  obtain ⟨D', hDD', m, f, hf, hm, hford⟩ := hγ D
  have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans
    (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)
  have hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)),
      (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 →
        ∀ i, v.1 ((g v).mulVec p i) ≤ 1 := by
    intro v
    refine GlobalTheory.T.functionFieldPlace_localIndex_scaled_uniformiser k F hFF v n (g v) _ (hg.1 v) ?_
    intro i j
    by_cases hv : v ∈ B
    · have hDv : D v = d0 v := by simp [D, Finsupp.onFinset_apply, hv]
      calc v.1 ((g v)⁻¹ i j) ≤ WithZero.exp (d0 v : ℤ) := hd0 v i j
        _ ≤ _ := by
          rw [WithZero.exp_le_exp]; have := hDD' v; rw [hDv] at this; omega
    · have hU : Unimod v (g v) := by simpa [B] using hv
      have hU' := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2
      calc v.1 ((g v)⁻¹ i j) ≤ 1 := hU'.1 i j
        _ = WithZero.exp 0 := rfl
        _ ≤ _ := by rw [WithZero.exp_le_exp]; omega
  choose N φ hN hφ using hloc
  set S := B ∪ D'.support with hS
  have hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v := by
    unfold Finsupp.sum
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv; simpa using hv
  have hdegS : deg g = ∑ v ∈ S, ord v (g v).det := by
    unfold deg
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.coe_union]; left
    simp only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hU; apply hv
    simp [ord, hU.2]
  have hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m := by
    push_cast
    rw [Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v := fun v => Int.toNat_of_nonneg (hD0 v)
    simp_rw [this]
    rw [← hsumD, ← hdegS]
    have := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)
    nlinarith
  obtain ⟨c, hp0, hpψ⟩ := GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)
  refine ⟨_, hp0, fun v i => ?_⟩
  have hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ) := fun i =>
    val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega)
      (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))
  by_cases hv : v ∈ S
  · exact hφ v _ hpb (hpψ v hv) i
  · have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have hD'v : D' v = 0 := by
      by_contra h; exact hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))
    have hU : Unimod v (g v) := by simpa [B] using hvB
    apply val_mulVec_le_one v _ hU.1
    intro i; have := hpb i; rw [hD'v] at this; simpa using this

end GlobalTheory.Nef
