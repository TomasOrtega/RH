import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeShiftSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [IsScalarTower S Ω E] in

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Submodule.span_induction (p := fun y _ => x i ^ c • y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg c`.

Use `Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse, M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul]`. Use `congr 1`. Simplify using `only [map_pow, aeval_X, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Introduce `a y _ hy`. Establish `: x i ^ c • (a • y) = a • (x i ^ c • y)`. Rewrite using `[Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ a hy`.
-/
theorem FinGradedSub.zpow_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) {I : Chart x}
    {i : Fin (N + 1)} (hi : i ∈ I.1) (c d : ℤ) {y : E} (hy : y ∈ M.tilde d I) :
    x i ^ c • y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c • y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      rw [smul_smul, smul_smul]
      congr 1
      simp only [map_pow, aeval_X, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      rw [smul_smul]
      congr 1
      simp only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c • (a • y) = a • (x i ^ c • y) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ a hy

/- English proof (translation)
Introduce `S _ Ω _ _ N x E _ _ _ _ M c`. Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `y hy`. Establish `h0 : x i ^ (-c) • y ∈ M.tilde 0 I`. Simplify using `using M.zpow_smul_mem_tilde hi (-c) c hy`. Use `Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x i ^ c ∈ twistMod S x c I`.

Rewrite using `[twistMod_eq_span c I hi]`. Conclude with `Submodule.mem_span_singleton_self _`. Rewrite using `[smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`.

Express the relevant statement in the definitionally equal form `q ∈ twistMod S x c I at hq`. Rewrite `hq` using `[twistMod_eq_span c I hi, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hq`. Establish `hy' : x i ^ c • y ∈ M.tilde c I`. Simplify using `using M.zpow_smul_mem_tilde hi c 0 hy`.

Establish `: (a • x i ^ c) • y = a • (x i ^ c • y)`. Rewrite using `[chartRing_smul_def, Subalgebra.smul_def, smul_smul]`. Rewrite using `[SetLike.mem_coe, this]`. Conclude with `Submodule.smul_mem _ a hy'`.
-/
theorem TildeShift.proof : TildeShift.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ M c
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) • y ∈ M.tilde 0 I := by
      simpa using M.zpow_smul_mem_tilde hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c • y ∈ M.tilde c I := by
      simpa using M.zpow_smul_mem_tilde hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c • y) := by
      rw [chartRing_smul_def, Subalgebra.smul_def, smul_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

end

end GroundTheory.Heights₂.Heights.Kleiman
