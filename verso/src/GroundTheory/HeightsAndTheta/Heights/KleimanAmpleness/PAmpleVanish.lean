import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Establish `hA : x i ^ a ∈ twistMod S x (a : ℤ) I`. Rewrite using `[twistMod_eq_span _ I hi, zpow_natCast]`.

Conclude with `Submodule.mem_span_singleton_self _`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`.

Use `Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m, Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a), hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a), mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `q ∈ twistMod S x (a : ℤ) I at hq`.

Rewrite `hq` using `[twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton]`. Take `⟨β, rfl⟩` from `hq`. Establish `key : x i ^ a • y ∈ M.tilde (a : ℤ) I`. Use `Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩`.

Use `Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse, M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, map_pow, aeval_X, mul_comm]`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `y y' _ _ h h'`.

Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ h h'`. Introduce `c y _ h`. Rewrite using `[Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]`. Conclude with `Submodule.smul_mem _ c h`.

Rewrite using `[SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]`. Conclude with `Submodule.smul_mem _ β key`.
-/
theorem FinGradedSub.tildeSys_natCast_eq_twist (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hA : x i ^ a ∈ twistMod S x (a : ℤ) I := by
    rw [twistMod_eq_span _ I hi, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m,
      Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a),
        hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩
    rw [smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x (a : ℤ) I at hq
    rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at hq
    obtain ⟨β, rfl⟩ := hq
    have key : x i ^ a • y ∈ M.tilde (a : ℤ) I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
        refine Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse,
          M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩
        rw [smul_smul, smul_smul, map_pow, aeval_X, mul_comm]
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [smul_add]
        exact Submodule.add_mem _ h h'
      · intro c y _ h
        rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
        exact Submodule.smul_mem _ c h
    rw [SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ β key

end Tilde

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x E _ _ _ _ F hF H hH`. Take `⟨r, h, hh⟩` from `hH`. Take `⟨F', hF', hiso⟩` from `hC S Ω N x E F hF H r h hh`. Take `⟨M, -, hM⟩` from `hE S Ω r h E F' hF'`. Take `⟨c₀, hc₀⟩` from `hT S Ω r h E M`.

Use `⟨c₀.toNat, fun i a hi ha => ?_⟩` and prove the remaining obligations. Take `⟨e⟩` from `hiso a i`. Establish `hsys : F'.toSubSystem = M.tildeSys 0` using `SubSystem.ext_sub fun J => (hM J).symm`. Establish `hv` using `hc₀ i hi a (by omega)`. Rewrite `hv` using `[M.tildeSys_natCast_eq_twist a, ← hsys]`.

Conclude with `e.toEquiv.subsingleton`.
-/
theorem AmpleVanish.proof (hC : VeryAmpleCech.Statement.{u, v, w}) (hE : Extension.Statement.{u, v, w})
    (hT : TildeVanish.Statement.{u, v, w}) : AmpleVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H hH
  obtain ⟨r, h, hh⟩ := hH
  obtain ⟨F', hF', hiso⟩ := hC S Ω N x E F hF H r h hh
  obtain ⟨M, -, hM⟩ := hE S Ω r h E F' hF'
  obtain ⟨c₀, hc₀⟩ := hT S Ω r h E M
  refine ⟨c₀.toNat, fun i a hi ha => ?_⟩
  obtain ⟨e⟩ := hiso a i
  have hsys : F'.toSubSystem = M.tildeSys 0 := SubSystem.ext_sub fun J => (hM J).symm
  have hv := hc₀ i hi a (by omega)
  rw [M.tildeSys_natCast_eq_twist a, ← hsys] at hv
  exact e.toEquiv.subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
