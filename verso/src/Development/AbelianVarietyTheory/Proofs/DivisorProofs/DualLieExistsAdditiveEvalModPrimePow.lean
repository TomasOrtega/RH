import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditiveStatement

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

/- English proof (translation)
Introduce `p O _ G l n`. Set `I : Ideal O` to `Ideal.span {(p : O) ^ n}`. Set `N : Submodule O G.dual.omega` to `Ideal.span {(p : O)} ^ n • ⊤`. Set `m : G.dual.omega →ₗ[O] O ⧸ I` to `(Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l`. Establish `hN : N ≤ LinearMap.ker m`.

Introduce `x hx`. Establish `hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega)` using `hx`. Rewrite `hx'` using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨v, -, rfl⟩` from `hx'`. Rewrite using `[LinearMap.mem_ker]`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0`. Rewrite using `[map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`. Set `u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I` to `N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap`. Establish `hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w)`.

Introduce `w`. Establish `h` using `(G.dual.omegaQuotEquiv_mk n w)`. Express the relevant statement in the definitionally equal form `N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _`. Rewrite using `[← h, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Take `⟨b, z, hb, hφ⟩` from `GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u`. Use `⟨b, z, hb, fun w φ hφw => ?_⟩` and prove the remaining obligations. Establish `h1` using `hφ φ`. Rewrite `h1` using `[hφw, hu, Ideal.Quotient.eq]`. Conclude with `Ideal.mem_span_singleton.1 h1`.
-/
theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
