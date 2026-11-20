import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

open scoped TensorProduct
open GlobalTheory.TateLimit

/- English proof (translation)
Establish `hN0 : (N : ℤ_[l]) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h1` using `PadicInt.unitCoeff_spec hN0`. Establish `h2` using `PadicInt.appr_spec (N : ℤ_[l]).valuation a`. Rewrite `h2` using `[Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h2`.

Use `⟨(a.appr (N : ℤ_[l]).valuation : ℕ), ((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c, ?_⟩` and prove the remaining obligations. Establish `h3 : (N : ℤ_[l]) * (((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c) = (l : ℤ_[l]) ^ (N : ℤ_[l]).valuation * c`. Generalize the expression as in `PadicInt.unitCoeff hN0 = u at h1 ⊢`. Generalize the expression as in `(l : ℤ_[l]) ^ (N : ℤ_[l]).valuation = q at h1 ⊢`. Rewrite using `[h1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, ← hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.V.K.padic_int_eq_int_add_mul (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (N : ℕ) (hN : 0 < N) :
    ∃ (k : ℤ) (b : ℤ_[l]), a = (k : ℤ_[l]) + (N : ℤ_[l]) * b := by
  have hN0 : (N : ℤ_[l]) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 := PadicInt.unitCoeff_spec hN0
  have h2 := PadicInt.appr_spec (N : ℤ_[l]).valuation a
  rw [Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨(a.appr (N : ℤ_[l]).valuation : ℕ), ((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c, ?_⟩
  have h3 : (N : ℤ_[l]) * (((PadicInt.unitCoeff hN0)⁻¹ : ℤ_[l]ˣ) * c)
      = (l : ℤ_[l]) ^ (N : ℤ_[l]).valuation * c := by
    generalize PadicInt.unitCoeff hN0 = u at h1 ⊢
    generalize (l : ℤ_[l]) ^ (N : ℤ_[l]).valuation = q at h1 ⊢
    rw [h1]
    calc (u : ℤ_[l]) * q * (((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * c)
        = ((u : ℤ_[l]) * ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) * (q * c) := by ring
      _ = q * c := by rw [Units.mul_inv, one_mul]
  rw [h3, ← hc]
  push_cast
  ring

/- English proof (translation)
Introduce `l _ T _ hT x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨s, rfl⟩` from `hx`.

Take `⟨t, rfl⟩` from `hy`. Conclude with `⟨s + t, by simp [TensorProduct.tmul_add]⟩`. Consider the case `tmul a t`. Take `⟨N, hN, hNt⟩` from `isOfFinAddOrder_iff_nsmul_eq_zero.1 (hT t)`. Take `⟨k, b, rfl⟩` from `UpperTheory.V.K.padic_int_eq_int_add_mul l a N hN`.

Use `⟨k • t, ?_⟩` and prove the remaining obligations. Establish `e1 : ((N : ℤ_[l]) * b) ⊗ₜ[ℤ] t = (0 : ℤ_[l] ⊗[ℤ] T)`. Establish `: (N : ℤ_[l]) * b = (N : ℤ) • b` using `by simp`. Rewrite using `[this, TensorProduct.smul_tmul, natCast_zsmul, hNt, TensorProduct.tmul_zero]`. Establish `e2 : (k : ℤ_[l]) = k • (1 : ℤ_[l])` using `by simp`.

Use `show (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • t) = _`. Rewrite using `[TensorProduct.add_tmul, e1, add_zero, e2, TensorProduct.smul_tmul]`.
-/
theorem UpperTheory.V.K.tensSurj :
    ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T], AddMonoid.IsTorsion T → Function.Surjective (fun t : T => ((1 : ℤ_[l]) ⊗ₜ[ℤ] t : ℤ_[l] ⊗[ℤ] T)) := by
  intro l _ T _ hT x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, by simp [TensorProduct.tmul_add]⟩
  | tmul a t =>
    obtain ⟨N, hN, hNt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hT t)
    obtain ⟨k, b, rfl⟩ := UpperTheory.V.K.padic_int_eq_int_add_mul l a N hN
    refine ⟨k • t, ?_⟩
    have e1 : ((N : ℤ_[l]) * b) ⊗ₜ[ℤ] t = (0 : ℤ_[l] ⊗[ℤ] T) := by
      have : (N : ℤ_[l]) * b = (N : ℤ) • b := by simp
      rw [this, TensorProduct.smul_tmul, natCast_zsmul, hNt, TensorProduct.tmul_zero]
    have e2 : (k : ℤ_[l]) = k • (1 : ℤ_[l]) := by simp
    show (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • t) = _
    rw [TensorProduct.add_tmul, e1, add_zero, e2, TensorProduct.smul_tmul]
