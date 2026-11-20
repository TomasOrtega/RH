import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairIterPhiMir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult
  GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h : dpowM (k` using `k) n (-(m : ℝ) / 2) * dpowM n (-(m : ℝ) / 2) * dpowM n (m : ℝ) = 1 := by`. Rewrite using `[← DerivTw.dpowM_add, ← DerivTw.dpowM_add, show (m : ℝ) + (-(m : ℝ) / 2 + -(m : ℝ) / 2) = 0 by ring, DerivTw.dpowM_zero]`. Establish `h2` using `congrArg (fun f : Mir k n →* ℂˣ => ((f p : ℂˣ) : ℂ)) h`. Simplify using `only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one] at h2`. Establish `h3 : ((dpowM n (m : ℝ) p : ℂˣ) : ℂ) = ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ)` using `by show ((detChar (Fin (n + 1)) (absPow k (((m : ℝ)) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = _`.

Rewrite using `[Complex.ofReal_natCast]`. Rewrite using `[← h3]`. Conclude with `h2`.
-/
theorem dpowM_half_cancel {n : ℕ} (m : ℕ) (p : Mir k n) :
    ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) * ((dpowM n (-(m : ℝ) / 2) p : ℂˣ) : ℂ) *
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = 1 := by
  have h : dpowM (k := k) n (-(m : ℝ) / 2) * dpowM n (-(m : ℝ) / 2) * dpowM n (m : ℝ) = 1 := by
    rw [← DerivTw.dpowM_add, ← DerivTw.dpowM_add,
      show (m : ℝ) + (-(m : ℝ) / 2 + -(m : ℝ) / 2) = 0 by ring, DerivTw.dpowM_zero]
  have h2 := congrArg (fun f : Mir k n →* ℂˣ => ((f p : ℂˣ) : ℂ)) h
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one] at h2
  have h3 : ((dpowM n (m : ℝ) p : ℂˣ) : ℂ) =
      ((detChar (Fin (n + 1)) (absPow k (m : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) := by
    show ((detChar (Fin (n + 1)) (absPow k (((m : ℝ)) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) = _
    rw [Complex.ofReal_natCast]
  rw [← h3]
  exact h2

/- English proof (translation)
Take `⟨B₀, hB₀, hn₀⟩` from `GlobalTheory.CompanionTheory.BZPairDescend.pair_iterPhi ψ hc h1 m m π.ρ π'.ρ hs hs' B hB hn`. Take `⟨e⟩ : MIso (iterN ψ m (gres π)) (mtw (iterPhi k ψ m (resM k π.ρ)) (-(m : ℝ) / 2))` from `DerivTw.iterN_iso ψ m (gres π)`. Take `⟨e'⟩ : MIso (iterN ψ⁻¹ m (gres π')) (mtw (iterPhi k ψ⁻¹ m (resM k π'.ρ)) (-(m : ℝ) / 2))` from `DerivTw.iterN_iso ψ⁻¹ m (gres π')`. Set `f : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (iterPhi k ψ m (resM k π.ρ)).V` to `e.toLinearEquiv`. Set `f' : (iterN ψ⁻¹ m (gres π')).V ≃ₗ[ℂ] (iterPhi k ψ⁻¹ m (resM k π'.ρ)).V` to `e'.toLinearEquiv`.

Establish `hf : ∀ p v, f ((iterN ψ m (gres π)).ρ p v) = ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ m (resM k π.ρ)).ρ p (f v)` using `fun p v => eint e p v`. Establish `hf' : ∀ p v, f' ((iterN ψ⁻¹ m (gres π')).ρ p v) = ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ⁻¹ m (resM k π'.ρ)).ρ p (f' v)` using `fun p v => eint e' p v`. Use `⟨(B₀.compl₁₂ f.toLinearMap f'.toLinearMap), fun p v v' => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]`. Rewrite using `[hf, hf', map_smul, map_smul, LinearMap.smul_apply, hB₀, smul_eq_mul, smul_eq_mul]`.

Take the linear combination `(B₀ (f v) (f' v')) * dpowM_half_cancel (k := k) m p`. Take `⟨w', hw'⟩` from `hn₀ (f v) (by simpa using hv)`. Use `⟨f'.symm w', ?_⟩` and prove the remaining obligations. Simplify using `using hw'`.
-/
theorem pair_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (π π' : GRep k (((m + 1) + m) + 1))
    (hs : IsSmooth π.ρ) (hs' : IsSmooth π'.ρ) (B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π.ρ g v) (π'.ρ g v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) :
    ∃ B' : (iterN ψ m (gres π)).V →ₗ[ℂ] (iterN ψ⁻¹ m (gres π')).V →ₗ[ℂ] ℂ,
      (∀ p v v', B' ((iterN ψ m (gres π)).ρ p v) ((iterN ψ⁻¹ m (gres π')).ρ p v') = B' v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B' v v' ≠ 0 := by
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.CompanionTheory.BZPairDescend.pair_iterPhi ψ hc h1 m m π.ρ π'.ρ hs hs' B hB hn
  obtain ⟨e⟩ : MIso (iterN ψ m (gres π)) (mtw (iterPhi k ψ m (resM k π.ρ)) (-(m : ℝ) / 2)) := DerivTw.iterN_iso ψ m (gres π)
  obtain ⟨e'⟩ : MIso (iterN ψ⁻¹ m (gres π')) (mtw (iterPhi k ψ⁻¹ m (resM k π'.ρ)) (-(m : ℝ) / 2)) :=
    DerivTw.iterN_iso ψ⁻¹ m (gres π')
  let f : (iterN ψ m (gres π)).V ≃ₗ[ℂ] (iterPhi k ψ m (resM k π.ρ)).V := e.toLinearEquiv
  let f' : (iterN ψ⁻¹ m (gres π')).V ≃ₗ[ℂ] (iterPhi k ψ⁻¹ m (resM k π'.ρ)).V := e'.toLinearEquiv
  have hf : ∀ p v, f ((iterN ψ m (gres π)).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ m (resM k π.ρ)).ρ p (f v) := fun p v => eint e p v
  have hf' : ∀ p v, f' ((iterN ψ⁻¹ m (gres π')).ρ p v) =
      ((dpowM (m + 1) (-(m : ℝ) / 2) p : ℂˣ) : ℂ) • (iterPhi k ψ⁻¹ m (resM k π'.ρ)).ρ p (f' v) := fun p v => eint e' p v
  refine ⟨(B₀.compl₁₂ f.toLinearMap f'.toLinearMap), fun p v v' => ?_, fun v hv => ?_⟩
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hf, hf', map_smul, map_smul, LinearMap.smul_apply, hB₀, smul_eq_mul, smul_eq_mul]
    linear_combination (B₀ (f v) (f' v')) * dpowM_half_cancel (k := k) m p
  · obtain ⟨w', hw'⟩ := hn₀ (f v) (by simpa using hv)
    refine ⟨f'.symm w', ?_⟩
    simpa using hw'

end GlobalTheory.CompanionTheory.BZShell

end
