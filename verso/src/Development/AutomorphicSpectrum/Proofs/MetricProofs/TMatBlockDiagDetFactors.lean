import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem tMat_blockEquiv (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (a b : Fin q ⊕ Fin p) :
    tMat Ts τ (blockEquiv p q a) (blockEquiv p q b) =
      (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ)) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) Ω) a b := by
  simp [tMat]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem omBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    omBlock (tMat Ts τ) = Ts (.inr τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inl a) (.inl b)

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem wBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    wBlock (tMat Ts τ) = Ts (.inl τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inr a) (.inr b)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Establish an intermediate fact. Both sides reduce to the same expression. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem isBlockDiag_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rw [tMat_blockEquiv]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd (by
      have h1 := a.2
      have h2 := b.2
      show ((a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p)
      omega) hab
  · rfl
  · rfl
  · exact absurd (by
      show (q + (a : ℕ) < p + q - p ↔ q + (b : ℕ) < p + q - p)
      omega) hab

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem tMat_main {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) ∧ (tMat Ts τ).det = (Ts (.inr τ)).det * (Ts (.inl τ)).det ∧
      ∀ i : Fin (p + q), detFac p i (tMat Ts τ) =
        (if p ≤ (i : ℕ) + 1 then (Ts (.inl τ)).det else 1) * (if (i : ℕ) + 1 = p + q then (Ts (.inr τ)).det else 1) := by
  refine ⟨isBlockDiag_tMat Ts τ, ?_, fun i => ?_⟩
  · have h := (isBlockDiag_tMat Ts τ).det_eq_blocks
    rw [omBlock_tMat, wBlock_tMat] at h
    exact h
  · have h1 : minorIJ (tMat Ts τ) (wIdx (p + q) p) (wIdx (p + q) p) = (Ts (.inl τ)).det := by
      rw [minorIJ_wIdx, wBlock_tMat]
      rfl
    have h2 : minorIJ (tMat Ts τ) (omIdx (p + q) p) (omIdx (p + q) p) = (Ts (.inr τ)).det := by
      rw [minorIJ_omIdx, omBlock_tMat]
      rfl
    rw [detFac, h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
