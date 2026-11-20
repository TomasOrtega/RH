import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem blkF_eq_none_iff (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2 := by
  unfold blkF
  split_ifs with h <;> simp [h]

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem stepOf_injective (Ψ : Type) (p q : ℕ) : Function.Injective (stepOf Ψ p q) := by
  rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
  have hi := i.2
  have hi' := i'.2
  by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
  · simp only [stepOf, dif_pos h₁, dif_pos h₂] at h
    have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
    have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext e₂)
  · simp only [stepOf, dif_pos h₁, dif_neg h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dif_neg h₁, dif_pos h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dif_neg h₁, dif_neg h₂] at h
    have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
    have e₂ : (i : ℕ) - p = (i' : ℕ) - p := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem blkF_inj (Ψ : Type) (p q : ℕ) (K₀ : Type) (r r' : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q)
    (h : blkF Ψ p q K₀ r = some k) (h' : blkF Ψ p q K₀ r' = some k) : r = r' := by
  unfold blkF at h h'
  split_ifs at h h'
  apply stepOf_injective Ψ p q
  have e := (Option.some.inj h).trans (Option.some.inj h').symm
  exact Sum.inr.inj e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Both sides reduce to the same expression. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem fromBlocks_isBlockDiag {R : Type} [CommRing R] (p q : ℕ) (A : Matrix (Fin q) (Fin q) R)
    (B : Matrix (Fin p) (Fin p) R) :
    IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  · exfalso
    apply hab
    have hx := x.2
    have hy := y.2
    show ((x : ℕ) < _ ↔ (y : ℕ) < _)
    omega
  · rfl
  · rfl
  · exfalso
    apply hab
    show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
    omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gMat_isBlockDiag (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) :
    IsBlockDiag p (gMat p q Ω τ) :=
  fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem blocks_main : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
    (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
    (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧
    ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) :=
  fun Ψ _ p q Ω _ K₀ => ⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks
