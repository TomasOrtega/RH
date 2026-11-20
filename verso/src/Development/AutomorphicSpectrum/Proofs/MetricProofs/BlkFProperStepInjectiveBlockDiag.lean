import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

/- English proof (translation)
Unfold `blkF`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem blkF_eq_none_iff (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2 := by
  unfold blkF
  split_ifs with h <;> simp [h]

/- English proof (translation)
Introduce and unpack `⟨τ, i⟩ ⟨τ', i'⟩ h`. Establish `hi` using `i.2`. Establish `hi'` using `i'.2`. Apply the tactic sequence `by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p`. Simplify using `only [stepOf, dif_pos h₁, dif_pos h₂] at h`.

Establish `e₁ : τ = τ'` using `Sum.inl.inj (congrArg Sigma.fst h)`. Establish `e₂` using `congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h`. Conclude with `Prod.ext e₁ (Fin.ext e₂)`. Simplify using `only [stepOf, dif_pos h₁, dif_neg h₂] at h`. Conclude with `absurd (congrArg Sigma.fst h) (by simp)`.

Simplify using `only [stepOf, dif_neg h₁, dif_pos h₂] at h`. Conclude with `absurd (congrArg Sigma.fst h) (by simp)`. Simplify using `only [stepOf, dif_neg h₁, dif_neg h₂] at h`. Establish `e₁ : τ = τ'` using `Sum.inr.inj (congrArg Sigma.fst h)`. Establish `e₂ : (i : ℕ) - p = (i' : ℕ) - p` using `congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h`.

Conclude with `Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))`.
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
Unfold `blkF at h h'`. Use `split_ifs at h h'`. Apply `stepOf_injective Ψ p q` to reduce the goal to its premises. Establish `e` using `(Option.some.inj h).trans (Option.some.inj h').symm`. Conclude with `Sum.inr.inj e`.
-/
theorem blkF_inj (Ψ : Type) (p q : ℕ) (K₀ : Type) (r r' : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q)
    (h : blkF Ψ p q K₀ r = some k) (h' : blkF Ψ p q K₀ r' = some k) : r = r' := by
  unfold blkF at h h'
  split_ifs at h h'
  apply stepOf_injective Ψ p q
  have e := (Option.some.inj h).trans (Option.some.inj h').symm
  exact Sum.inr.inj e

/- English proof (translation)
Introduce `a b hab`. Take `⟨x, rfl⟩` from `(blockEquiv p q).surjective a`. Take `⟨y, rfl⟩` from `(blockEquiv p q).surjective b`. Simplify using `only [Matrix.submatrix_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`.

It suffices to derive a contradiction. Apply `hab` to reduce the goal to its premises. Establish `hx` using `x.2`. Establish `hy` using `y.2`. Use `show ((x : ℕ) < _ ↔ (y : ℕ) < _)`.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `hab` to reduce the goal to its premises.

Use `show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)`. Use linear arithmetic over natural numbers and integers.
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
The claim follows from `fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))`.
-/
theorem gMat_isBlockDiag (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) :
    IsBlockDiag p (gMat p q Ω τ) :=
  fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))

/- English proof (translation)
Introduce `Ψ _ p q Ω _ K₀` and use `⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩`.
-/
theorem blocks_main : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
    (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
    (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧
    ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) :=
  fun Ψ _ p q Ω _ K₀ => ⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks
