import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/- English proof (translation)
Use `ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_add]`. Conclude with `le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl`.
-/
theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

/- English proof (translation)
Establish `key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤`. Introduce and unpack `r ⟨S, T, h1, h2, h3⟩`. Establish `hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero`. Introduce `hi`. Use `hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)` as an intermediate fact. Simplify using `using le_trans le_add_self this`. Consider the case `succ i ih`.

Introduce `hi`. Establish `h4` using `ih (by omega)`. Establish `h5` using `hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))`. Establish `h6` using `hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)`. Use `le_trans ?_ h6` and prove the remaining obligations.

Establish `: (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `add_le_add (h4.trans h5) le_rfl`. Break down `r with _ | r` into its components or cases. Simplify using the standard rewrite rules.

Conclude with `(hi r (by omega)).trans (hmono _ _ le_top)`. Unfold `jhMult`. Rewrite using `[ENat.iSup_mul]`. Use `iSup_le fun r => ?_` and prove the remaining obligations. Rewrite using `[ENat.iSup_mul]`.

Conclude with `iSup_le fun hr => key r hr`.
-/
theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
