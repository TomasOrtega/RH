import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelMain

noncomputable section
open Matrix

namespace PI.SqPair.LCP

/- English proof (translation)
Introduce `R _ _ R₀ ϖ hI ι _ _ A A' h k hP hNB`. Use `hI.dom` as an intermediate fact. Take `⟨⟨_, hA⟩, ⟨_, hA'⟩, hrel⟩` from `hP`. Establish `hne : Nonempty ι`. Assume the negation of the conclusion as `hne`.

Rewrite `hne` using `[not_nonempty_iff]`. Conclude with `hNB ⟨1, by simp, by ext i; exact (IsEmpty.false i).elim⟩`. Set `σ : R ≃+* R` to `starRingAut`. Establish `hct : ∀ M : Matrix ι ι R, (M.map σ)ᵀ = Mᴴ`. Introduce `M`.

Use extensionality with `i j`. Simplify using `[σ, Matrix.conjTranspose_apply]`. Establish `hs : ∀ x : ι → R, star x = fun l => σ (x l)`. Introduce `x`. Use extensionality with `l`.

Simplify using `[σ]`. Establish `hσϖ : σ ϖ = ϖ` using `by simpa [σ] using (hI.fix ϖ).mp hI.pi_mem`. Establish `hrel' : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A'` using `by rw [hct]; exact hrel`. Take `⟨m, h₁, rfl, hle, _, hcase⟩` from `sel_main σ ϖ hI.pi_ne hI.pi_nonunit hσϖ hI.val A A' h hA hA' k hrel'`. Break down `hcase with ⟨hmk, hu⟩ | ⟨hlt, g₁, j, y, _, _, _, hxy, hxx, hy⟩` into its components or cases.

Conclude with `absurd ⟨h₁, hu, by rw [hmk]⟩ hNB`. Use `⟨k - m, h₁ *ᵥ Pi.single j 1, y, by omega, by omega, ?_, ⟨A' j j, ?_⟩, ⟨Pi.single j 1, ?_⟩, ⟨g₁ *ᵥ y, ?_⟩⟩` and prove the remaining obligations. Unfold `hf`. Rewrite using `[hs]`. Conclude with `hxy`.

Unfold `hf`. Rewrite using `[hs]`. Conclude with `hxx`. Rewrite using `[Matrix.smul_mulVec, show k - (k - m) = m by omega]`. Rewrite using `[Matrix.smul_mulVec, ← hy, smul_smul, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
theorem pair_selection : Select := by
  intro R _ _ R₀ ϖ hI ι _ _ A A' h k hP hNB
  have := hI.dom
  obtain ⟨⟨_, hA⟩, ⟨_, hA'⟩, hrel⟩ := hP
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hNB ⟨1, by simp, by ext i; exact (IsEmpty.false i).elim⟩
  let σ : R ≃+* R := starRingAut
  have hct : ∀ M : Matrix ι ι R, (M.map σ)ᵀ = Mᴴ := by
    intro M; ext i j; simp [σ, Matrix.conjTranspose_apply]
  have hs : ∀ x : ι → R, star x = fun l => σ (x l) := by
    intro x; ext l; simp [σ]
  have hσϖ : σ ϖ = ϖ := by simpa [σ] using (hI.fix ϖ).mp hI.pi_mem
  have hrel' : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A' := by rw [hct]; exact hrel
  obtain ⟨m, h₁, rfl, hle, _, hcase⟩ :=
    sel_main σ ϖ hI.pi_ne hI.pi_nonunit hσϖ hI.val A A' h hA hA' k hrel'
  rcases hcase with ⟨hmk, hu⟩ | ⟨hlt, g₁, j, y, _, _, _, hxy, hxx, hy⟩
  · exact absurd ⟨h₁, hu, by rw [hmk]⟩ hNB
  · refine ⟨k - m, h₁ *ᵥ Pi.single j 1, y, by omega, by omega, ?_, ⟨A' j j, ?_⟩,
      ⟨Pi.single j 1, ?_⟩, ⟨g₁ *ᵥ y, ?_⟩⟩
    · unfold hf; rw [hs]; exact hxy
    · unfold hf; rw [hs]; exact hxx
    · rw [Matrix.smul_mulVec, show k - (k - m) = m by omega]
    · rw [Matrix.smul_mulVec, ← hy, smul_smul, ← pow_add]
      congr 2
      omega

end PI.SqPair.LCP
