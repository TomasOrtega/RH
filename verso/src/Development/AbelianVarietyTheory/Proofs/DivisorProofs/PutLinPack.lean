import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

/- English proof (translation)
Introduce `R _ n o₁ o₂ p q`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X Y`. Use extensionality with `i j`. Simplify using `only [put, Matrix.of_apply, Matrix.add_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `X`. Use extensionality with `i j`. Simplify using `only [put, Matrix.of_apply, Matrix.neg_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Use extensionality with `i j`. Simplify using `only [put, Matrix.of_apply, Matrix.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `X`. Use extensionality with `i j`.

Simplify using `only [put, Matrix.of_apply, Matrix.transpose_apply]`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression. Conclude with `absurd ⟨h1.2, h1.1⟩ h2`. Conclude with `absurd ⟨h2.2, h2.1⟩ h1`.

Both sides reduce to the same expression. Use extensionality with `i j`. Simplify using `only [eye, put, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Use extensionality with `i j`.

Simplify using `only [eye, put, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | (exfalso; omega) | simp_all`. Introduce `X h`. Use extensionality with `i j`. Simplify using `only [put, Matrix.of_apply, Matrix.zero_apply]`.

Use `split_ifs with h1`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Introduce `X`.

Use extensionality with `i j`. Simplify using `only [put, Matrix.of_apply]`. Use `split_ifs with h1`. Simplify using the standard rewrite rules. It suffices to derive a contradiction.

Use linear arithmetic over natural numbers and integers.
-/
theorem put_lin_pack : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (∀ X Y : Matrix (Fin p) (Fin q) R, put n o₁ o₂ (X + Y) = put n o₁ o₂ X + put n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, put n o₁ o₂ (-X) = -put n o₁ o₂ X) ∧ put n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 0 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (put n o₁ o₂ X)ᵀ = put n o₂ o₁ Xᵀ) ∧ eye R n o₁ o₂ (p + q) = eye R n o₁ o₂ p + eye R n (o₁ + p) (o₂ + p) q ∧ eye R n 0 0 n = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → put n o₁ o₂ X = 0) ∧ (∀ X : Matrix (Fin n) (Fin n) R, put n 0 0 X = X) := by
  intro R _ n o₁ o₂ p q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y
    ext i j
    simp only [put, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  · intro X
    ext i j
    simp only [put, Matrix.of_apply, Matrix.neg_apply]
    split_ifs <;> simp
  · ext i j
    simp only [put, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp
  · intro X
    ext i j
    simp only [put, Matrix.of_apply, Matrix.transpose_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · rfl
  · ext i j
    simp only [eye, put, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · ext i j
    simp only [eye, put, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega | (exfalso; omega) | simp_all
  · intro X h
    ext i j
    simp only [put, Matrix.of_apply, Matrix.zero_apply]
    split_ifs with h1
    · exfalso; omega
    · rfl
  · intro X
    ext i j
    simp only [put, Matrix.of_apply]
    split_ifs with h1
    · simp
    · exfalso; omega

end GlobalTheory.GamMul
