import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_blockpos

/- English proof (translation)
Rewrite `hA`, `hB`, the goal using `[Matrix.posDef_iff_dotProduct_mulVec]`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1, hB.1]`. Simplify using the standard rewrite rules. Establish `e : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 B *ᵥ x) = star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr))`.

Rewrite using `[Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fintype.sum_sum_type]`. Rewrite using `[e]`. Establish `h1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))`. Distinguish the cases in `h : x ∘ Sum.inl = 0`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `(hA.2 h).le`. Establish `h2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr))`. Distinguish the cases in `h : x ∘ Sum.inr = 0`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `(hB.2 h).le`. Distinguish the cases in `h : x ∘ Sum.inl = 0`. Establish `h' : x ∘ Sum.inr ≠ 0` using `fun h' => hx (funext fun i => by`.

Break down `i with i | i` into its components or cases. Conclude with `congrFun h i`. Conclude with `congrFun h' i)`. Conclude with `add_pos_of_nonneg_of_pos h1 (hB.2 h')`. Conclude with `add_pos_of_pos_of_nonneg (hA.2 h) h2`.
-/
theorem posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1, hB.1]; simp
  · have e : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 B *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [e]
    have h1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
      by_cases h : x ∘ Sum.inl = 0
      · rw [h]; simp
      · exact (hA.2 h).le
    have h2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      by_cases h : x ∘ Sum.inr = 0
      · rw [h]; simp
      · exact (hB.2 h).le
    by_cases h : x ∘ Sum.inl = 0
    · have h' : x ∘ Sum.inr ≠ 0 := fun h' => hx (funext fun i => by
        rcases i with i | i
        · exact congrFun h i
        · exact congrFun h' i)
      exact add_pos_of_nonneg_of_pos h1 (hB.2 h')
    · exact add_pos_of_pos_of_nonneg (hA.2 h) h2

end PositivityTheory.Xgp.c_bm_exists_blockpos

/- English proof (translation)
Introduce `p q Γ h`. Use `⟨fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(blockEquiv p q).surjective a`. Take `⟨b, rfl⟩` from `(blockEquiv p q).surjective b`. Simplify using `only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]`.

Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab`. Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab`.

Use `Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective` and prove the remaining obligations. Conclude with `PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks (h.submatrix (omEmb_strictMono p q).injective).transpose.inv (h.submatrix (wEmb_strictMono p q).injective)`.
-/
theorem PositivityTheory.Xgp.t_c_bm_exists_blockpos : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  intro p q Γ h
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
    simp only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab
    · rfl
    · rfl
    · exact absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab
  · refine Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective
    exact PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks
      (h.submatrix (omEmb_strictMono p q).injective).transpose.inv
      (h.submatrix (wEmb_strictMono p q).injective)
