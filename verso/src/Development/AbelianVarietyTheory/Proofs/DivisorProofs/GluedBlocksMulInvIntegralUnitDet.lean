import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.GlueBlocks

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isIntV_det {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {d : ℕ}
    (X : Matrix (Fin d) (Fin d) C) (hX : ∀ a b, IsIntV v (X a b)) : IsIntV v X.det := by
  let A' : Matrix (Fin d) (Fin d) (PTb.intRing v) := Matrix.of fun a b => ⟨X a b, hX a b⟩
  have hA : (PTb.intRing v).subtype.mapMatrix A' = X := by ext a b; rfl
  have : X.det = (PTb.intRing v).subtype A'.det := by
    rw [RingHom.map_det, hA]
  rw [this]
  exact (A'.det).2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem glue_mul_glue_inv : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  intro C _ v d ι lab S x y hlab hx hy hxi hyi hinv
  have hint : ∀ z : ι → Matrix (Fin d) (Fin d) C, (∀ i a b, IsIntV v (z i a b)) →
      ∀ a b, IsIntV v (glue lab S z a b) := by
    intro z hz a b
    simp only [glue, Matrix.of_apply]
    split_ifs
    · exact hz _ _ _
    · unfold IsIntV; rw [v.map_one]
    · unfold IsIntV; rw [v.map_zero]; exact le_top
  have hmul : glue lab S x * glue lab S y = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases ha : a ∈ S (lab a)
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c = x (lab a) a b * y (lab a) b c := by
        intro b
        simp only [glue, Matrix.of_apply, if_pos ha]
        by_cases hxb : x (lab a) a b = 0
        · rw [hxb, zero_mul, zero_mul]
        · have hb := (hx _ _ _ hxb).2
          have hl : lab b = lab a := hlab _ _ hb
          rw [if_pos (hl ▸ hb), hl]
      simp_rw [hterm]
      by_cases hc : c ∈ S (lab a)
      · exact hinv _ _ _ ha hc
      · have h0 : ∀ b, y (lab a) b c = 0 := by
          intro b; by_contra hne; exact hc (hy _ _ _ hne).2
        simp only [h0, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl; exact hc ha
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c =
          if a = b then glue lab S y b c else 0 := by
        intro b
        simp only [glue, Matrix.of_apply, if_neg ha]
        split_ifs <;> simp
      simp_rw [hterm]
      rw [Finset.sum_ite_eq Finset.univ a (fun b => glue lab S y b c), if_pos (Finset.mem_univ _)]
      simp only [glue, Matrix.of_apply, if_neg ha]
  refine ⟨hint x hxi, hmul, ?_⟩
  have hd : (glue lab S x).det * (glue lab S y).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have h1 : v (glue lab S x).det + v (glue lab S y).det = 0 := by
    rw [← v.map_mul, hd, v.map_one]
  have hX : (0 : WithTop ℝ) ≤ v (glue lab S x).det := isIntV_det v _ (hint x hxi)
  have hY : (0 : WithTop ℝ) ≤ v (glue lab S y).det := isIntV_det v _ (hint y hyi)
  exact ((add_eq_zero_iff_of_nonneg hX hY).1 h1).1

end GlobalTheory.GlueBlocks
