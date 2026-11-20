import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.GlueBlocks

/- English proof (translation)
Set `A' : Matrix (Fin d) (Fin d) (PTb.intRing v)` to `Matrix.of fun a b => ⟨X a b, hX a b⟩`. Establish `hA : (PTb.intRing v).subtype.mapMatrix A' = X` using `by ext a b; rfl`. Establish `: X.det = (PTb.intRing v).subtype A'.det`. Rewrite using `[RingHom.map_det, hA]`. Rewrite using `[this]`.

Conclude with `(A'.det).2`.
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
Introduce `C _ v d ι lab S x y hlab hx hy hxi hyi hinv`. Establish `hint : ∀ z : ι → Matrix (Fin d) (Fin d) C, (∀ i a b, IsIntV v (z i a b)) → ∀ a b, IsIntV v (glue lab S z a b)`. Introduce `z hz a b`. Simplify using `only [glue, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `hz _ _ _`. Unfold `IsIntV`. Rewrite using `[v.map_one]`. Unfold `IsIntV`. Rewrite using `[v.map_zero]`.

Conclude with `le_top`. Establish `hmul : glue lab S x * glue lab S y = 1`. Use extensionality with `a c`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Distinguish the cases in `ha : a ∈ S (lab a)`.

Establish `hterm : ∀ b, glue lab S x a b * glue lab S y b c = x (lab a) a b * y (lab a) b c`. Introduce `b`. Simplify using `only [glue, Matrix.of_apply, if_pos ha]`. Distinguish the cases in `hxb : x (lab a) a b = 0`. Rewrite using `[hxb, zero_mul, zero_mul]`.

Establish `hb` using `(hx _ _ _ hxb).2`. Establish `hl : lab b = lab a` using `hlab _ _ hb`. Rewrite using `[if_pos (hl ▸ hb), hl]`. Repeatedly rewrite using `[hterm]`. Distinguish the cases in `hc : c ∈ S (lab a)`.

Conclude with `hinv _ _ _ ha hc`. Establish `h0 : ∀ b, y (lab a) b c = 0`. Introduce `b`. Assume the negation of the conclusion as `hne`. Conclude with `hc (hy _ _ _ hne).2`.

Simplify using `only [h0, mul_zero, Finset.sum_const_zero]`. Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hc ha`. Establish `hterm : ∀ b, glue lab S x a b * glue lab S y b c = if a = b then glue lab S y b c else 0`.

Introduce `b`. Simplify using `only [glue, Matrix.of_apply, if_neg ha]`. Apply the tactic sequence `split_ifs <;> simp`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_ite_eq Finset.univ a (fun b => glue lab S y b c), if_pos (Finset.mem_univ _)]`.

Simplify using `only [glue, Matrix.of_apply, if_neg ha]`. Use `⟨hint x hxi, hmul, ?_⟩` and prove the remaining obligations. Establish `hd : (glue lab S x).det * (glue lab S y).det = 1`. Rewrite using `[← Matrix.det_mul, hmul, Matrix.det_one]`. Establish `h1 : v (glue lab S x).det + v (glue lab S y).det = 0`.

Rewrite using `[← v.map_mul, hd, v.map_one]`. Establish `hX : (0 : WithTop ℝ) ≤ v (glue lab S x).det` using `isIntV_det v _ (hint x hxi)`. Establish `hY : (0 : WithTop ℝ) ≤ v (glue lab S y).det` using `isIntV_det v _ (hint y hyi)`. Conclude with `((add_eq_zero_iff_of_nonneg hX hY).1 h1).1`.
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
