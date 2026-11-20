import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCap

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hw l j)) (hc i l)`.
-/
theorem val_mul_lt_left {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (c : Matrix X Y k)
    (w : Matrix Y Z k) (hc : ∀ i j, valuation k (c i j) < 1) (hw : ∀ i j, valuation k (w i j) ≤ 1) :
    ∀ i j, valuation k ((c * w) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (hw l j)) (hc i l)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hw i l)) (hc l j)`.
-/
theorem val_mul_lt_right {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (w : Matrix X Y k)
    (c : Matrix Y Z k) (hw : ∀ i j, valuation k (w i j) ≤ 1) (hc : ∀ i j, valuation k (c i j) < 1) :
    ∀ i j, valuation k ((w * c) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hw i l)) (hc l j)

/- English proof (translation)
Rewrite using `[← fromBlocks_toBlocks P, ← fromBlocks_toBlocks E, ← fromBlocks_toBlocks Q, hP, hE, hQ]`. Simplify using `[fromBlocks_multiply]`.
-/
theorem toBlocks₂₁_mul_mul {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (P E Q : Matrix (A ⊕ D) (A ⊕ D) k) (hP : P.toBlocks₂₁ = 0) (hE : E.toBlocks₂₁ = 0)
    (hQ : Q.toBlocks₂₁ = 0) : (P * E * Q).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks E, ← fromBlocks_toBlocks Q, hP, hE, hQ]
  simp [fromBlocks_multiply]

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks M]`. Simplify using `[fromBlocks_multiply]`.
-/
theorem lowUni_mul_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (fromBlocks 1 0 X 1 * M).toBlocks₂₁ = X * M.toBlocks₁₁ + M.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks M]`. Simplify using `[fromBlocks_multiply]`.
-/
theorem mul_lowUni_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (M * fromBlocks 1 0 X 1).toBlocks₂₁ = M.toBlocks₂₁ + M.toBlocks₂₂ * X := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ g ν m hg ⟨x, y, j, hj, j', hj', he⟩`. Take `⟨⟨u, hu, hua⟩, -, hc, -⟩` from `(GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j.1).1 ⟨j, hj, rfl⟩`. Take `⟨-, -, hc', ⟨u', hu', hud⟩⟩` from `(GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j'.1).1 ⟨j', hj', rfl⟩`. Establish `hui` using `((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u⁻¹).1).1 ⟨u⁻¹, inv_mem hu, rfl⟩).1`. Establish `hui'` using `((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u'⁻¹).1).1 ⟨u'⁻¹, inv_mem hu', rfl⟩).1`.

Use `set ν₁ := j.1.toBlocks₂₁ * (u⁻¹).1`. Use `set ν₂ := (u'⁻¹).1 * j'.1.toBlocks₂₁`. Use `⟨ν₁, ν₂, val_mul_lt_left _ _ hc hui, val_mul_lt_right _ _ hui' hc', ?_⟩` and prove the remaining obligations. Establish `hP : (fromBlocks 1 0 (-ν₁) 1 * j.1).toBlocks₂₁ = 0`. Establish `e1 : ν₁ * u.1 = j.1.toBlocks₂₁` using `by simp only [ν₁, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Rewrite using `[lowUni_mul_toBlocks₂₁, ← hua, Matrix.neg_mul, e1, neg_add_cancel]`. Establish `hQ : (j'.1 * fromBlocks 1 0 (-ν₂) 1).toBlocks₂₁ = 0`. Establish `e2 : u'.1 * ν₂ = j'.1.toBlocks₂₁` using `by simp only [ν₂, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Rewrite using `[mul_lowUni_toBlocks₂₁, ← hud, Matrix.mul_neg, e2, add_neg_cancel]`. Establish `hE : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1.toBlocks₂₁ = 0`.

Rewrite using `[val_emb₂]`. Simplify using the standard rewrite rules. Establish `key` using `toBlocks₂₁_mul_mul _ _ _ hP hE hQ`. Establish `h2 : fromBlocks 1 0 (-ν₁) 1 * j.1 * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1 * (j'.1 * fromBlocks 1 0 (-ν₂) 1) = fromBlocks 1 0 (-ν₁) 1 * g.1 * fromBlocks 1 0 (-ν₂) 1`. Rewrite using `[he]`.

Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite `key` using `[h2, hg]`. Simplify using `[fromBlocks_multiply] at key`. Rewrite using `[← sub_eq_zero, ← key]`. Normalize the expressions using the abelian group laws.
-/
theorem lowerUni_mem_cap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (ν : Matrix D A k)
    (m : GL D k), g.1 = fromBlocks 1 0 ν m.1 →
    (∃ x y, ∃ j ∈ parahoric k A D, ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j') →
    ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
      ν = ν₁ + m.1 * ν₂ := by
  intro k _ _ _ _ A D _ _ _ _ g ν m hg ⟨x, y, j, hj, j', hj', he⟩
  obtain ⟨⟨u, hu, hua⟩, -, hc, -⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j.1).1 ⟨j, hj, rfl⟩
  obtain ⟨-, -, hc', ⟨u', hu', hud⟩⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j'.1).1 ⟨j', hj', rfl⟩
  have hui := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u⁻¹).1).1 ⟨u⁻¹, inv_mem hu, rfl⟩).1
  have hui' := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u'⁻¹).1).1 ⟨u'⁻¹, inv_mem hu', rfl⟩).1
  set ν₁ := j.1.toBlocks₂₁ * (u⁻¹).1
  set ν₂ := (u'⁻¹).1 * j'.1.toBlocks₂₁
  refine ⟨ν₁, ν₂, val_mul_lt_left _ _ hc hui, val_mul_lt_right _ _ hui' hc', ?_⟩
  have hP : (fromBlocks 1 0 (-ν₁) 1 * j.1).toBlocks₂₁ = 0 := by
    have e1 : ν₁ * u.1 = j.1.toBlocks₂₁ := by simp only [ν₁, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [lowUni_mul_toBlocks₂₁, ← hua, Matrix.neg_mul, e1, neg_add_cancel]
  have hQ : (j'.1 * fromBlocks 1 0 (-ν₂) 1).toBlocks₂₁ = 0 := by
    have e2 : u'.1 * ν₂ = j'.1.toBlocks₂₁ := by simp only [ν₂, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_lowUni_toBlocks₂₁, ← hud, Matrix.mul_neg, e2, add_neg_cancel]
  have hE : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1.toBlocks₂₁ = 0 := by
    rw [val_emb₂]
    simp
  have key := toBlocks₂₁_mul_mul _ _ _ hP hE hQ
  have h2 : fromBlocks 1 0 (-ν₁) 1 * j.1 * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1 *
      (j'.1 * fromBlocks 1 0 (-ν₂) 1) = fromBlocks 1 0 (-ν₁) 1 * g.1 * fromBlocks 1 0 (-ν₂) 1 := by
    rw [he]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, hg] at key
  simp [fromBlocks_multiply] at key
  rw [← sub_eq_zero, ← key]
  abel

end GlobalTheory.ParHeckeCap
