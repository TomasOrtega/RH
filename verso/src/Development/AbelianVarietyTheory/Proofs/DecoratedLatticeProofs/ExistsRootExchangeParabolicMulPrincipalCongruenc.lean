import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ResidueLift

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def blockIx (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp only [blockIx, Sum.elim_inl, Sum.elim_inr] at h`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega` and prove the remaining obligations. Use `⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega` and prove the remaining obligations. Use `⟨?_, by simp, fun e => ?_⟩` and prove the remaining obligations.

Simplify using `only [lev, Sum.elim_inr]`. Use linear arithmetic over natural numbers and integers. Consider the cases of `e`. Use linear arithmetic over natural numbers and integers.
-/
theorem of_blockIx_lt {a b : n ⊕ Fin c} (h : blockIx p b < blockIx p a) :
    lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) ∧ a ≠ b := by
  rcases a with a | a <;> rcases b with b | b <;> simp only [blockIx, Sum.elim_inl, Sum.elim_inr] at h
  · omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, fun e => ?_⟩
    · simp only [lev, Sum.elim_inr]; omega
    · cases e; omega

/- English proof (translation)
Establish `hbt : r.val.BlockTriangular (blockIx p)` using `fun a b h => by`. Take `⟨h1, h2, h3⟩` from `of_blockIx_lt h`. Rewrite using `[hr a b h1 h2, one_apply_ne h3]`. Establish `hbt' : (r⁻¹).val.BlockTriangular (blockIx p)`. Rewrite using `[Matrix.coe_units_inv]`.

Conclude with `blockTriangular_inv_of_blockTriangular hbt`. Establish `hz : ∀ (x : n) (j : Fin c), j.val + 1 ≤ p → r.val (.inl x) (.inr j) = 0` using `fun x j hj => by`. Rewrite using `[hr _ _ (by simpa [lev] using hj) (by simp)]; simp`. Establish `hz' : ∀ (x : n) (j : Fin c), p ≤ j.val + 1 → (r⁻¹).val (.inr j) (.inl x) = 0` using `fun x j hj => hbt' (by simp only [blockIx, Sum.elim_inl, Sum.elim_inr]; omega)`. Establish `e1 : r.val.toBlocks₁₁ * (r⁻¹).val.toBlocks₁₁ = 1`.

Use `congrArg Matrix.toBlocks₁₁ (congrArg Units.val (mul_inv_cancel r))` as an intermediate fact. Rewrite `this` using `[Units.val_mul, mul_toBlocks₁₁, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]`. Rewrite using `[← this, left_eq_add]`. Use extensionality with `x x'`. Simplify using `only [mul_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `le_total (j.val + 1) p with hj | hj` into its components or cases. Rewrite using `[hz x j hj, zero_mul]`. Rewrite using `[hz' x' j hj, mul_zero]`. Set `γ : GL n k` to `⟨r.val.toBlocks₁₁, (r⁻¹).val.toBlocks₁₁, e1, mul_eq_one_comm.1 e1⟩`.

Establish `e2 : (γ⁻¹).val * r.val.toBlocks₁₁ = 1` using `Units.inv_mul γ`. Establish `hm : InN p ((embX c γ)⁻¹ * r)`. Introduce `a b hab`. Rewrite using `[← map_inv, Units.val_mul, show (embX c γ⁻¹).val = fromBlocks (γ⁻¹).val 0 0 1 from rfl]`. Break down `a with x | i` into its components or cases.

Break down `b with x' | j` into its components or cases. Use `congrFun (congrFun e2 x) x'` as an intermediate fact. Simplify `this` using `[mul_apply, Fintype.sum_sum_type, toBlocks₁₁, one_apply]`. Establish `hj : j.val + 1 ≤ p` using `by simpa [lev] using hab`. Simplify using `[mul_apply, Fintype.sum_sum_type, hz _ _ hj]`.

Use `hr (.inr i) b hab (by simp)` as an intermediate fact. Simplify `this` using `[mul_apply, Fintype.sum_sum_type, one_apply]`. Establish `: r = embX c γ * ((embX c γ)⁻¹ * r)` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hm))`.
-/
theorem mem_R_of_pattern (r : GL (n ⊕ Fin c) k)
    (hr : ∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
      r.val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b) :
    r ∈ R k n c p := by
  have hbt : r.val.BlockTriangular (blockIx p) := fun a b h => by
    obtain ⟨h1, h2, h3⟩ := of_blockIx_lt h
    rw [hr a b h1 h2, one_apply_ne h3]
  have hbt' : (r⁻¹).val.BlockTriangular (blockIx p) := by
    rw [Matrix.coe_units_inv]; exact blockTriangular_inv_of_blockTriangular hbt
  have hz : ∀ (x : n) (j : Fin c), j.val + 1 ≤ p → r.val (.inl x) (.inr j) = 0 := fun x j hj => by
    rw [hr _ _ (by simpa [lev] using hj) (by simp)]; simp
  have hz' : ∀ (x : n) (j : Fin c), p ≤ j.val + 1 → (r⁻¹).val (.inr j) (.inl x) = 0 := fun x j hj =>
    hbt' (by simp only [blockIx, Sum.elim_inl, Sum.elim_inr]; omega)
  have e1 : r.val.toBlocks₁₁ * (r⁻¹).val.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ (congrArg Units.val (mul_inv_cancel r))
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁] at this
    rw [← this, left_eq_add]
    ext x x'
    simp only [mul_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_total (j.val + 1) p with hj | hj
    · rw [hz x j hj, zero_mul]
    · rw [hz' x' j hj, mul_zero]
  let γ : GL n k := ⟨r.val.toBlocks₁₁, (r⁻¹).val.toBlocks₁₁, e1, mul_eq_one_comm.1 e1⟩
  have e2 : (γ⁻¹).val * r.val.toBlocks₁₁ = 1 := Units.inv_mul γ
  have hm : InN p ((embX c γ)⁻¹ * r) := by
    intro a b hab
    rw [← map_inv, Units.val_mul, show (embX c γ⁻¹).val = fromBlocks (γ⁻¹).val 0 0 1 from rfl]
    rcases a with x | i
    · rcases b with x' | j
      · have := congrFun (congrFun e2 x) x'
        simpa [mul_apply, Fintype.sum_sum_type, toBlocks₁₁, one_apply] using this
      · have hj : j.val + 1 ≤ p := by simpa [lev] using hab
        simp [mul_apply, Fintype.sum_sum_type, hz _ _ hj]
    · have := hr (.inr i) b hab (by simp)
      simpa [mul_apply, Fintype.sum_sum_type, one_apply] using this
  have : r = embX c γ * ((embX c γ)⁻¹ * r) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hm))

end GlobalTheory.SymChain.ResidueLift

namespace GlobalTheory.SymChain.ResidueLift

/- English proof (translation)
Introduce `k _ _ _ _ ϖ n _ _ c p h hg hpat`. Set `M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k` to `Matrix.of fun a b => if lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) then (1 : Matrix _ _ k) a b else ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b`. Establish `hM : MaxM (M - ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val)` using `fun a b => by`. Simplify using `only [M, Matrix.sub_apply, Matrix.of_apply]`. Use `split_ifs with hc`.

Rewrite using `[← neg_sub, Valuation.map_neg]`. Conclude with `hpat a b hc.1 hc.2`. Simplify using the standard rewrite rules. Take `⟨u', hu', eu'⟩` from `exists_mul_KOne hg hM`. Use `⟨(typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas) * u') * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n …` and prove the remaining obligations.

Use `mem_R_of_pattern _ fun a b h1 h2 => ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, eu', Model.typeFrame_val, Model.typeFrame_inv, mul_diagonal, diagonal_mul]`. Simplify using `only [M, Matrix.of_apply, if_pos (And.intro h1 h2)]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[mul_inv_cancel₀ (Model.wt_ne_zero ϖ a)]`. Simplify using `[one_apply_ne hab]`. Establish `e : (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹) * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas = u'⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `inv_mem hu'`.

Use `group`.
-/
theorem exists_R_mul_KOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  intro k _ _ _ _ ϖ n _ _ c p h hg hpat
  classical
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun a b =>
    if lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) then (1 : Matrix _ _ k) a b
    else ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b
  have hM : MaxM (M - ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val) := fun a b => by
    simp only [M, Matrix.sub_apply, Matrix.of_apply]
    split_ifs with hc
    · rw [← neg_sub, Valuation.map_neg]; exact hpat a b hc.1 hc.2
    · simp
  obtain ⟨u', hu', eu'⟩ := exists_mul_KOne hg hM
  refine ⟨(typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas *
      (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas) * u') *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_,
    (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_, ?_⟩
  · refine mem_R_of_pattern _ fun a b h1 h2 => ?_
    rw [Units.val_mul, Units.val_mul, eu', Model.typeFrame_val, Model.typeFrame_inv, mul_diagonal, diagonal_mul]
    simp only [M, Matrix.of_apply, if_pos (And.intro h1 h2)]
    by_cases hab : a = b
    · subst hab; simp [mul_inv_cancel₀ (Model.wt_ne_zero ϖ a)]
    · simp [one_apply_ne hab]
  · have e : (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ *
        (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹) * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas = u'⁻¹ := by group
    rw [e]; exact inv_mem hu'
  · group

end GlobalTheory.SymChain.ResidueLift
