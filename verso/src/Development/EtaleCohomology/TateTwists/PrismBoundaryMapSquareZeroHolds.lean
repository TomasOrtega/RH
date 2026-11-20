import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

/- English proof (translation)
Simplify using `only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]`. Both sides reduce to the same expression.
-/
lemma push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  simp only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

def inv {N : ℕ} (p : Fin (N + 3) × Fin (N + 2)) : Fin (N + 3) × Fin (N + 2) :=
  if h : (p.2 : ℕ) < p.1 then (p.2.castSucc, p.1.pred (by intro e; rw [e] at h; simp at h))
  else (p.2.succ, p.1.castPred (fun e => by have := congrArg Fin.val e; have := p.2.isLt; simp at this; simp at *; omega))

/- English proof (translation)
Introduce `N c`. Unfold `Pr.bd`. Simplify using `only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]`. Rewrite using `[← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]`. Use `Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_` and prove the remaining obligations.

Introduce and unpack `⟨i, j⟩ -`. Simplify using `only [inv]`. Use `split_ifs with h`. Establish `hj : j ≤ i.pred (fun e => by subst e; simp at h)`. Rewrite using `[Fin.le_def, Fin.val_pred]`.

Use linear arithmetic over natural numbers and integers. Establish `e` using `SimplexCategory.δ_comp_δ hj`. Establish `hi : (i.pred (fun e => by subst e; simp at h)).succ = i` using `Fin.succ_pred _ _`. Rewrite `e` using `[hi]`. Simplify using `only [Fin.val_castSucc, Fin.val_pred]`.

Rewrite using `[e, ← add_smul]`. Use `(congrArg (· • _) ?_).trans (zero_smul ℤ _)` and prove the remaining obligations. Take `⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[hk, Nat.add_sub_cancel, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Use `push Not at h`. Establish `hne : i ≠ Fin.last (N + 2)` using `fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega`. Establish `hj : i.castPred hne ≤ j` using `by rw [Fin.le_def, Fin.coe_castPred]; omega`. Establish `e` using `SimplexCategory.δ_comp_δ hj`. Rewrite `e` using `[Fin.castSucc_castPred]`.

Simplify using `only [Fin.val_succ, Fin.coe_castPred]`. Rewrite using `[← e, ← add_smul]`. Use `(congrArg (· • _) ?_).trans (zero_smul ℤ _)` and prove the remaining obligations. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨i, j⟩ - -`. Simplify using `only [inv]`. Apply the tactic sequence `split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega`. Introduce and unpack `⟨i, j⟩ -`. Simplify using `only [inv]`.

Use `split_ifs with h h2 h2`. It suffices to derive a contradiction. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers. Simplify using `[Prod.ext_iff, Fin.ext_iff]`.

Simplify using `[Prod.ext_iff, Fin.ext_iff]`. It suffices to derive a contradiction. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem prism_boundary_map_square_zero_holds : leaf_bdbd := by
  intro N c
  unfold Pr.bd
  simp only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]
  refine Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h
    · have hj : j ≤ i.pred (fun e => by subst e; simp at h) := by
        rw [Fin.le_def, Fin.val_pred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      have hi : (i.pred (fun e => by subst e; simp at h)).succ = i := Fin.succ_pred _ _
      rw [hi] at e
      simp only [Fin.val_castSucc, Fin.val_pred]
      rw [e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    · push Not at h
      have hne : i ≠ Fin.last (N + 2) := fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega
      have hj : i.castPred hne ≤ j := by rw [Fin.le_def, Fin.coe_castPred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      rw [Fin.castSucc_castPred] at e
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [← e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      rw [pow_succ]; ring
  · rintro ⟨i, j⟩ - -
    simp only [inv]
    split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h h2 h2
    · exfalso; simp at h2; omega
    · simp [Prod.ext_iff, Fin.ext_iff]
    · simp [Prod.ext_iff, Fin.ext_iff]
    · exfalso; simp at h2; omega

end LateralTheory.EtaleFoundations.SteenPf
