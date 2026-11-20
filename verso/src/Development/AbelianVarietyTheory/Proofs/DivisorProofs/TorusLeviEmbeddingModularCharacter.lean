import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock

namespace GlobalTheory.IndJacBlock

/- English proof (translation)
Introduce `k _ _ _ _ d h2 x`. Establish `hsc : ∀ (n : Type) [Fintype n] [DecidableEq n] (u : kˣ) (i j : n), ((Matrix.GeneralLinearGroup.scalar n u : GL n k) : Matrix n n k) i j = if i = j then (u : k) else 0`. Introduce `n _ _ u i j`. Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]`. Establish `hdet : ∀ (n : Type) [Fintype n] [DecidableEq n] (u : kˣ), Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n u) = u ^ Fintype.card n`.

Introduce `n _ _ u`. Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Prove the components needed by the constructor for the conclusion. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Take `⟨⟨a, i'⟩, rfl⟩` from `(place3 h2).surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `(place3 h2).surjective j`. Rewrite using `[GlobalTheory.JacBlock₂.diagFirst_apply]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Rewrite using `[leviEmb_apply_same, torus_three_block_apply, hsc]`. Establish `hinj : (place3 h2 ⟨a, i'⟩ = place3 h2 ⟨a, j'⟩) ↔ i' = j'`. Rewrite using `[(place3 h2).injective.eq_iff]`. Simplify using the standard rewrite rules.

Establish `hv : ((place3 h2 ⟨a, i'⟩ : Fin d) : ℕ) = 0 ↔ (a : ℕ) = 0`. Establish `hi : (i' : ℕ) < sz3 d a` using `i'.2`. Unfold `place3`. Rewrite using `[stdBlocks_val]`. Apply the tactic sequence `fin_cases a <;> simp [sz3, Fin.sum_univ_succ] at hi ⊢ <;> omega`.

Simplify using `only [hinj, hv]`. Distinguish the cases in `hij : i' = j'`. Simplify using `only [hij, if_true]`. Unfold `torEntry`. Apply the tactic sequence `split_ifs <;> simp_all`.

Simplify using `[hij]`. Rewrite using `[leviEmb_apply_ne k (place3 h2) _ hab, if_neg]`. Introduce `h`. Conclude with `hab (congrArg Sigma.fst ((place3 h2).injective h))`. Rewrite using `[deltaHalf_apply, Units.coe_prod, Fin.prod_univ_three]`.

Establish `e1 : tor3 k d (x, 1) 1 = 1` using `by rw [torus_three_block_apply]; simp [torEntry]`. Establish `e2 : tor3 k d (x, 1) 2 = 1` using `by rw [torus_three_block_apply]; simp [torEntry]`. Establish `e0 : Matrix.GeneralLinearGroup.det (tor3 k d (x, 1) 0) = x`. Rewrite using `[torus_three_block_apply, hdet]`. Simplify using `[torEntry, sz3]`.

Establish `hm : modExp (fun j : Fin 3 => Fin (sz3 d j)) 0 = (d : ℤ) - 1`. Simplify using `only [modExp, Fintype.card_fin, Finset.sum_filter, Fin.sum_univ_three]`. Simplify using `[sz3]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2, e0, hm]`.

Simplify using `[val_absPow, GlobalTheory.SplitFlip.apow]`.
-/
theorem torus_levi_embedding_modulus_half : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (h2 : 2 ≤ d) (x : kˣ),
    leviEmb k (place3 h2) (tor3 k d (x, 1)) = GlobalTheory.JacBlock₂.diagFirst x ∧
    (deltaHalf k (fun j : Fin 3 => Fin (sz3 d j)) (tor3 k d (x, 1)) : ℂ) = GlobalTheory.SplitFlip.apow x (((d : ℂ) - 1) / 2) := by
  intro k _ _ _ _ d h2 x
  have hsc : ∀ (n : Type) [Fintype n] [DecidableEq n] (u : kˣ) (i j : n),
      ((Matrix.GeneralLinearGroup.scalar n u : GL n k) : Matrix n n k) i j = if i = j then (u : k) else 0 := by
    intro n _ _ u i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hdet : ∀ (n : Type) [Fintype n] [DecidableEq n] (u : kˣ),
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n u) = u ^ Fintype.card n := by
    intro n _ _ u; ext; simp [Matrix.GeneralLinearGroup.scalar]
  constructor
  · apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := (place3 h2).surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := (place3 h2).surjective j
    rw [GlobalTheory.JacBlock₂.diagFirst_apply]
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, torus_three_block_apply, hsc]
      have hinj : (place3 h2 ⟨a, i'⟩ = place3 h2 ⟨a, j'⟩) ↔ i' = j' := by
        rw [(place3 h2).injective.eq_iff]; simp
      have hv : ((place3 h2 ⟨a, i'⟩ : Fin d) : ℕ) = 0 ↔ (a : ℕ) = 0 := by
        have hi : (i' : ℕ) < sz3 d a := i'.2
        unfold place3; rw [stdBlocks_val]
        fin_cases a <;> simp [sz3, Fin.sum_univ_succ] at hi ⊢ <;> omega
      simp only [hinj, hv]
      by_cases hij : i' = j'
      · simp only [hij, if_true]
        unfold torEntry
        split_ifs <;> simp_all
      · simp [hij]
    · rw [leviEmb_apply_ne k (place3 h2) _ hab, if_neg]
      intro h; exact hab (congrArg Sigma.fst ((place3 h2).injective h))
  · rw [deltaHalf_apply, Units.coe_prod, Fin.prod_univ_three]
    have e1 : tor3 k d (x, 1) 1 = 1 := by rw [torus_three_block_apply]; simp [torEntry]
    have e2 : tor3 k d (x, 1) 2 = 1 := by rw [torus_three_block_apply]; simp [torEntry]
    have e0 : Matrix.GeneralLinearGroup.det (tor3 k d (x, 1) 0) = x := by
      rw [torus_three_block_apply, hdet]; simp [torEntry, sz3]
    have hm : modExp (fun j : Fin 3 => Fin (sz3 d j)) 0 = (d : ℤ) - 1 := by
      simp only [modExp, Fintype.card_fin, Finset.sum_filter, Fin.sum_univ_three]
      simp [sz3]; omega
    rw [e1, e2, e0, hm]
    simp [val_absPow, GlobalTheory.SplitFlip.apow]

end GlobalTheory.IndJacBlock
