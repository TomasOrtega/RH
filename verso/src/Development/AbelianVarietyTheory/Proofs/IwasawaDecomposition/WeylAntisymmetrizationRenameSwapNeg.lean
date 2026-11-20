import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmSwap

/- English proof (translation)
Introduce `ι _ _ m Q τ i j hij`. Use `set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu`. Establish `hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)), (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m)`. Introduce `w`. Use function extensionality and compare the values at `⟨t, k⟩`.

Simplify using `only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]`. Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality. Simplify using `only [hu, Function.update_self]`. Rewrite using `[Equiv.swap_apply_def, Equiv.swap_apply_def]`.

Apply the tactic sequence `split_ifs <;> simp_all`. Establish `h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩` using `fun h => ht (congrArg Sigma.fst h)`. Establish `h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩` using `fun h => ht (congrArg Sigma.fst h)`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]`. Both sides reduce to the same expression.

Establish `hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1`. Rewrite using `[Fintype.prod_eq_single τ]`. Simplify using `[hu, Equiv.Perm.sign_swap hij]`. Introduce `t ht`. Simplify using `[hu, Function.update_of_ne ht]`.

Establish `hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)), (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t)`. Introduce `w`. Simplify using `only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]`. Unfold `GlobalTheory.GoodMetric.antisymm`. Rewrite using `[map_sum]`.

Repeatedly rewrite using `[map_zsmul, rename_rename, hf]`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_` and prove the remaining obligations. Introduce `w _`. Simplify using `only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]`.
-/
theorem rename_swap_antisymm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι)
    (i j : Fin (m τ)), i ≠ j →
      rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  intro ι _ _ m Q τ i j hij
  set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu
  have hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))
        = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m) := by
    intro w
    funext ⟨t, k⟩
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]
    by_cases ht : t = τ
    · subst ht
      simp only [hu, Function.update_self]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩ := fun h => ht (congrArg Sigma.fst h)
      have h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩ := fun h => ht (congrArg Sigma.fst h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]
      rfl
  have hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1 := by
    rw [Fintype.prod_eq_single τ]
    · simp [hu, Equiv.Perm.sign_swap hij]
    · intro t ht
      simp [hu, Function.update_of_ne ht]
  have hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t) := by
    intro w
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]
  unfold GlobalTheory.GoodMetric.antisymm
  rw [map_sum]
  simp_rw [map_zsmul, rename_rename, hf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_
  intro w _
  simp only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]

end GlobalTheory.AntisymmSwap
