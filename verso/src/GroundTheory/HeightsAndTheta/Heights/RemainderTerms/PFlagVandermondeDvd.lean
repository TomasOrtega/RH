import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagVandermondeDvd

/- English proof (translation)
Rewrite using `[Finset.prod_filter, Fintype.prod_prod_type]`. Simplify using `only [blockVandermonde, vandermondeOf]`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Establish `: Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j)` using `by ext; simp`. Rewrite using `[this, Finset.prod_filter]`.
-/
theorem blockVandermonde_eq_prod (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j) := by ext; simp
  rw [this, Finset.prod_filter]

/- English proof (translation)
Unfold `blockPermute`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨σ, k⟩` from `p`. Distinguish the cases in `hσ : σ = τ`.

Substitute `hσ` using the available equality. Simplify using `only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]`. Apply the tactic sequence `split_ifs <;> rfl`. Simplify using `only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]`. Apply the tactic sequence `rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]`.
-/
theorem rename_swap_eq (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by
  unfold blockPermute
  congr 1
  funext p
  obtain ⟨σ, k⟩ := p
  by_cases hσ : σ = τ
  · subst hσ
    simp only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]

/- English proof (translation)
Unfold `blockSign`. Rewrite using `[Fintype.prod_eq_single τ]`. Simplify using `[Equiv.Perm.sign_swap hij]`. Introduce `σ hσ`. Simplify using `[Function.update_of_ne hσ]`.
-/
theorem blockSign_update_swap (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by
  unfold blockSign
  rw [Fintype.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hij]
  · intro σ hσ
    simp [Function.update_of_ne hσ]

end FlagVandermondeDvd

open FlagVandermondeDvd in

/- English proof (translation)
Introduce `f N P hP`. Rewrite using `[blockVandermonde_eq_prod]`. Use `h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨τ, i, j⟩ ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht`.

Conclude with `h2 _ _ _ (by simp [ht.ne])`. Introduce and unpack `⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'`. Use `h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨ha, hb⟩`.

Simplify using `only [Prod.mk.injEq] at ha hb`. Conclude with `hne (by rw [ha.1, ha.2, hb.2])`. Introduce and unpack `⟨ha, hb⟩`. Simplify using `only [Prod.mk.injEq] at ha hb`. Rewrite `ht` using `[ha.2, hb.2]`.

Conclude with `absurd (ht.trans ht') (lt_irrefl _)`. Introduce and unpack `⟨τ, i, j⟩ ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ht`. Use `h1 _ P _ _ (by simp [ht.ne]) ?_` and prove the remaining obligations. Rewrite using `[rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]`.
-/
theorem FlagVandermondeDvd.proof (h1 : FlagSwapDivisible.Statement) (h2 : FlagDiffPrime.Statement)
    (h3 : FlagDiffNotDvd.Statement) (h4 : FlagProdPrimesDvd.Statement) :
    FlagVandermondeDvd.Statement := by
  intro f N P hP
  rw [blockVandermonde_eq_prod]
  refine h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h2 _ _ _ (by simp [ht.ne])
  · rintro ⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      exact hne (by rw [ha.1, ha.2, hb.2])
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      rw [ha.2, hb.2] at ht
      exact absurd (ht.trans ht') (lt_irrefl _)
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine h1 _ P _ _ (by simp [ht.ne]) ?_
    rw [rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
