import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeFamOf
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
import Formalism.PolynomialDimension.FinalNum
import Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.CountingSumsFrames

/- English proof (translation)
Establish `hcons : weylDim (m + 2) (Fin.cons ((a' : ℤ) + mu 0) mu) = (∏ j : Fin (m + 1), (((((a' : ℤ) + mu 0 - mu j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim (m + 1) mu` using `gram_weylDim_cons (m + 1) ((a' : ℤ) + mu 0) mu`. Establish `hP : (((∏ j : Fin (m + 1), (((((a' : ℤ) + mu 0 - mu j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) : ℚ) : ℝ) = ∏ j : Fin (m + 1), ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)`. Rewrite using `[Rat.cast_prod]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcons, Rat.cast_mul, hP]`. Establish `hW : (0 : ℝ) < (weylDim (m + 1) mu : ℝ)` using `by exact_mod_cast gram_weylDim_pos (m + 1) mu hanti`. Establish `hc0 : (0 : ℝ) ≤ c₀` using `Nat.cast_nonneg c₀`. Establish `hx : (0 : ℝ) ≤ (c₀ : ℝ) / a` using `div_nonneg hc0 ha.le`.

Establish `hxa : (c₀ : ℝ) / a * a = c₀` using `div_mul_cancel₀ _ ha.ne'`. Establish `hmu0c : ((mu 0 : ℤ) : ℝ) ≤ c₀` using `by exact_mod_cast (hmu 0).2`. Establish `hf : ∀ j : Fin (m + 1), 0 ≤ ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)`. Introduce `j`. Establish `h1 : ((mu j : ℤ) : ℝ) ≤ mu 0` using `by exact_mod_cast hanti (Fin.zero_le j)`.

Establish `h2 : (0 : ℝ) ≤ a'` using `Nat.cast_nonneg a'`. Establish `h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Apply the tactic sequence `apply div_nonneg <;> linarith`. Establish `hfg : ∀ j : Fin (m + 1), ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) ≤ (1 + (c₀ : ℝ) / a) * (((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1))`. Introduce `j`.

Establish `h1 : (0 : ℝ) ≤ mu j` using `by exact_mod_cast (hmu j).1`. Establish `h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `h4 : (c₀ : ℝ) / a * a ≤ (c₀ : ℝ) / a * ((a' : ℝ) + ((j : ℕ) : ℝ) + 1)` using `mul_le_mul_of_nonneg_left (by linarith) hx`. Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `hPle` using `gram_prod_le (m + 1) _ _ ((c₀ : ℝ) / a) hf hfg`. Establish `hC` using `gram_choose_prod a' (m + 1)`. Rewrite `hC` using `[show a' + (m + 1) = a' + m + 1 by ring]`. Rewrite `hPle` using `[← hC]`.

Establish `hP0 : 0 ≤ ∏ j : Fin (m + 1), ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_nonneg fun j _ => hf j`. Establish `hkey : (1 - ((m : ℝ) + 2) * c₀ / a) * (1 + (c₀ : ℝ) / a) ^ (m + 1) ≤ 1`. Apply `gram_key (m + 1) _ _ hx` to reduce the goal to its premises. Establish `e : ((m : ℝ) + 2) * c₀ / a = ((m : ℝ) + 2) * ((c₀ : ℝ) / a)` using `by ring`. Rewrite using `[e]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `one_sub_mul_mul_le _ _ _ _ _ (m + 1) hW.le hP0 (Nat.cast_nonneg _) hPle hkey`.
-/
theorem weylDim_cons_le_choose_mul (m : ℕ) (mu : Fin (m + 1) → ℤ) (a' : ℕ) (c₀ : ℕ) (a : ℝ) (ha : 0 < a) (hanti : Antitone mu)
    (hmu : ∀ i, 0 ≤ mu i ∧ mu i ≤ c₀) (haa' : a ≤ a') :
    (1 - ((m : ℝ) + 2) * c₀ / a) * (weylDim (m + 2) (Fin.cons ((a' : ℤ) + mu 0) mu) : ℝ) ≤
      ((a' + m + 1).choose (m + 1) : ℝ) * (weylDim (m + 1) mu : ℝ) := by
  have hcons : weylDim (m + 2) (Fin.cons ((a' : ℤ) + mu 0) mu) =
      (∏ j : Fin (m + 1), (((((a' : ℤ) + mu 0 - mu j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) *
        weylDim (m + 1) mu := gram_weylDim_cons (m + 1) ((a' : ℤ) + mu 0) mu
  have hP : (((∏ j : Fin (m + 1), (((((a' : ℤ) + mu 0 - mu j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) /
      (((j : ℕ) : ℚ) + 1)) : ℚ) : ℝ) =
      ∏ j : Fin (m + 1), ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  rw [hcons, Rat.cast_mul, hP]
  have hW : (0 : ℝ) < (weylDim (m + 1) mu : ℝ) := by exact_mod_cast gram_weylDim_pos (m + 1) mu hanti
  have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
  have hx : (0 : ℝ) ≤ (c₀ : ℝ) / a := div_nonneg hc0 ha.le
  have hxa : (c₀ : ℝ) / a * a = c₀ := div_mul_cancel₀ _ ha.ne'
  have hmu0c : ((mu 0 : ℤ) : ℝ) ≤ c₀ := by exact_mod_cast (hmu 0).2
  have hf : ∀ j : Fin (m + 1),
      0 ≤ ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
    intro j
    have h1 : ((mu j : ℤ) : ℝ) ≤ mu 0 := by exact_mod_cast hanti (Fin.zero_le j)
    have h2 : (0 : ℝ) ≤ a' := Nat.cast_nonneg a'
    have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    apply div_nonneg <;> linarith
  have hfg : ∀ j : Fin (m + 1),
      ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) ≤
        (1 + (c₀ : ℝ) / a) * (((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) := by
    intro j
    have h1 : (0 : ℝ) ≤ mu j := by exact_mod_cast (hmu j).1
    have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (c₀ : ℝ) / a * a ≤ (c₀ : ℝ) / a * ((a' : ℝ) + ((j : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hx
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hPle := gram_prod_le (m + 1) _ _ ((c₀ : ℝ) / a) hf hfg
  have hC := gram_choose_prod a' (m + 1)
  rw [show a' + (m + 1) = a' + m + 1 by ring] at hC
  rw [← hC] at hPle
  have hP0 : 0 ≤ ∏ j : Fin (m + 1),
      ((a' : ℝ) + (mu 0 : ℝ) - (mu j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => hf j
  have hkey : (1 - ((m : ℝ) + 2) * c₀ / a) * (1 + (c₀ : ℝ) / a) ^ (m + 1) ≤ 1 := by
    apply gram_key (m + 1) _ _ hx
    have e : ((m : ℝ) + 2) * c₀ / a = ((m : ℝ) + 2) * ((c₀ : ℝ) / a) := by ring
    rw [e]
    push_cast
    nlinarith
  exact one_sub_mul_mul_le _ _ _ _ _ (m + 1) hW.le hP0 (Nat.cast_nonneg _) hPle hkey

/- English proof (translation)
Unfold `weylDim`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: lam i + c - (lam j + c) = lam i - lam j` using `by ring`. Rewrite using `[this]`.
-/
theorem weylDim_shift (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) : weylDim n (fun i => lam i + c) = weylDim n lam := by
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  have : lam i + c - (lam j + c) = lam i - lam j := by ring
  rw [this]

/- English proof (translation)
Unfold `weylDim`. Establish `key : ∀ i j : Fin n, (if i < j then ((((-lam i.rev) - (-lam j.rev) : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1) = (if j.rev < i.rev then (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) / (((i.rev : ℕ) : ℚ) - ((j. …`. Introduce `i j`. Establish `e : (((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)`. Rewrite using `[Fin.val_rev, Fin.val_rev, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Fin.rev_lt_rev]`. Use `split_ifs`. Establish `e2 : (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) = ((((-lam i.rev) - (-lam j.rev) : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))`.

Establish `: (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) = ((lam j.rev - lam i.rev : ℤ) : ℚ) + (((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ))` using `by ring`. Rewrite using `[this, e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, e]`.

Both sides reduce to the same expression. Simplify using `only [key]`. Rewrite using `[Finset.prod_comm]`. Rewrite using `[← Equiv.prod_comp Fin.revPerm]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← Equiv.prod_comp Fin.revPerm]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`.
-/
theorem weylDim_dual (n : ℕ) (lam : Fin n → ℤ) : weylDim n (fun i => -lam i.rev) = weylDim n lam := by
  unfold weylDim
  have key : ∀ i j : Fin n,
      (if i < j then ((((-lam i.rev) - (-lam j.rev) : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
          (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1) =
      (if j.rev < i.rev then (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) /
          (((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) else 1) := by
    intro i j
    have e : (((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by
      rw [Fin.val_rev, Fin.val_rev, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [Fin.rev_lt_rev]
    split_ifs
    · have e2 : (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) =
          ((((-lam i.rev) - (-lam j.rev) : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
        have : (((lam j.rev - lam i.rev : ℤ) : ℚ) + ((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) =
            ((lam j.rev - lam i.rev : ℤ) : ℚ) + (((i.rev : ℕ) : ℚ) - ((j.rev : ℕ) : ℚ)) := by ring
        rw [this, e]
        push_cast
        ring
      rw [e2, e]
    · rfl
  simp only [key]
  rw [Finset.prod_comm]
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]

end Formalism.MainNotions.Pf14
