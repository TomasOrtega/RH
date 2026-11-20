import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PbSmithLam
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.WeylDimShift

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.WeylDimBound

/- English proof (translation)
The claim follows from `Formalism.MainNotions.flipOneThree.Pf.pb_finrank ℂ n la hla`.
-/
theorem dim_eq_weylDim (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) :
    (GlobalTheory.DualWeyl.dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) :=
  Formalism.MainNotions.flipOneThree.Pf.pb_finrank ℂ n la hla

/- English proof (translation)
Establish `hanti : Antitone (fun i : Fin n => s - la (Fin.rev i))`. Introduce `i j hij`. Use `hla (Fin.rev_le_rev.mpr hij)` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `dim_eq_weylDim n _ hanti`. Establish `h2` using `dim_eq_weylDim n la hla`. Establish `h3 : Formalism.CountingSumsFrames.weylDim n (fun i => (((s - la (Fin.rev i) : ℕ)) : ℤ)) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ))`. Establish `e : (fun i : Fin n => (((s - la (Fin.rev i) : ℕ)) : ℤ)) = fun i => -((fun k => (la k : ℤ)) i.rev) + (s : ℤ)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Nat.cast_sub (hs _)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Formalism.MainNotions.Pf14.weylDim_shift n (fun i => -((fun k => (la k : ℤ)) i.rev)) (s : ℤ)]`. Conclude with `Formalism.MainNotions.Pf14.weylDim_dual n (fun k => (la k : ℤ))`. Conclude with `h1.trans (h3.trans h2.symm)` after adjusting the coercions.
-/
theorem dim_dual (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (s : ℕ) (hs : ∀ i, la i ≤ s) :
    GlobalTheory.DualWeyl.dim (fun i => s - la (Fin.rev i)) = GlobalTheory.DualWeyl.dim la := by
  have hanti : Antitone (fun i : Fin n => s - la (Fin.rev i)) := by
    intro i j hij
    have := hla (Fin.rev_le_rev.mpr hij)
    dsimp only
    omega
  have h1 := dim_eq_weylDim n _ hanti
  have h2 := dim_eq_weylDim n la hla
  have h3 : Formalism.CountingSumsFrames.weylDim n (fun i => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
      Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) := by
    have e : (fun i : Fin n => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
        fun i => -((fun k => (la k : ℤ)) i.rev) + (s : ℤ) := by
      funext i
      rw [Nat.cast_sub (hs _)]
      ring
    rw [e, Formalism.MainNotions.Pf14.weylDim_shift n (fun i => -((fun k => (la k : ℤ)) i.rev)) (s : ℤ)]
    exact Formalism.MainNotions.Pf14.weylDim_dual n (fun k => (la k : ℤ))
  exact_mod_cast h1.trans (h3.trans h2.symm)

/- English proof (translation)
Establish `h1 : ∀ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n - 1 - i`. Introduce `i`. Rewrite using `[← Fin.card_Ioi]`. Use `congr 1`. Use extensionality with `j`.

Simplify using the standard rewrite rules. Simplify using `only [h1]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n, Finset.sum_range_reflect (fun k => k) n, Finset.sum_range_id, Nat.choose_two_right]`.
-/
theorem sum_card_lt (n : ℕ) : ∑ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n.choose 2 := by
  have h1 : ∀ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n - 1 - i := by
    intro i
    rw [← Fin.card_Ioi]
    congr 1
    ext j
    simp
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n, Finset.sum_range_reflect (fun k => k) n,
    Finset.sum_range_id, Nat.choose_two_right]

/- English proof (translation)
Simplify using `only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_card_lt]`.
-/
theorem prod_ite_lt (n : ℕ) (c : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if i < j then c else 1) = c ^ n.choose 2 := by
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, sum_card_lt]

/- English proof (translation)
Use `set S := ∑ i, |((la i : ℤ) : ℝ) - w| with hS`. Establish `hcast : ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) = ∏ i : Fin n, ∏ j : Fin n, (if i < j then (((la i : ℝ) - la j) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1)`. Unfold `Formalism.CountingSumsFrames.weylDim`. Rewrite using `[Rat.cast_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Rat.cast_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Establish `hpair : ∀ i j : Fin n, i ≠ j → |((la i : ℤ) : ℝ) - w| + |((la j : ℤ) : ℝ) - w| ≤ S`. Introduce `i j hij`.

Rewrite using `[← Finset.sum_pair (f := fun k => |((la k : ℤ) : ℝ) - w|) hij]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => abs_nonneg _`. Rewrite using `[hcast, ← prod_ite_lt]`. Use `Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ => Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with hij`.

Establish `hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ)` using `by exact_mod_cast (Fin.lt_def.mp hij)`. Establish `ha : (la j : ℝ) ≤ la i` using `by exact_mod_cast hla hij.le`. Conclude with `div_nonneg (by linarith) (by linarith)`. Conclude with `zero_le_one`. Use `split_ifs with hij`.

Establish `hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ)` using `by exact_mod_cast (Fin.lt_def.mp hij)`. Establish `ha : (la j : ℝ) ≤ la i` using `by exact_mod_cast hla hij.le`. Conclude with `div_nonneg (by linarith) (by linarith)`. Conclude with `zero_le_one`. Use `split_ifs with hij`.

Establish `hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ)` using `by exact_mod_cast (Fin.lt_def.mp hij)`. Establish `ha : (la j : ℝ) ≤ la i` using `by exact_mod_cast hla hij.le`. Establish `hp` using `hpair i j hij.ne`. Establish `h1` using `le_abs_self (((la i : ℤ) : ℝ) - w)`. Establish `h2` using `neg_abs_le (((la j : ℤ) : ℝ) - w)`.

Move the coercions through the operations in `at hp h1 h2`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_rfl`.
-/
theorem weylDim_le (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (w : ℤ) :
    ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  set S := ∑ i, |((la i : ℤ) : ℝ) - w| with hS
  have hcast : ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) = ∏ i : Fin n, ∏ j : Fin n,
      (if i < j then (((la i : ℝ) - la j) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) := by
    unfold Formalism.CountingSumsFrames.weylDim
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> push_cast <;> ring
  have hpair : ∀ i j : Fin n, i ≠ j → |((la i : ℤ) : ℝ) - w| + |((la j : ℤ) : ℝ) - w| ≤ S := by
    intro i j hij
    rw [← Finset.sum_pair (f := fun k => |((la k : ℤ) : ℝ) - w|) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => abs_nonneg _
  rw [hcast, ← prod_ite_lt]
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_)
    fun i _ => Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      have hp := hpair i j hij.ne
      have h1 := le_abs_self (((la i : ℤ) : ℝ) - w)
      have h2 := neg_abs_le (((la j : ℤ) : ℝ) - w)
      push_cast at hp h1 h2
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact le_rfl

/- English proof (translation)
Introduce `n la hla`. Use `⟨dim_eq_weylDim n la hla, fun s hs => dim_dual n la hla s hs, fun w => ?_⟩` and prove the remaining obligations. Establish `h : (dim la : ℝ) = ((dim la : ℚ) : ℝ)` using `(Rat.cast_natCast _).symm`. Rewrite using `[h, dim_eq_weylDim n la hla]`. Conclude with `weylDim_le n la hla w`.
-/
theorem dim_weyl_dual_bound : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la →
    (dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) ∧
      (∀ s : ℕ, (∀ i, la i ≤ s) → dim (fun i => s - la (Fin.rev i)) = dim la) ∧
      ∀ w : ℤ, (dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  intro n la hla
  refine ⟨dim_eq_weylDim n la hla, fun s hs => dim_dual n la hla s hs, fun w => ?_⟩
  have h : (dim la : ℝ) = ((dim la : ℚ) : ℝ) := (Rat.cast_natCast _).symm
  rw [h, dim_eq_weylDim n la hla]
  exact weylDim_le n la hla w

end GlobalTheory.WeylDimBound
