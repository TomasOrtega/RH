import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InnerCLe

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Establish `key : ∀ S : Finset (Fin (p + 1)), 0 ∉ S → ∑ j ∈ S, ν j = -∑ j ∈ S, e j` using `fun S hS => by`. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun j hj => hl j (fun h => hS (h ▸ hj))`. Establish `hsplit : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, ν j = ν 0 + ∑ j ∈ (Finset.Iic l).erase 0, ν j` using `fun l => (Finset.add_sum_erase _ _ (Finset.mem_Iic.mpr (by simp))).symm`. Establish `hE : ∀ l : Fin (p + 1), ∑ j ∈ (Finset.Iic l).erase 0, e j ≤ ∑ j ∈ Finset.univ.erase 0, e j` using `fun l => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase _ (Finset.subset_univ _)) (fun j _ _ => (he j).le)`.

Establish `hX : ∀ l : Fin (p + 1), 0 ≤ ∑ j ∈ (Finset.Iic l).erase 0, e j` using `fun l => Finset.sum_nonneg fun j _ => (he j).le`. Establish `h0S : ∀ l : Fin (p + 1), (0 : Fin (p + 1)) ∉ (Finset.Iic l).erase 0` using `fun l => by simp`. Use `⟨fun l => ?_, fun l _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit, key _ (h0S l), h0]`. Combine the linear relations using `[hE l, hX l, he 0]`.

Establish `hIoi : (0 : Fin (p + 1)) ∉ Finset.Ioi l` using `by simp`. Establish `hpart : ∑ j ∈ Finset.univ.erase 0, e j = ∑ j ∈ (Finset.Iic l).erase 0, e j + ∑ j ∈ Finset.Ioi l, e j`. Rewrite using `[← Finset.sum_union]`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_union, Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ, and_true]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Distinguish the cases in `hjl : j ≤ l`. Conclude with `Or.inl ⟨h, hjl⟩`.

Conclude with `Or.inr (not_le.mp hjl)`. Introduce and unpack `(⟨h, _⟩ | h)`. Conclude with `h`. Conclude with `(lt_of_le_of_lt (by simp : (0 : Fin (p + 1)) ≤ l) h).ne'`. Rewrite using `[Finset.disjoint_left]`.

Introduce `j hj1 hj2`. Simplify using `only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi] at hj1 hj2`. Conclude with `absurd hj1.2 (not_le.mpr hj2)`. Rewrite using `[hsplit, key _ (h0S l), key _ hIoi, h0]`. Combine the linear relations using `[hpart, hX l, he 0]`.
-/
theorem chcond_of {p : ℕ} (ν e : Fin (p + 1) → ℝ) (he : ∀ l, 0 < e l)
    (h0 : ν 0 = e 0 + 2 * ∑ l ∈ Finset.univ.erase 0, e l) (hl : ∀ l, l ≠ 0 → ν l = -e l) : CHCond p ν := by
  have key : ∀ S : Finset (Fin (p + 1)), 0 ∉ S → ∑ j ∈ S, ν j = -∑ j ∈ S, e j := fun S hS => by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hl j (fun h => hS (h ▸ hj))
  have hsplit : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, ν j = ν 0 + ∑ j ∈ (Finset.Iic l).erase 0, ν j :=
    fun l => (Finset.add_sum_erase _ _ (Finset.mem_Iic.mpr (by simp))).symm
  have hE : ∀ l : Fin (p + 1), ∑ j ∈ (Finset.Iic l).erase 0, e j ≤ ∑ j ∈ Finset.univ.erase 0, e j :=
    fun l => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase _ (Finset.subset_univ _))
      (fun j _ _ => (he j).le)
  have hX : ∀ l : Fin (p + 1), 0 ≤ ∑ j ∈ (Finset.Iic l).erase 0, e j :=
    fun l => Finset.sum_nonneg fun j _ => (he j).le
  have h0S : ∀ l : Fin (p + 1), (0 : Fin (p + 1)) ∉ (Finset.Iic l).erase 0 := fun l => by simp
  refine ⟨fun l => ?_, fun l _ => ?_⟩
  · rw [hsplit, key _ (h0S l), h0]
    linarith [hE l, hX l, he 0]
  · have hIoi : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp
    have hpart : ∑ j ∈ Finset.univ.erase 0, e j =
        ∑ j ∈ (Finset.Iic l).erase 0, e j + ∑ j ∈ Finset.Ioi l, e j := by
      rw [← Finset.sum_union]
      · congr 1
        ext j
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ, and_true]
        constructor
        · intro h
          by_cases hjl : j ≤ l
          · exact Or.inl ⟨h, hjl⟩
          · exact Or.inr (not_le.mp hjl)
        · rintro (⟨h, _⟩ | h)
          · exact h
          · exact (lt_of_le_of_lt (by simp : (0 : Fin (p + 1)) ≤ l) h).ne'
      · rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi] at hj1 hj2
        exact absurd hj1.2 (not_le.mpr hj2)
    rw [hsplit, key _ (h0S l), key _ hIoi, h0]
    linarith [hpart, hX l, he 0]

section fin
variable (k r' : ℕ)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succ]`. Establish `e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i)` using `fun i => Fin.ext (by simp [sc])`. Simplify using `only [e]`. Rewrite using `[Fin.sum_congr' (fun j => f (sc r' j)) (by omega : 1 + r' = r' + 1)]`.
-/
theorem sum_sc (f : Fin (1 + r' + 1) → ℝ) : ∑ l, f l = f 0 + ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Fin.sum_univ_succ]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e]
  rw [Fin.sum_congr' (fun j => f (sc r' j)) (by omega : 1 + r' = r' + 1)]

/- English proof (translation)
Rewrite using `[Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_sc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_erase0 (f : Fin (1 + r' + 1) → ℝ) : ∑ l ∈ Finset.univ.erase 0, f l = ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_sc]; ring

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc]`. Establish `h1 : ∀ i : Fin r', s0 k (1 + r') (sc r' (Fin.castSucc i)) = 2` using `fun i => by`. Use `i.isLt` as an intermediate fact. Conclude with `if_pos (by simp only [sc, Fin.val_castSucc]; omega)`. Establish `h2 : s0 k (1 + r') (sc r' (Fin.last r')) = k`.

Conclude with `if_neg (by simp only [sc, Fin.val_last]; omega)`. Simplify using `only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_levelExponents_shifted : ∑ l : Fin (r' + 1), s0 k (1 + r') (sc r' l) = 2 * (r' : ℝ) + k := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin r', s0 k (1 + r') (sc r' (Fin.castSucc i)) = 2 := fun i => by
    have := i.isLt
    exact if_pos (by simp only [sc, Fin.val_castSucc]; omega)
  have h2 : s0 k (1 + r') (sc r' (Fin.last r')) = k := by
    exact if_neg (by simp only [sc, Fin.val_last]; omega)
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/- English proof (translation)
Conclude with `if_pos (by simp)`.
-/
theorem levelExponent_first_eq_two : s0 k (1 + r') 0 = 2 := by
  exact if_pos (by simp)

/- English proof (translation)
Unfold `s0N s0`. Use `split_ifs`. Both sides reduce to the same expression. Rewrite using `[Nat.cast_sub hk]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponentShift_eq_levelExponent (hk : 1 ≤ k) (l : Fin (1 + r' + 1)) : s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
  unfold s0N s0
  split_ifs
  · rfl
  · rw [Nat.cast_sub hk]; push_cast; ring

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[sc] at this`.
-/
theorem sc_ne_zero (l : Fin (r' + 1)) : sc r' l ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [sc] at this

/- English proof (translation)
Establish `hPsi : 0 ≤ Psi k r' s x` using `Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hGl _) hG0.le) _`. Rewrite using `[← ENNReal.ofReal_mul hPsi, ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hGl l) _)]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ, if_pos rfl]`. Establish `e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i)` using `fun i => Fin.ext (by simp [sc])`.

Simplify using `only [e, sc_ne_zero, if_false]`. Rewrite using `[Fin.prod_congr' (fun j => Ga k (1 + r') (sc r' j) (Yx k r' x) ^ (-s (sc r' j) / 2)) (by omega : 1 + r' = r' + 1)]`. Unfold `Psi Dx`. Establish `hP : ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2) = (∏ l : Fin (r' + 1), Ga k (1 + r') (sc r' l) (Yx k r' x) ^ (-s (sc r' l) / 2)) * Ga k (1 + r') 0 (Yx k r' x) ^ (∑ l : Fin (r' + 1), s (sc r' l) / 2)`. Rewrite using `[Real.rpow_sum_of_pos hG0, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Real.div_rpow (hGl _) hG0.le, div_eq_mul_inv, ← Real.rpow_neg hG0.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ (-(aw + 2)) = Ga k (1 + r') 0 (Yx k r' x) ^ (-(aw + 2) / 2)`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_mul hG0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hP, hD, mul_assoc, ← Real.rpow_add hG0, mul_comm]`. Use `congr 2`.

Rewrite using `[← Finset.sum_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th_ident (s : Fin (1 + r' + 1) → ℝ) (aw : ℝ) (x : HPar k r') (hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x))
    (hGl : ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x)) :
    ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) =
      ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^
        (-(if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) / 2)) := by
  have hPsi : 0 ≤ Psi k r' s x := Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hGl _) hG0.le) _
  rw [← ENNReal.ofReal_mul hPsi, ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hGl l) _)]
  congr 1
  rw [Fin.prod_univ_succ, if_pos rfl]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e, sc_ne_zero, if_false]
  rw [Fin.prod_congr' (fun j => Ga k (1 + r') (sc r' j) (Yx k r' x) ^ (-s (sc r' j) / 2)) (by omega : 1 + r' = r' + 1)]
  unfold Psi Dx
  have hP : ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)
      = (∏ l : Fin (r' + 1), Ga k (1 + r') (sc r' l) (Yx k r' x) ^ (-s (sc r' l) / 2)) *
        Ga k (1 + r') 0 (Yx k r' x) ^ (∑ l : Fin (r' + 1), s (sc r' l) / 2) := by
    rw [Real.rpow_sum_of_pos hG0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Real.div_rpow (hGl _) hG0.le, div_eq_mul_inv, ← Real.rpow_neg hG0.le]
    congr 2; ring
  have hD : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ (-(aw + 2)) = Ga k (1 + r') 0 (Yx k r' x) ^ (-(aw + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hG0.le]; congr 1; ring
  rw [hP, hD, mul_assoc, ← Real.rpow_add hG0, mul_comm]
  congr 2
  rw [← Finset.sum_div]; ring

end fin

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
