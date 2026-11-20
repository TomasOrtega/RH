import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.GaussJetProofs.MfactEqProdUniv
import Formalism.GaussJetBounds.GaussJetProofs.OneRow
import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets
import Formalism.GaussJetBounds.GaussJetProofs.GaussB

universe u

namespace Formalism.DworkPowerSeriesWeights

/- English proof (translation)
The claim follows from `matching_existence`.
-/
theorem matchings : Matchings.{u} := matching_existence
/- English proof (translation)
The claim follows from `pair_jet_bound`.
-/
theorem pairJet : PairJet.{u} := pair_jet_bound
/- English proof (translation)
Unfold `OneRowBasis`. Introduce `K _ _ N0 h0 x1 hx hx1`. Take `⟨a0, ha0⟩` from `hx1`. Use `set z : Fin N0 := ⟨0, h0⟩ with hz`. Establish `hu0 : x1 a0 ≠ 0`.

Introduce `h`. Rewrite `ha0` using `[h, norm_zero]`. Conclude with `zero_ne_one ha0`. Establish `huinv : ‖(x1 a0)⁻¹‖ = 1` using `by rw [norm_inv, ha0, inv_one]`. Set `σ : Equiv.Perm (Fin N0)` to `Equiv.swap z a0`.

Establish `hσz : σ z = a0` using `Equiv.swap_apply_left z a0`. Set `d : Fin N0 → K` to `fun a => if a = z then (x1 a0)⁻¹ else 1`. Set `e : Fin N0 → K` to `fun a => if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)`. Set `g : Matrix (Fin N0) (Fin N0) K` to `fun a b => (if a = b then d a else 0) + (if z = b then e a else 0)`. Establish `hd : ∀ a, ‖d a‖ ≤ 1`.

Introduce `a`. Use `show ‖(if a = z then (x1 a0)⁻¹ else 1)‖ ≤ 1`. Use `split_ifs`. Conclude with `huinv.le`. Simplify using the standard rewrite rules.

Establish `he : ∀ a, ‖e a‖ ≤ 1`. Introduce `a`. Use `show ‖(if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹))‖ ≤ 1`. Use `split_ifs`. Simplify using the standard rewrite rules.

Rewrite using `[norm_neg, norm_mul, huinv, mul_one]`. Conclude with `hx _`. Establish `hg : ∀ a b, ‖g a b‖ ≤ 1`. Introduce `a b`. Use `show ‖(if a = b then d a else 0) + (if z = b then e a else 0)‖ ≤ 1`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hd a`. Simplify using the standard rewrite rules. Use `split_ifs`.

Conclude with `he a`. Simplify using the standard rewrite rules. Establish `htri : g.BlockTriangular OrderDual.toDual`. Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`.

Establish `h2 : ¬ z = j`. Introduce `h`. Establish `h3 : (z : ℕ) = (j : ℕ)` using `congrArg Fin.val h`. Establish `h4 : (z : ℕ) = 0` using `by rw [hz]`. Establish `h5 : (i : ℕ) < (j : ℕ)` using `hij'`.

Use linear arithmetic over natural numbers and integers. Use `show (if i = j then d i else 0) + (if z = j then e i else 0) = 0`. Rewrite using `[if_neg (ne_of_lt hij'), if_neg h2, add_zero]`. Establish `hdet : ‖g.det‖ = 1`. Rewrite using `[Matrix.det_of_lowerTriangular g htri, norm_prod]`.

Use `Finset.prod_eq_one (fun i _ => ?_)` and prove the remaining obligations. Use `show ‖(if i = i then d i else 0) + (if z = i then e i else 0)‖ = 1`. Rewrite using `[if_pos (rfl : i = i)]`. Distinguish the cases in `hi : z = i`. Substitute `hi show ‖(if z = z then (x1 a0)⁻¹ else 1) + (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹))‖ = 1` using the available equality.

Rewrite using `[if_pos (rfl : z = z), if_pos (rfl : z = z), add_zero]`. Conclude with `huinv`. Rewrite using `[if_neg hi, add_zero] show ‖(if i = z then (x1 a0)⁻¹ else 1)‖ = 1`. Rewrite using `[if_neg (fun h => hi h.symm)]`. Simplify using the standard rewrite rules.

Use `⟨g.submatrix id σ, fun a a' => hg a (σ a'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_permute', norm_mul, hdet, mul_one]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Introduce `a`. Establish `hsum : (∑ a', x1 a' * (g.submatrix id σ) a a') = ∑ b, x1 (σ b) * g a b` using `Fintype.sum_equiv σ _ _ (fun a' => by simp [σ, Matrix.submatrix_apply])`.

Rewrite using `[hsum]`. Use `show (∑ b, x1 (σ b) * ((if a = b then d a else 0) + (if z = b then e a else 0))) = _`. Simplify using `only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Distinguish the cases in `ha : a = z`. Rewrite using `[if_pos ha, ha, hσz] show x1 a0 * (if z = z then (x1 a0)⁻¹ else 1) + x1 a0 * (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹)) = 1`.

Rewrite using `[if_pos (rfl : z = z), if_pos (rfl : z = z)]`. Take the linear combination `mul_inv_cancel₀ hu0`. Rewrite using `[if_neg ha, hσz] show x1 (σ a) * (if a = z then (x1 a0)⁻¹ else 1) + x1 a0 * (if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)) = 0`. Rewrite using `[if_neg ha, if_neg ha]`. Take the linear combination `(-x1 (σ a)) * mul_inv_cancel₀ hu0`.
-/
theorem oneRowBasis : OneRowBasis.{u} := by
  unfold OneRowBasis
  intro K _ _ N0 h0 x1 hx hx1
  obtain ⟨a0, ha0⟩ := hx1
  set z : Fin N0 := ⟨0, h0⟩ with hz
  have hu0 : x1 a0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha0
    exact zero_ne_one ha0
  have huinv : ‖(x1 a0)⁻¹‖ = 1 := by rw [norm_inv, ha0, inv_one]
  let σ : Equiv.Perm (Fin N0) := Equiv.swap z a0
  have hσz : σ z = a0 := Equiv.swap_apply_left z a0
  let d : Fin N0 → K := fun a => if a = z then (x1 a0)⁻¹ else 1
  let e : Fin N0 → K := fun a => if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)
  let g : Matrix (Fin N0) (Fin N0) K :=
    fun a b => (if a = b then d a else 0) + (if z = b then e a else 0)
  have hd : ∀ a, ‖d a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then (x1 a0)⁻¹ else 1)‖ ≤ 1
    split_ifs
    · exact huinv.le
    · simp
  have he : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹))‖ ≤ 1
    split_ifs
    · simp
    · rw [norm_neg, norm_mul, huinv, mul_one]
      exact hx _
  have hg : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    show ‖(if a = b then d a else 0) + (if z = b then e a else 0)‖ ≤ 1
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs
      · exact hd a
      · simp
    · split_ifs
      · exact he a
      · simp
  have htri : g.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have h2 : ¬ z = j := by
      intro h
      have h3 : (z : ℕ) = (j : ℕ) := congrArg Fin.val h
      have h4 : (z : ℕ) = 0 := by rw [hz]
      have h5 : (i : ℕ) < (j : ℕ) := hij'
      omega
    show (if i = j then d i else 0) + (if z = j then e i else 0) = 0
    rw [if_neg (ne_of_lt hij'), if_neg h2, add_zero]
  have hdet : ‖g.det‖ = 1 := by
    rw [Matrix.det_of_lowerTriangular g htri, norm_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    show ‖(if i = i then d i else 0) + (if z = i then e i else 0)‖ = 1
    rw [if_pos (rfl : i = i)]
    by_cases hi : z = i
    · subst hi
      show ‖(if z = z then (x1 a0)⁻¹ else 1) +
          (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹))‖ = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z), add_zero]
      exact huinv
    · rw [if_neg hi, add_zero]
      show ‖(if i = z then (x1 a0)⁻¹ else 1)‖ = 1
      rw [if_neg (fun h => hi h.symm)]
      simp
  refine ⟨g.submatrix id σ, fun a a' => hg a (σ a'), ?_, ?_⟩
  · rw [Matrix.det_permute', norm_mul, hdet, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro a
    have hsum : (∑ a', x1 a' * (g.submatrix id σ) a a') = ∑ b, x1 (σ b) * g a b :=
      Fintype.sum_equiv σ _ _ (fun a' => by simp [σ, Matrix.submatrix_apply])
    rw [hsum]
    show (∑ b, x1 (σ b) * ((if a = b then d a else 0) + (if z = b then e a else 0))) = _
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases ha : a = z
    · rw [if_pos ha, ha, hσz]
      show x1 a0 * (if z = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹)) = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z)]
      linear_combination mul_inv_cancel₀ hu0
    · rw [if_neg ha, hσz]
      show x1 (σ a) * (if a = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)) = 0
      rw [if_neg ha, if_neg ha]
      linear_combination (-x1 (σ a)) * mul_inv_cancel₀ hu0
/- English proof (translation)
The claim follows from `one_row_bound`.
-/
theorem oneRow : OneRow.{u} := one_row_bound
/- English proof (translation)
The claim follows from `theorem_B`.
-/
theorem thmB : ThmB.{u} := theorem_B
/- English proof (translation)
Unfold `SizesB`. Introduce `H _ _ TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'`. Establish `hf0 : 0 ≤ f`. Establish `: (0:ℝ) ≤ (Fintype.card H : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Prove the components needed by the constructor for the conclusion. Establish `h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0)`. Introduce `t`. Distinguish the cases in `ht : t ∈ TT`. Rewrite using `[if_pos ht]`.

Conclude with `hc2 t ht`. Rewrite using `[if_neg ht, add_zero]`. Conclude with `hc1 t ht`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]`.

Use `_ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by rw [hf]; ring`. Establish `hS0 : 0 ≤ ∑ t, min (wt t) (wt' t)` using `Finset.sum_nonneg (fun t _ => le_min (hw t).1 (hw' t))`. Establish `hS1 : ∑ t, min (wt t) (wt' t) ≤ f * b'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_le]`.

Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hS1), mul_nonneg hf0 hb', mul_nonneg (mul_nonneg hf0 hb') (by linarith : (0:ℝ) ≤ k + 1)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hk) hS0, mul_nonneg (mul_nonneg hf0 (by linarith : (0:ℝ) ≤ k)) hb']`.
-/
theorem sizesB : SizesB := by
  unfold SizesB
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0) := by
      intro t
      by_cases ht : t ∈ TT
      · rw [if_pos ht]; exact hc2 t ht
      · rw [if_neg ht, add_zero]; exact hc1 t ht
    calc (∑ t, c t) ≤ ∑ t, (4 * k * b' + (if t ∈ TT then 2 * b else 0)) :=
          Finset.sum_le_sum (fun t _ => h1 t)
      _ = (Fintype.card H : ℝ) * (4 * k * b') + (TT.card : ℝ) * (2 * b) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
      _ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by rw [hf]; ring
  · have hS0 : 0 ≤ ∑ t, min (wt t) (wt' t) :=
      Finset.sum_nonneg (fun t _ => le_min (hw t).1 (hw' t))
    have hS1 : ∑ t, min (wt t) (wt' t) ≤ f * b' := by
      calc ∑ t, min (wt t) (wt' t) ≤ ∑ _t : H, 2 * b' :=
            Finset.sum_le_sum (fun t _ => (min_le_left _ _).trans (hw t).2)
        _ = f * b' := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hf]; ring
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hS1), mul_nonneg hf0 hb',
        mul_nonneg (mul_nonneg hf0 hb') (by linarith : (0:ℝ) ≤ k + 1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) hS0,
        mul_nonneg (mul_nonneg hf0 (by linarith : (0:ℝ) ≤ k)) hb']
/- English proof (translation)
Unfold `IntOp`. Introduce `K _ _ ι Th hTh P hP`. Unfold `jetPair`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations. Introduce `κ _`.

Rewrite using `[mul_assoc, norm_mul]`. Conclude with `mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)`.
-/
theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)
/- English proof (translation)
Unfold `polar`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_one₀ (hc x y) (norm_nonneg _) ?_` and prove the remaining obligations.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)`.
-/
private theorem norm_polar_le_one_of_norm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] (c : ι → ι → K) (L L' : ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ 1) (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by
  unfold polar
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun y _ => ?_)
  rw [norm_mul]
  refine mul_le_one₀ (hc x y) (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)
  · rw [norm_mul]; exact mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `m`. Rewrite using `[Finset.prod_empty, MvPolynomial.coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `@insert a s ha ih`. Introduce `m`. Rewrite using `[Finset.prod_insert ha, MvPolynomial.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `mul_le_one₀ ?_ (norm_nonneg _) (ih p.2)` and prove the remaining obligations. Unfold `linForm`. Rewrite using `[MvPolynomial.coeff_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', norm_mul]`.

Use `mul_le_one₀ (hL a x) (norm_nonneg _) ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem norm_coeff_prod_linForm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] {n : ℕ} (L : Fin n → ι → K) (hL : ∀ i x, ‖L i x‖ ≤ 1)
    (s : Finset (Fin n)) : ∀ m, ‖MvPolynomial.coeff m (∏ i ∈ s, linForm (L i))‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Finset.prod_empty, MvPolynomial.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    intro m
    rw [Finset.prod_insert ha, MvPolynomial.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun p _ => ?_)
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ih p.2)
    unfold linForm
    rw [MvPolynomial.coeff_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', norm_mul]
    refine mul_le_one₀ (hL a x) (norm_nonneg _) ?_
    split_ifs <;> simp

/- English proof (translation)
Unfold `MatchBound`. Introduce `K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM`. Establish `hm : Matchings.{u}` using `matchings`. Unfold `Matchings at hm`. Establish `hI : IntOp.{u}` using `intOp`.

Unfold `IntOp at hI`. Rewrite using `[hm K ι c S sg n L]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _) ?_` and prove the remaining obligations. Introduce `σ hσ`. Rewrite `hσ` using `[Finset.mem_filter]`.

Distinguish the cases in `hz : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0`. Establish `hcard` using `hM σ hσ.2 hz`. Rewrite using `[norm_mul, norm_prod]`. Establish `hJ` using `hI K ι sg hsg _ (norm_coeff_prod_linForm_le_one L hL (Finset.univ.filter (fun i => σ i = i)))`. Establish `hP : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖ ≤ pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ))`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_neg]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by`.

Rewrite using `[Finset.prod_const, Real.rpow_mul hpi0.le, Real.rpow_natCast]`. Establish `hmono : pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) ≤ pi ^ (-(1 / 2 : ℝ) * (M : ℝ))`. Apply `Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le` to reduce the goal to its premises. Establish `: ((Finset.univ.filter (fun i => i < σ i)).card : ℝ) ≤ (M : ℝ)`. Conclude with `hcard` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(mul_le_mul hP hJ (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)).trans ?_` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `hmono`. Use `push_neg at hz`.

Take `⟨i, hi, hpol⟩` from `hz`. Establish `h0 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) = 0` using `Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by rw [hpol, mul_zero])`. Rewrite using `[h0, zero_mul, norm_zero]`. Conclude with `Real.rpow_nonneg hpi0.le _`.
-/
theorem matchBound : MatchBound.{u} := by
  unfold MatchBound
  intro K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM
  have hm : Matchings.{u} := matchings
  unfold Matchings at hm
  have hI : IntOp.{u} := intOp
  unfold IntOp at hI
  rw [hm K ι c S sg n L]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _) ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ
  by_cases hz : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0
  · have hcard := hM σ hσ.2 hz
    rw [norm_mul, norm_prod]
    have hJ := hI K ι sg hsg _
      (norm_coeff_prod_linForm_le_one L hL (Finset.univ.filter (fun i => σ i = i)))
    have hP : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
      calc ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖
          ≤ ∏ _i ∈ Finset.univ.filter (fun i => i < σ i), pi ^ (-(1 / 2 : ℝ)) := by
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
            rw [norm_mul, norm_neg]
            calc ‖S‖ * ‖polar c (L i) (L (σ i))‖ ≤ ‖S‖ * 1 :=
                  mul_le_mul_of_nonneg_left
                    (norm_polar_le_one_of_norm_le_one c (L i) (L (σ i)) hc (hL i) (hL (σ i))) (norm_nonneg _)
              _ ≤ pi ^ (-(1 / 2 : ℝ)) := by rw [mul_one]; exact hS
        _ = pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
            rw [Finset.prod_const, Real.rpow_mul hpi0.le, Real.rpow_natCast]
    have hmono : pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) ≤
        pi ^ (-(1 / 2 : ℝ) * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le
      have : ((Finset.univ.filter (fun i => i < σ i)).card : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hcard
      linarith
    refine (mul_le_mul hP hJ (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)).trans ?_
    rw [mul_one]
    exact hmono
  · push_neg at hz
    obtain ⟨i, hi, hpol⟩ := hz
    have h0 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by rw [hpol, mul_zero])
    rw [h0, zero_mul, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
/- English proof (translation)
Unfold `SizesE`. Introduce `H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hw hw'`. Establish `hB : SizesB` using `sizesB`. Unfold `SizesB at hB`. Take `⟨hsum, habs⟩` from `hB H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'`.

Establish `hf0 : 0 ≤ f`. Establish `: (0:ℝ) ≤ (Fintype.card H : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC0 : 0 ≤ ∑ t, c t` using `Finset.sum_nonneg (fun t _ => hc0 t)`. Establish `hT0 : (0:ℝ) ≤ (TT.card : ℝ) * b` using `mul_nonneg (Nat.cast_nonneg _) hb`.

Establish `hF0 : 0 ≤ f * k * b'` using `mul_nonneg (mul_nonneg hf0 (by linarith)) hb'`. Rewrite `habs`, the goal using `[abs_le]`. Take `⟨h1, h2⟩` from `habs`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem sizesE : SizesE := by
  unfold SizesE
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hw hw'
  have hB : SizesB := sizesB
  unfold SizesB at hB
  obtain ⟨hsum, habs⟩ := hB H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  have hC0 : 0 ≤ ∑ t, c t := Finset.sum_nonneg (fun t _ => hc0 t)
  have hT0 : (0:ℝ) ≤ (TT.card : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
  have hF0 : 0 ≤ f * k * b' := mul_nonneg (mul_nonneg hf0 (by linarith)) hb'
  rw [abs_le] at habs ⊢
  obtain ⟨h1, h2⟩ := habs
  constructor <;> linarith
/- English proof (translation)
The claim follows from `theorem_B_gauss_sums`.
-/
theorem thmBGauss : ThmBGauss := theorem_B_gauss_sums

end Formalism.DworkPowerSeriesWeights
