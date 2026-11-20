import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

/- English proof (translation)
Establish `hpos : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ)` using `by positivity`. Rewrite using `[Int.fdiv_eq_ediv_of_nonneg _ hpos.le]`. Establish `h1` using `Int.ediv_mul_le x hpos.ne'`. Generalize the expression as in `x / ((T + d + 2 : ℕ) : ℤ) = q at h1`. Break down `le_or_gt q 0 with hq | hq` into its components or cases.

Rewrite using `[Int.toNat_eq_zero.2 hq]`. Simplify using `using hc`. Rewrite using `[Int.toNat_of_nonneg hq.le]`. Move the coercions through the operations in `at h1`. Establish `hd : (0 : ℤ) ≤ d` using `by positivity`.

Use polynomial arithmetic with `[mul_nonneg hq.le hd]`.
-/
theorem mul_toNat_fdiv_le (T d : ℕ) (c x : ℤ) (hc : 0 ≤ c) (hx : x ≤ c + 2) :
    (T : ℤ) * ((Int.fdiv x ((T + d + 2 : ℕ) : ℤ)).toNat : ℤ) ≤ c := by
  have hpos : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ) := by positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hpos.le]
  have h1 := Int.ediv_mul_le x hpos.ne'
  generalize x / ((T + d + 2 : ℕ) : ℤ) = q at h1
  rcases le_or_gt q 0 with hq | hq
  · rw [Int.toNat_eq_zero.2 hq]; simpa using hc
  · rw [Int.toNat_of_nonneg hq.le]
    push_cast at h1
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith [mul_nonneg hq.le hd]

/- English proof (translation)
Unfold `WeightAlgebra.gapZ`. Use `split_ifs with h`. Establish `: a ⟨i.1 + 1, h⟩ ≤ a i` using `ha (by simp [Fin.le_def])`. Use linear arithmetic over natural numbers and integers. Check the signs of the components of the expression.
-/
theorem gapZ_nonneg_of_antitone {p : ℕ} {a : Fin p → ℕ} (ha : Antitone a) (i : Fin p) :
    0 ≤ WeightAlgebra.gapZ a i := by
  unfold WeightAlgebra.gapZ
  split_ifs with h
  · have : a ⟨i.1 + 1, h⟩ ≤ a i := ha (by simp [Fin.le_def])
    omega
  · positivity

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ i : Fin p, i.1 + n + 1 = p → T * ofGaps g i ≤ a i`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `i hi`.

Establish `hn : ¬ i.1 + 1 < p` using `by omega`. Establish `h1` using `h i`. Rewrite using `[ofGaps_last g i hn]`. Unfold `WeightAlgebra.gapZ at h1`. Rewrite `h1` using `[dif_neg hn]`.

Conclude with `h1` after adjusting the coercions. Consider the case `succ n ih`. Introduce `i hi`. Establish `hn : i.1 + 1 < p` using `by omega`. Establish `h1` using `h i`.

Establish `h2` using `ih ⟨i.1 + 1, hn⟩ (by simp only; omega)`. Rewrite using `[ofGaps_succ g i hn, Nat.mul_add]`. Unfold `WeightAlgebra.gapZ at h1`. Rewrite `h1` using `[dif_pos hn]`. Establish `h3 : ((T * g i : ℕ) : ℤ) ≤ (a i : ℤ) - a ⟨i.1 + 1, hn⟩` using `by push_cast; exact h1`.

Use linear arithmetic over natural numbers and integers. Conclude with `key (p - 1 - i.1) i (by have := i.2; omega)`.
-/
theorem mul_ofGaps_le {p : ℕ} (T : ℕ) (g a : Fin p → ℕ)
    (h : ∀ i, (T : ℤ) * (g i : ℤ) ≤ WeightAlgebra.gapZ a i) (i : Fin p) : T * ofGaps g i ≤ a i := by
  have key : ∀ n : ℕ, ∀ i : Fin p, i.1 + n + 1 = p → T * ofGaps g i ≤ a i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hn : ¬ i.1 + 1 < p := by omega
      have h1 := h i
      rw [ofGaps_last g i hn]
      unfold WeightAlgebra.gapZ at h1
      rw [dif_neg hn] at h1
      exact_mod_cast h1
    | succ n ih =>
      intro i hi
      have hn : i.1 + 1 < p := by omega
      have h1 := h i
      have h2 := ih ⟨i.1 + 1, hn⟩ (by simp only; omega)
      rw [ofGaps_succ g i hn, Nat.mul_add]
      unfold WeightAlgebra.gapZ at h1
      rw [dif_pos hn] at h1
      have h3 : ((T * g i : ℕ) : ℤ) ≤ (a i : ℤ) - a ⟨i.1 + 1, hn⟩ := by push_cast; exact h1
      omega
  exact key (p - 1 - i.1) i (by have := i.2; omega)

/- English proof (translation)
Use `mul_ofGaps_le T (lGapP D ka T nW τ) (ka.aP τ) (fun i => ?_) i` and prove the remaining obligations. Establish `h0` using `gapZ_nonneg_of_antitone (ka.aPlus_antitone τ) i`. Unfold `lGapP WeightAlgebra.Tp`. Use `split_ifs with h`. Conclude with `mul_toNat_fdiv_le _ _ _ _ h0 le_rfl`.

Use `mul_toNat_fdiv_le _ _ _ _ h0 ?_` and prove the remaining obligations. Unfold `WeightAlgebra.gapZ`. Rewrite using `[dif_neg h]`. Establish `: (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW` using `by positivity`. Establish `: (0 : ℤ) ≤ (D.R.r : ℤ)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_lWt_aP_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : T * (lWt D ka T nW hW).aP τ i ≤ ka.aP τ i := by
  refine mul_ofGaps_le T (lGapP D ka T nW τ) (ka.aP τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aPlus_antitone τ) i
  unfold lGapP WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    have : (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW := by positivity
    have : (0 : ℤ) ≤ (D.R.r : ℤ) := by positivity
    linarith

/- English proof (translation)
Use `mul_ofGaps_le T (lGapM D ka T τ) (ka.aM τ) (fun i => ?_) i` and prove the remaining obligations. Establish `h0` using `gapZ_nonneg_of_antitone (ka.aM_anti τ) i`. Unfold `lGapM WeightAlgebra.Tp`. Use `split_ifs with h`. Conclude with `mul_toNat_fdiv_le _ _ _ _ h0 le_rfl`.

Use `mul_toNat_fdiv_le _ _ _ _ h0 ?_` and prove the remaining obligations. Unfold `WeightAlgebra.gapZ`. Rewrite using `[dif_neg h]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_lWt_aM_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) : T * (lWt D ka T nW hW).aM τ i ≤ ka.aM τ i := by
  refine mul_ofGaps_le T (lGapM D ka T τ) (ka.aM τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aM_anti τ) i
  unfold lGapM WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    linarith

/- English proof (translation)
Unfold `WeightAlgebra.DF WeightAlgebra.degP`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.mul_add, Finset.mul_sum, Finset.mul_sum]`. Conclude with `Nat.add_le_add (Finset.sum_le_sum fun i _ => mul_lWt_aP_le D ka T nW hW τ i) (Finset.sum_le_sum fun i _ => mul_lWt_aM_le D ka T nW hW τ i)`.
-/
theorem mul_DF_lWt_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) :
    T * WeightAlgebra.DF (lWt D ka T nW hW) ≤ WeightAlgebra.DF ka := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
  exact Nat.add_le_add (Finset.sum_le_sum fun i _ => mul_lWt_aP_le D ka T nW hW τ i)
    (Finset.sum_le_sum fun i _ => mul_lWt_aM_le D ka T nW hW τ i)

/- English proof (translation)
Introduce `D L Pm Tp hK j τ`. Conclude with `⟨fun i => mul_lWt_aP_le D _ _ _ _ τ i, fun i => mul_lWt_aM_le D _ _ _ _ τ i, mul_DF_lWt_le D _ _ _ _⟩`.
-/
theorem mul_rows_lR_le_kaR : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ) (τ : D.what₂.Tau), (∀ i, Tp.TO * (lR Tp hK j).aP τ i ≤ (kaR Tp hK j).aP τ i) ∧ (∀ i, Tp.TO * (lR Tp hK j).aM τ i ≤ (kaR Tp hK j).aM τ i) ∧ Tp.TO * WeightAlgebra.DF (lR Tp hK j) ≤ WeightAlgebra.DF (kaR Tp hK j) := by
  intro D L Pm Tp hK j τ
  exact ⟨fun i => mul_lWt_aP_le D _ _ _ _ τ i, fun i => mul_lWt_aM_le D _ _ _ _ τ i,
    mul_DF_lWt_le D _ _ _ _⟩

end GlobalTheory.RunDepth
