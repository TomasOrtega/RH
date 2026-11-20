import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.WindowsAllowOffCentre

noncomputable section

namespace GlobalTheory.RunNuTest

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.Cons NumberField IsDedekindDomain

/- English proof (translation)
Establish `hp : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ)` using `by positivity`. Rewrite using `[Int.fdiv_eq_ediv_of_nonneg _ hp.le]`. Establish `h1` using `Int.ediv_mul_le x hp.ne'`. Use `set k := x / ((T + d + 2 : ℕ) : ℤ)`. Break down `le_or_gt k 0 with hk | hk` into its components or cases.

Rewrite using `[Int.toNat_of_nonpos hk]`. Simplify using `using hc`. Rewrite using `[Int.toNat_of_nonneg hk.le]`. Move the coercions through the operations in `at h1`. Establish `hd : (0 : ℤ) ≤ d` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem floor_le (T d : ℕ) (c x : ℤ) (hc : 0 ≤ c) (hx : x ≤ c + 2) :
    (T : ℤ) * ((Int.fdiv x ((T + d + 2 : ℕ) : ℤ)).toNat : ℤ) ≤ c := by
  have hp : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ) := by positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 := Int.ediv_mul_le x hp.ne'
  set k := x / ((T + d + 2 : ℕ) : ℤ)
  rcases le_or_gt k 0 with hk | hk
  · rw [Int.toNat_of_nonpos hk]; simpa using hc
  · rw [Int.toNat_of_nonneg hk.le]
    push_cast at h1
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith

/- English proof (translation)
Unfold `WeightAlgebra.gapZ`. Use `split_ifs with hi`. Establish `: l ⟨i.1 + 1, hi⟩ ≤ l i` using `h (by simp [Fin.le_def])`. Use linear arithmetic over natural numbers and integers. Check the signs of the components of the expression.
-/
theorem gap_nonneg {p : ℕ} {l : Fin p → ℕ} (h : Antitone l) (i : Fin p) : 0 ≤ WeightAlgebra.gapZ l i := by
  unfold WeightAlgebra.gapZ
  split_ifs with hi
  · have : l ⟨i.1 + 1, hi⟩ ≤ l i := h (by simp [Fin.le_def])
    omega
  · positivity

/- English proof (translation)
Establish `key : ∀ n (i : Fin p), p - i.1 = n + 1 → (u i : ℤ) = a i - T * b i`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `i hi`.

Use `h i` as an intermediate fact. Establish `hn : ¬ i.1 + 1 < p` using `by omega`. Simplify `this` using `[WeightAlgebra.gapZ, hn]`. Consider the case `succ n ih`. Introduce `i hi`.

Use `h i` as an intermediate fact. Establish `hn : i.1 + 1 < p` using `by omega`. Establish `e` using `ih ⟨i.1 + 1, hn⟩ (by show p - (i.1 + 1) = n + 1; omega)`. Simplify using `only [WeightAlgebra.gapZ, dif_pos hn] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i`. Conclude with `key (p - i.1 - 1) i (by have := i.2; omega)`.
-/
theorem of_gaps {p : ℕ} (u a b : Fin p → ℕ) (T : ℤ) (h : ∀ i, WeightAlgebra.gapZ u i = WeightAlgebra.gapZ a i - T * WeightAlgebra.gapZ b i) :
    ∀ i, (u i : ℤ) = a i - T * b i := by
  have key : ∀ n (i : Fin p), p - i.1 = n + 1 → (u i : ℤ) = a i - T * b i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have := h i
      have hn : ¬ i.1 + 1 < p := by omega
      simpa [WeightAlgebra.gapZ, hn] using this
    | succ n ih =>
      intro i hi
      have := h i
      have hn : i.1 + 1 < p := by omega
      have e := ih ⟨i.1 + 1, hn⟩ (by show p - (i.1 + 1) = n + 1; omega)
      simp only [WeightAlgebra.gapZ, dif_pos hn] at this
      linarith
  intro i
  exact key (p - i.1 - 1) i (by have := i.2; omega)

variable {D : D7} {j : ℕ}

/- English proof (translation)
Use `⟨rfl, fun τ => of_gaps _ _ _ _ fun i => ?_, fun τ => of_gaps _ _ _ _ fun i => ?_⟩` and prove the remaining obligations. Use `show WeightAlgebra.gapZ (ofGaps _) i = _ - _ * WeightAlgebra.gapZ (ofGaps _) i`. Rewrite using `[gapZ_ofGaps, gapZ_ofGaps]`. Unfold `fGapP`. Use `split_ifs with hi`.

Use `show (((WeightAlgebra.gapZ _ i - _ * WeightAlgebra.gapZ (ofGaps _) i).toNat : ℕ) : ℤ) = _`. Rewrite using `[gapZ_ofGaps]`. Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Unfold `lGapP`. Rewrite using `[if_pos hi]`.

Conclude with `sub_nonneg.2 (floor_le T _ _ _ (gap_nonneg (ka.aPlus_antitone τ) i) le_rfl)`. Use `show ((((ka.aP τ i : ℤ) - _ * ((ofGaps _ i : ℕ) : ℤ)).toNat : ℕ) : ℤ) = _`. Rewrite using `[ofGaps_last _ i hi]`. Establish `e : WeightAlgebra.gapZ (ka.aP τ) i = ka.aP τ i` using `by simp [WeightAlgebra.gapZ, hi]`. Rewrite using `[e]`.

Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Unfold `lGapP`. Rewrite using `[if_neg hi]`. Use `sub_nonneg.2 (floor_le T _ _ _ (by positivity) ?_)` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW` using `by positivity`.

Establish `: (0 : ℤ) ≤ D.R.r` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show WeightAlgebra.gapZ (ofGaps _) i = _ - _ * WeightAlgebra.gapZ (ofGaps _) i`. Rewrite using `[gapZ_ofGaps, gapZ_ofGaps]`. Unfold `fGapM`.

Use `split_ifs with hi`. Use `show (((WeightAlgebra.gapZ _ i - _ * WeightAlgebra.gapZ (ofGaps _) i).toNat : ℕ) : ℤ) = _`. Rewrite using `[gapZ_ofGaps]`. Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Unfold `lGapM`.

Rewrite using `[if_pos hi]`. Conclude with `sub_nonneg.2 (floor_le T _ _ _ (gap_nonneg (ka.aM_anti τ) i) le_rfl)`. Use `show ((((ka.aM τ i : ℤ) - _ * ((ofGaps _ i : ℕ) : ℤ)).toNat : ℕ) : ℤ) = _`. Rewrite using `[ofGaps_last _ i hi]`. Establish `e : WeightAlgebra.gapZ (ka.aM τ) i = ka.aM τ i` using `by simp [WeightAlgebra.gapZ, hi]`.

Rewrite using `[e]`. Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Unfold `lGapM`. Rewrite using `[if_neg hi]`. Conclude with `sub_nonneg.2 (floor_le T _ _ _ (by positivity) (by linarith))`.
-/
theorem isF (ka : WeightFamilies.Wt D j) (T nW nP : ℕ) (hW : Even nW) (hP : Even nP) :
    WeightAlgebra.IsF' ka (lWt D ka T nW hW) (fWt D ka (lWt D ka T nW hW) T nP hP) T nP := by
  refine ⟨rfl, fun τ => of_gaps _ _ _ _ fun i => ?_, fun τ => of_gaps _ _ _ _ fun i => ?_⟩
  · show WeightAlgebra.gapZ (ofGaps _) i = _ - _ * WeightAlgebra.gapZ (ofGaps _) i
    rw [gapZ_ofGaps, gapZ_ofGaps]
    unfold fGapP
    split_ifs with hi
    · show (((WeightAlgebra.gapZ _ i - _ * WeightAlgebra.gapZ (ofGaps _) i).toNat : ℕ) : ℤ) = _
      rw [gapZ_ofGaps]
      apply Int.toNat_of_nonneg
      unfold lGapP; rw [if_pos hi]
      exact sub_nonneg.2 (floor_le T _ _ _ (gap_nonneg (ka.aPlus_antitone τ) i) le_rfl)
    · show ((((ka.aP τ i : ℤ) - _ * ((ofGaps _ i : ℕ) : ℤ)).toNat : ℕ) : ℤ) = _
      rw [ofGaps_last _ i hi]
      have e : WeightAlgebra.gapZ (ka.aP τ) i = ka.aP τ i := by simp [WeightAlgebra.gapZ, hi]
      rw [e]
      apply Int.toNat_of_nonneg
      unfold lGapP; rw [if_neg hi]
      refine sub_nonneg.2 (floor_le T _ _ _ (by positivity) ?_)
      have : (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW := by positivity
      have : (0 : ℤ) ≤ D.R.r := by positivity
      linarith
  · show WeightAlgebra.gapZ (ofGaps _) i = _ - _ * WeightAlgebra.gapZ (ofGaps _) i
    rw [gapZ_ofGaps, gapZ_ofGaps]
    unfold fGapM
    split_ifs with hi
    · show (((WeightAlgebra.gapZ _ i - _ * WeightAlgebra.gapZ (ofGaps _) i).toNat : ℕ) : ℤ) = _
      rw [gapZ_ofGaps]
      apply Int.toNat_of_nonneg
      unfold lGapM; rw [if_pos hi]
      exact sub_nonneg.2 (floor_le T _ _ _ (gap_nonneg (ka.aM_anti τ) i) le_rfl)
    · show ((((ka.aM τ i : ℤ) - _ * ((ofGaps _ i : ℕ) : ℤ)).toNat : ℕ) : ℤ) = _
      rw [ofGaps_last _ i hi]
      have e : WeightAlgebra.gapZ (ka.aM τ) i = ka.aM τ i := by simp [WeightAlgebra.gapZ, hi]
      rw [e]
      apply Int.toNat_of_nonneg
      unfold lGapM; rw [if_neg hi]
      exact sub_nonneg.2 (floor_le T _ _ _ (by positivity) (by linarith))

/- English proof (translation)
Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Rewrite using `[Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]`. Conclude with `Int.ediv_nonneg hx (by positivity)`.
-/
theorem fdiv_toNat (x : ℤ) (n : ℕ) (hx : 0 ≤ x) : (((Int.fdiv x n).toNat : ℕ) : ℤ) = Int.fdiv x n := by
  apply Int.toNat_of_nonneg
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]
  exact Int.ediv_nonneg hx (by positivity)

/- English proof (translation)
Use `⟨rfl, fun τ i => ?_, fun τ i => ?_⟩` and prove the remaining obligations. Use `show WeightAlgebra.gapZ (ofGaps _) i = _`. Rewrite using `[gapZ_ofGaps]`. Unfold `lGapP`. Use `split_ifs with hi`.

Conclude with `fdiv_toNat _ _ (by have := gap_nonneg (ka.aPlus_antitone τ) i; omega)`. Use `fdiv_toNat _ _ ?_` and prove the remaining obligations. Use `h τ i hi` as an intermediate fact. Use `zify at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show WeightAlgebra.gapZ (ofGaps _) i = _`. Rewrite using `[gapZ_ofGaps]`. Unfold `lGapM`. Use `split_ifs with hi`. Conclude with `fdiv_toNat _ _ (by have := gap_nonneg (ka.aM_anti τ) i; omega)`.

Conclude with `fdiv_toNat _ _ (by positivity)`.
-/
theorem isL (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW)
    (h : ∀ τ (i : Fin (D.R.sigW j).1), ¬ i.1 + 1 < (D.R.sigW j).1 → (WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r ≤ ka.aP τ i) :
    WeightAlgebra.IsL D ka (lWt D ka T nW hW) T nW := by
  refine ⟨rfl, fun τ i => ?_, fun τ i => ?_⟩
  · show WeightAlgebra.gapZ (ofGaps _) i = _
    rw [gapZ_ofGaps]; unfold lGapP
    split_ifs with hi
    · exact fdiv_toNat _ _ (by have := gap_nonneg (ka.aPlus_antitone τ) i; omega)
    · refine fdiv_toNat _ _ ?_
      have := h τ i hi
      zify at this
      linarith
  · show WeightAlgebra.gapZ (ofGaps _) i = _
    rw [gapZ_ofGaps]; unfold lGapM
    split_ifs with hi
    · exact fdiv_toNat _ _ (by have := gap_nonneg (ka.aM_anti τ) i; omega)
    · exact fdiv_toNat _ _ (by positivity)

/- English proof (translation)
Rewrite using `[← Nat.choose_two_right, ← Nat.choose_two_right]`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, Nat.choose_one_right, Nat.choose_one_right]`.

Simplify using `only [Nat.reduceAdd]`. Rewrite using `[← ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem choose_two_add (p q : ℕ) : p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, Nat.choose_one_right, Nat.choose_one_right]
    simp only [Nat.reduceAdd]
    rw [← ih]; ring

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Rewrite using `[T.Dp_eq]`. Unfold `WeightFamilies.dimY`. Rewrite using `[choose_two_add]`. Use `congr 2`. Use `show D.R.k + j - 1 + (D.R.m - j) = D.R.r`.

Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_eq (T : ParamsT D L P) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WeightFamilies.dimY D j = T.Dp := by
  rw [T.Dp_eq]; unfold WeightFamilies.dimY
  rw [choose_two_add]
  congr 2
  show D.R.k + j - 1 + (D.R.m - j) = D.R.r
  unfold Ranks.r; omega

/- English proof (translation)
Take `⟨a, b, c⟩` from `GlobalTheory.RunCounterexample.clauses_at_shifted_gap T hK h1 h2`. Establish `hP : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * T.TO ^ 2 ≤ (kaR T hK j).aP τ i`. Introduce `τ i hi`. Use `b τ i hi` as an intermediate fact. Establish `: (2 * (T.TO : ℝ) ^ 2) ≤ ((kaR T hK j).aP τ i : ℝ)` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hw` using `T.nW_lo.2.1`. Use `⟨kaWt_n _ _ _ _, T.split, isL _ _ _ _ fun τ i hi => ?_, isF _ _ _ _ _ _, by omega, by omega, hP, fun τ i hi => ?_⟩` and prove the remaining obligations. Use `hP τ i (by have := i.2; omega)` as an intermediate fact. Establish `h3` using `T.TO_nW`.

Rewrite using `[dim_eq T h1 h2]`. Use the polynomial consequences of the given equalities and inequalities. Use `c τ i hi` as an intermediate fact. Establish `: (2 * (T.TO : ℝ) ^ 2) ≤ ((kaR T hK j).aM τ i : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem weights (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (kaR T hK j).n = D.R.nV ∧ D.R.nV = T.nP + T.TO * T.nWn ∧ WeightAlgebra.IsL D (kaR T hK j) (lR T hK j) T.TO T.nWn ∧
      WeightAlgebra.IsF' (kaR T hK j) (lR T hK j) (fR T hK j) T.TO T.nP ∧
      T.nWn = D.R.r + (T.nWn - D.R.r) ∧ D.R.r ≤ T.nWn - D.R.r ∧
      (∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * T.TO ^ 2 ≤ (kaR T hK j).aP τ i) ∧
      (∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 → 2 * T.TO ^ 2 ≤ (kaR T hK j).aM τ i) := by
  obtain ⟨a, b, c⟩ := GlobalTheory.RunCounterexample.clauses_at_shifted_gap T hK h1 h2
  have hP : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * T.TO ^ 2 ≤ (kaR T hK j).aP τ i := by
    intro τ i hi
    have := b τ i hi
    have : (2 * (T.TO : ℝ) ^ 2) ≤ ((kaR T hK j).aP τ i : ℝ) := by linarith
    exact_mod_cast this
  have hw := T.nW_lo.2.1
  refine ⟨kaWt_n _ _ _ _, T.split, isL _ _ _ _ fun τ i hi => ?_, isF _ _ _ _ _ _, by omega, by omega, hP, fun τ i hi => ?_⟩
  · have := hP τ i (by have := i.2; omega)
    have h3 := T.TO_nW
    rw [dim_eq T h1 h2]
    nlinarith
  · have := c τ i hi
    have : (2 * (T.TO : ℝ) ^ 2) ≤ ((kaR T hK j).aM τ i : ℝ) := by linarith
    exact_mod_cast this

variable (B : WeightFamilies.Prov D)

end GlobalTheory.RunNuTest
