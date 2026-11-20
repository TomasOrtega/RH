import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.PrimalPlace

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.TwSMInt2

open MomentRationality MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
Rewrite using `[q_actL]`. Use `set v := gi g *ᵥ toL y with hv`. Establish `hv0 : v ≠ 0` using `gi_ne g hy`. Establish `hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty`. Assume the negation of the conclusion as `hcon`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hi`. Conclude with `hcon ⟨i, by simpa using hi⟩`. Establish `hi0mem : v ((Finset.univ.filter fun i => v i ≠ 0).max' hne) ≠ 0`.

Use `Finset.max'_mem _ hne` as an intermediate fact. Simplify using `using this`. Use `set i0 := (Finset.univ.filter fun i => v i ≠ 0).max' hne with hi0`. Establish `hzero : ∀ j, i0 < j → v j = 0`. Introduce `j hj`.

Assume the negation of the conclusion as `hjne`. Establish `: j ≤ i0` using `Finset.le_max' _ j (by simpa using hjne)`. Conclude with `absurd hj (not_lt.mpr this)`. Establish `hplace` using `fun w => primal_place hN hc hp hs hk y hzero w`. Use `set Z := ∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1 with hZdef`.

Establish `hZ : 0 < Z` using `by positivity`. Establish `hsum` using `sum_sq_ge hL hd hi0mem (int_d hdi y i0)`. Establish `he : Real.exp (-s imax) ≤ Real.exp (-s i0)` using `Real.exp_le_exp.mpr (by linarith [himax i0])`. Establish `hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 ≤ ∑ i, ‖(MomentRationality.mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2`. Introduce `w`.

Use `le_trans ?_ (hplace w)` and prove the remaining obligations. Establish `hzpos : 0 < ‖z w‖` using `norm_pos_iff.mpr (z_ne hN hc w)`. Establish `hzle : ‖z w‖ ^ 2 ≤ Z`. Use `Finset.single_le_sum (f := fun w => ‖z w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hZinv : Z⁻¹ ≤ (‖z w‖⁻¹) ^ 2`. Rewrite using `[inv_pow]`. Conclude with `inv_anti₀ (by positivity) hzle`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ _ := Finset.sum_le_sum fun w _ => hterm w`.
-/
theorem primal_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imax : Fin N} (himax : ∀ i, s i ≤ s imax) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2 ≤
      q (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1) y := by
  classical
  rw [q_actL]
  set v := gi g *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gi_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi0mem : v ((Finset.univ.filter fun i => v i ≠ 0).max' hne) ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  set i0 := (Finset.univ.filter fun i => v i ≠ 0).max' hne with hi0
  have hzero : ∀ j, i0 < j → v j = 0 := by
    intro j hj
    by_contra hjne
    have : j ≤ i0 := Finset.le_max' _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => primal_place hN hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi0mem (int_d hdi y i0)
  have he : Real.exp (-s imax) ≤ Real.exp (-s i0) := Real.exp_le_exp.mpr (by linarith [himax i0])
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 ≤
      ∑ i, ‖(MomentRationality.mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ (‖z w‖⁻¹) ^ 2 := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) hzle
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * (‖z w‖⁻¹) ^ 2 * Real.exp (-s i0) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i0)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

/- English proof (translation)
Rewrite using `[q_dual]`. Use `set v := (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y with hv`. Establish `hv0 : v ≠ 0` using `gT_ne g hy`. Establish `hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty`. Assume the negation of the conclusion as `hcon`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hi`. Conclude with `hcon ⟨i, by simpa using hi⟩`. Establish `hi1mem : v ((Finset.univ.filter fun i => v i ≠ 0).min' hne) ≠ 0`.

Use `Finset.min'_mem _ hne` as an intermediate fact. Simplify using `using this`. Use `set i1 := (Finset.univ.filter fun i => v i ≠ 0).min' hne with hi1`. Establish `hzero : ∀ j, j < i1 → v j = 0`. Introduce `j hj`.

Assume the negation of the conclusion as `hjne`. Establish `: i1 ≤ j` using `Finset.min'_le _ j (by simpa using hjne)`. Conclude with `absurd hj (not_lt.mpr this)`. Establish `hplace` using `fun w => dual_place hc hp hs hk y hzero w`. Use `set Z := ∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1 with hZdef`.

Establish `hZ : 0 < Z` using `by positivity`. Establish `hsum` using `sum_sq_ge hL hd hi1mem (int_d hdg y i1)`. Establish `he : Real.exp (s imin) ≤ Real.exp (s i1)` using `Real.exp_le_exp.mpr (himin i1)`. Establish `hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 ≤ ∑ i, ‖((MomentRationality.mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2`. Introduce `w`.

Use `le_trans ?_ (hplace w)` and prove the remaining obligations. Establish `hzpos : 0 < ‖z w‖` using `norm_pos_iff.mpr (z_ne hN hc w)`. Establish `hzle : ‖z w‖⁻¹ ^ 2 ≤ Z`. Use `Finset.single_le_sum (f := fun w => ‖z w‖⁻¹ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hZinv : Z⁻¹ ≤ ‖z w‖ ^ 2`. Use `inv_anti₀ (by positivity) hzle` as an intermediate fact. Rewrite `this` using `[inv_pow, inv_inv]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Establish `hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ _ := Finset.sum_le_sum fun w _ => hterm w`.
-/
theorem dual_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imin : Fin N} (himin : ∀ i, s imin ≤ s i) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2 ≤
      q (dualH (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1)) y := by
  classical
  rw [q_dual]
  set v := (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gT_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi1mem : v ((Finset.univ.filter fun i => v i ≠ 0).min' hne) ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  set i1 := (Finset.univ.filter fun i => v i ≠ 0).min' hne with hi1
  have hzero : ∀ j, j < i1 → v j = 0 := by
    intro j hj
    by_contra hjne
    have : i1 ≤ j := Finset.min'_le _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => dual_place hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi1mem (int_d hdg y i1)
  have he : Real.exp (s imin) ≤ Real.exp (s i1) := Real.exp_le_exp.mpr (himin i1)
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 ≤
      ∑ i, ‖((MomentRationality.mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖⁻¹ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖⁻¹ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ ‖z w‖ ^ 2 := by
      have := inv_anti₀ (by positivity) hzle
      rwa [inv_pow, inv_inv] at this
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * ‖z w‖ ^ 2 * Real.exp (s i1) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i1)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

/- English proof (translation)
Introduce `L _ _ hL N hN c hrat M`. Take `⟨g, z, hc⟩` from `hrat`. Take `⟨d, hd, hint⟩` from `exists_den ((Finset.univ.image fun ij : Fin N × Fin N => gi g ij.1 ij.2) ∪ (Finset.univ.image fun ij : Fin N × Fin N => ((g : Matrix (Fin N) (Fin N) L)ᵀ) ij.1 ij.2))`. Establish `hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j)` using `fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))`. Establish `hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j)` using `fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))`.

Use `set A1 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA1def`. Use `set A2 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA2def`. Use `⟨(A1 * A2)⁻¹, ?_⟩` and prove the remaining obligations. Introduce `p hp s hs k hk`. Use `haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩`.

Take `⟨imax, himax⟩` from `Finite.exists_max s`. Take `⟨imin, himin⟩` from `Finite.exists_min s`. Establish `hM : M ≠ 0`. Introduce and unpack `rfl`. Take `⟨w0⟩` from `(inferInstance : Nonempty (InfinitePlace L))`.

Establish `h1` using `hp.2.2.2 ⟨0, hN⟩`. Rewrite `h1` using `[Finset.prod_eq_zero (Finset.mem_univ w0)]`. Conclude with `zero_ne_one h1`. Conclude with `le_antisymm (hp.2.1 w0 _ _) (norm_nonneg _)`. Establish `hdR : (d : ℝ) ≠ 0` using `by exact_mod_cast hd`.

Establish `hA1 : 0 < A1` using `by positivity`. Establish `hA2 : 0 < A2` using `by positivity`. Establish `h1` using `lam_ge hN (fun y hy => primal_y hL hN hc hd hdi hp hs hk himax y hy)`. Establish `h2` using `lam_ge hN (fun y hy => dual_y hL hN hc hd hdg hp hs hk himin y hy)`. Use `set e1 := Real.exp (-s imax) ^ 2`.

Use `set e2 := Real.exp (s imin) ^ 2`. Use `set X := Real.exp (2 * (s imax - s imin))`. Establish `he1 : 0 < e1` using `by positivity`. Establish `he2 : 0 < e2` using `by positivity`. Establish `hprod : e1 * e2 * X = 1`.

Simplify using `only [e1, e2, X, sq, ← Real.exp_add]`. Use `Real.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hX : X = (e1 * e2)⁻¹` using `eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)`. Use `show (lam _ * lam _)⁻¹ ≤ _`.

Combine the equalities or inequalities in the displayed calculation. Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)`. Use `_ = (A1 * A2)⁻¹ * X := by rw [hX]; ring`. Use `_ ≤ (A1 * A2)⁻¹ * Real.exp (2 * W s) := by gcongr show Real.exp (2 * (s imax - s imin)) ≤ Real.exp (2 * W s)`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hW` using `sub_le_sum_abs_consecutive_diff s imax imin`. Unfold `W`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sHtB : SHtB := by
  intro L _ _ hL N hN c hrat M
  obtain ⟨g, z, hc⟩ := hrat
  classical
  obtain ⟨d, hd, hint⟩ := exists_den
    ((Finset.univ.image fun ij : Fin N × Fin N => gi g ij.1 ij.2) ∪
      (Finset.univ.image fun ij : Fin N × Fin N => ((g : Matrix (Fin N) (Fin N) L)ᵀ) ij.1 ij.2))
  have hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j) := fun i j =>
    hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j) := fun i j =>
    hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  set A1 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA1def
  set A2 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA2def
  refine ⟨(A1 * A2)⁻¹, ?_⟩
  intro p hp s hs k hk
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨imax, himax⟩ := Finite.exists_max s
  obtain ⟨imin, himin⟩ := Finite.exists_min s
  have hM : M ≠ 0 := by
    rintro rfl
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have h1 := hp.2.2.2 ⟨0, hN⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ w0)] at h1
    · exact zero_ne_one h1
    · exact le_antisymm (hp.2.1 w0 _ _) (norm_nonneg _)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have h1 := lam_ge hN (fun y hy => primal_y hL hN hc hd hdi hp hs hk himax y hy)
  have h2 := lam_ge hN (fun y hy => dual_y hL hN hc hd hdg hp hs hk himin y hy)
  set e1 := Real.exp (-s imax) ^ 2
  set e2 := Real.exp (s imin) ^ 2
  set X := Real.exp (2 * (s imax - s imin))
  have he1 : 0 < e1 := by positivity
  have he2 : 0 < e2 := by positivity
  have hprod : e1 * e2 * X = 1 := by
    simp only [e1, e2, X, sq, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hX : X = (e1 * e2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  show (lam _ * lam _)⁻¹ ≤ _
  calc (lam _ * lam _)⁻¹ ≤ (A1 * e1 * (A2 * e2))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
    _ = (A1 * A2)⁻¹ * X := by rw [hX]; ring
    _ ≤ (A1 * A2)⁻¹ * Real.exp (2 * W s) := by
        gcongr
        show Real.exp (2 * (s imax - s imin)) ≤ Real.exp (2 * W s)
        apply Real.exp_le_exp.mpr
        have hW := sub_le_sum_abs_consecutive_diff s imax imin
        unfold W
        linarith

end PositivityTheory.KB.TwSMInt2
