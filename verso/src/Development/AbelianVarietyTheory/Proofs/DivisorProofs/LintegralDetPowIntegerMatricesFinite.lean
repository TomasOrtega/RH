import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumnStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

/- English proof (translation)
Rewrite using `[det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]`. Simplify using `[Matrix.submatrix]`. Conclude with `Or.inl rfl`.
-/
theorem det_blk {k : Type} [Field k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det =
      x * M.det + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det := by
  rw [det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Matrix.submatrix]
  exact Or.inl rfl

/- English proof (translation)
Simplify using `only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]`. The claim follows by propositional logic.
-/
theorem mem_intM_blk {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))) ∈ intM k (Fin (n + 1)) (Fin (n + 1)) ↔
      x ∈ 𝒪[k] ∧ (∀ j, u j ∈ 𝒪[k]) ∧ (∀ i, v i ∈ 𝒪[k]) ∧ M ∈ intM k (Fin n) (Fin n) := by
  simp only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

/- English proof (translation)
Establish `h1` using `(𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))`. Establish `h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X` using `by ext; rfl`. Rewrite `h1` using `[h2]`. Rewrite using `[← h1]`. Conclude with `SetLike.coe_mem _`.
-/
theorem det_mem_int {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {X : Matrix (Fin n) (Fin n) k}
    (hX : X ∈ intM k (Fin n) (Fin n)) : X.det ∈ 𝒪[k] := by
  have h1 := (𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))
  have h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X := by ext; rfl
  rw [h2] at h1
  rw [← h1]
  exact SetLike.coe_mem _

/- English proof (translation)
Introduce `k _ _ _ _ _ _ μ _ n s hs`. Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `hOm : MeasurableSet (𝒪[k] : Set k)` using `GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet`. Establish `hO : μ (𝒪[k] : Set k) ≠ ⊤` using `GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne`. Use `set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP`.

Use `show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤`. Break down `le_or_gt 0 s with hs0 | hs0` into its components or cases. Establish `hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤ (intM k (Fin n) (Fin n)).indicator 1 X`. Introduce `X`. Distinguish the cases in `hX : X ∈ intM k (Fin n) (Fin n)`.

Rewrite using `[Set.indicator_of_mem hX, Set.indicator_of_mem hX]`. Establish `hdet` using `det_mem_int hX`. Simplify using `only [P, Pi.one_apply]`. Use `split_ifs with h`. Break down `hs0.eq_or_lt with h0 | h0` into its components or cases.

Simplify using `[← h0]`. Simplify using `[ENNReal.zero_rpow_of_pos h0]`. Conclude with `ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0`. Simplify using `[Set.indicator_of_notMem hX]`. Establish `hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k))`.

Use extensionality with `X`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Establish `hm : MeasurableSet (intM k (Fin n) (Fin n))`. Rewrite using `[hint]`. Conclude with `MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hint, volM]`. Use `erw [Measure.pi_pi]`. Simplify using `only [Measure.pi_pi]`. Conclude with `ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top`.

Use `set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK`. Establish `hKt : K ≠ ⊤` using `ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩`. Proceed by induction on `n with`. Consider the case `zero`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `hX : X ∈ intM k (Fin 0) (Fin 0)`. Rewrite using `[Set.indicator_of_mem hX]`. Simplify using `[P, GlobalTheory.SplitWeil.Model.nabs_one]`. Simplify using `[Set.indicator_of_notMem hX]`. Consider the case `succ n ih`.

Set `U : Set (Fin n → k)` to `Set.univ.pi fun _ => (𝒪[k] : Set k)`. Establish `hU : MeasurableSet U` using `MeasurableSet.univ_pi fun _ => hOm`. Establish `hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n` using `by simp [U, Measure.pi_pi]`. Establish `hUt : μ 𝒪[k] ^ n ≠ ⊤` using `ENNReal.pow_ne_top hO`. Use `set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI`.

Establish `inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det) (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤ U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u`. Introduce `M v u`. Distinguish the cases in `h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)`. Take `⟨hu, hv, hM⟩` from `h`. Rewrite using `[Set.indicator_of_mem hu, Set.indicator_of_mem hv]`.

Simplify using `only [I, Set.indicator_of_mem hM]`. Establish `he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det) (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) = (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n …`. Introduce `x`. Distinguish the cases in `hx : x ∈ (𝒪[k] : Set k)`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]`.

Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]`. Repeatedly rewrite using `[he]`. Use `(GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Rewrite using `[show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det) (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `x`. Use `Set.indicator_of_notMem (fun hx => h ?_) _` and prove the remaining obligations. Take `⟨_, hu, hv, hM⟩` from `(mem_intM_blk x u v M).1 hx`. Conclude with `⟨fun j _ => hu j, fun i _ => hv i, hM⟩`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun M => ?_` and prove the remaining obligations. Repeatedly rewrite using `[lintegral_indicator_const hU, hUv]`. Rewrite using `[lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]`. Use `_ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by`.

Rewrite using `[lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]`. Use `_ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)`.
-/
theorem intdet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  intro k _ _ _ _ _ _ μ _ n s hs
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hOm : MeasurableSet (𝒪[k] : Set k) := GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet
  have hO : μ (𝒪[k] : Set k) ≠ ⊤ := GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤
  rcases le_or_gt 0 s with hs0 | hs0
  · have hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤
        (intM k (Fin n) (Fin n)).indicator 1 X := by
      intro X
      by_cases hX : X ∈ intM k (Fin n) (Fin n)
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
        have hdet := det_mem_int hX
        simp only [P, Pi.one_apply]
        split_ifs with h
        · rcases hs0.eq_or_lt with h0 | h0
          · simp [← h0]
          · simp [ENNReal.zero_rpow_of_pos h0]
        · exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0
      · simp [Set.indicator_of_notMem hX]
    have hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    have hm : MeasurableSet (intM k (Fin n) (Fin n)) := by
      rw [hint]; exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm
    calc _ ≤ ∫⁻ X, (intM k (Fin n) (Fin n)).indicator 1 X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono hb
      _ = volM μ (Fin n) (Fin n) (intM k (Fin n) (Fin n)) := lintegral_indicator_one hm
      _ < ⊤ := by
        rw [hint, volM]; erw [Measure.pi_pi]
        simp only [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top
  · set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK
    have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩
    induction n with
    | zero =>
      calc _ ≤ ∫⁻ X, 1 ∂(volM μ (Fin 0) (Fin 0)) := lintegral_mono fun X => ?_
        _ < ⊤ := by rw [lintegral_one, volM]; erw [Measure.pi_univ]; simp
      by_cases hX : X ∈ intM k (Fin 0) (Fin 0)
      · rw [Set.indicator_of_mem hX]
        simp [P, GlobalTheory.SplitWeil.Model.nabs_one]
      · simp [Set.indicator_of_notMem hX]
    | succ n ih =>
      let U : Set (Fin n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
      have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hOm
      have hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n := by simp [U, Measure.pi_pi]
      have hUt : μ 𝒪[k] ^ n ≠ ⊤ := ENNReal.pow_ne_top hO
      set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI
      have inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
          (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤
          U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u := by
        intro M v u
        by_cases h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)
        · obtain ⟨hu, hv, hM⟩ := h
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv]
          simp only [I, Set.indicator_of_mem hM]
          have he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) =
              (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det)) x := by
            intro x
            by_cases hx : x ∈ (𝒪[k] : Set k)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]
          simp_rw [he]
          refine (GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)
          rw [mul_comm]
        · rw [show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]
          · simp
          funext x
          refine Set.indicator_of_notMem (fun hx => h ?_) _
          obtain ⟨_, hu, hv, hM⟩ := (mem_intM_blk x u v M).1 hx
          exact ⟨fun j _ => hu j, fun i _ => hv i, hM⟩
      calc _ ≤ _ := GlobalTheory.T.lintegral_matrix_first_row_column k μ n _
        _ ≤ ∫⁻ M, ∫⁻ v, ∫⁻ u, U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u
              ∂(Measure.pi fun _ : Fin n => μ) ∂(Measure.pi fun _ : Fin n => μ) ∂(volM μ (Fin n) (Fin n)) :=
            lintegral_mono fun M => lintegral_mono fun v => lintegral_mono fun u => inner M v u
        _ = ∫⁻ M, K * I M * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) ∂(volM μ (Fin n) (Fin n)) := by
            refine lintegral_congr fun M => ?_
            simp_rw [lintegral_indicator_const hU, hUv]
            rw [lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]
        _ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)

end GlobalTheory.GJInt
