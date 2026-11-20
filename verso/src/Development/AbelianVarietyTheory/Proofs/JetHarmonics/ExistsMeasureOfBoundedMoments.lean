import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open Filter
open scoped BigOperators Topology

namespace GlobalTheory.MultiMahler

variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Use `letI : Module ℤ_[q] E := Module.compHom E (algebraMap ℤ_[q] ℚ_[q])`. Use `haveI : IsBoundedSMul ℤ_[q] E := IsBoundedSMul.of_norm_smul_le fun r x => norm_smul_le (r : ℚ_[q]) x`. Conclude with `PadicInt.fwdDiff_tendsto_zero f`.
-/
theorem fwdDiff_tendsto_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[q] E]
    [IsUltrametricDist E] (f : C(ℤ_[q], E)) :
    Tendsto (fun n => (fwdDiff (1 : ℤ_[q]))^[n] f 0) atTop (𝓝 0) := by
  letI : Module ℤ_[q] E := Module.compHom E (algebraMap ℤ_[q] ℚ_[q])
  haveI : IsBoundedSMul ℤ_[q] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[q]) x
  exact PadicInt.fwdDiff_tendsto_zero f

noncomputable def curryFirst {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    C(ℤ_[q], C(Fin g → ℤ_[q], ℂ_[q])) :=
  ContinuousMap.curry (F.comp ⟨fun x : ℤ_[q] × (Fin g → ℤ_[q]) => Fin.cons x.1 x.2,
    Continuous.finCons continuous_fst continuous_snd⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem curryFirst_apply {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) (t : ℤ_[q])
    (a : Fin g → ℤ_[q]) : curryFirst F t a = F (Fin.cons t a) := rfl

/- English proof (translation)
Rewrite using `[ContinuousMap.norm_le _ (norm_nonneg _)]`. Introduce `t`. Rewrite using `[ContinuousMap.norm_le _ (norm_nonneg _)]`. Introduce `a`. Conclude with `F.norm_coe_le_norm _`.
-/
theorem norm_curryFirst_le {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    ‖curryFirst F‖ ≤ ‖F‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro t
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro a
  exact F.norm_coe_le_norm _

noncomputable def diffFirst {g : ℕ} (m : ℕ) :
    C(Fin (g + 1) → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin g → ℤ_[q], ℂ_[q]) where
  toFun F := (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0
  map_add' F G := by
    have : (curryFirst (F + G) : ℤ_[q] → _) = curryFirst F + curryFirst G := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_add]; rfl
  map_smul' r F := by
    have : (curryFirst (r • F) : ℤ_[q] → _) = r • (curryFirst F : ℤ_[q] → _) := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_const_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diffFirst_apply {g : ℕ} (m : ℕ) (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    diffFirst m F = (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0 := rfl

/- English proof (translation)
Proceed by induction on `g with`. Consider the case `zero`. Use `⟨fun _ => { toFun := fun F => F 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }, fun n F => F.norm_coe_le_norm _, fun n f F hF => by simpa using hF 0, fun F => ?_⟩` and prove the remaining obligations. Rewrite using `[Filter.cofinite_eq_bot]`. Conclude with `tendsto_bot`.

Consider the case `succ g ih`. Take `⟨D, h1, h2, h3⟩` from `ih`. Use `⟨fun n => (D (Fin.tail n)).comp (diffFirst (n 0)), fun n F => ?_, fun n f F hF => ?_, fun F => ?_⟩` and prove the remaining obligations. Conclude with `(h1 _ _).trans ((IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 _ 0 _).trans (norm_curryFirst_le F))`. Set `P : C(Fin g → ℤ_[q], ℂ_[q])` to `⟨fun a => ∏ i, f i.succ (a i), by fun_prop⟩`.

Establish `hP : diffFirst (n 0) F = (fwdDiff (1 : ℤ_[q]))^[n 0] (f 0) 0 • P`. Rewrite using `[diffFirst_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Use `congr 1`.

Use extensionality with `a`. Simplify using `[curryFirst_apply, hF, Fin.prod_univ_succ, P]`. Rewrite using `[LinearMap.comp_apply, hP, map_smul, h2 _ (fun i => f i.succ) P (fun _ => rfl), Fin.prod_univ_succ]`. Both sides reduce to the same expression. Use `NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_` and prove the remaining obligations.

Establish `hA` using `NormedAddGroup.tendsto_nhds_zero.mp (fwdDiff_tendsto_zero' (curryFirst F)) ε hε`. Rewrite `hA` using `[← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]`. Establish `hB : ∀ m, {n' : Fin g → ℕ | ¬ ‖D n' (diffFirst m F)‖ < ε}.Finite` using `fun m => Filter.eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp (h3 _) ε hε)`. Rewrite using `[Filter.eventually_cofinite]`. Use `(hA.biUnion fun m _ => (hB m).image (fun n' => (Fin.cons m n' : Fin (g + 1) → ℕ))).subset fun n hn => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, not_lt] at hn ⊢`. Conclude with `⟨n 0, hn.trans (h1 _ _), Fin.tail n, hn, Fin.cons_self_tail n⟩`.
-/
theorem exists_multiDiff (g : ℕ) :
    ∃ D : (Fin g → ℕ) → C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q],
      (∀ n F, ‖D n F‖ ≤ ‖F‖) ∧
      (∀ n (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
        (∀ a, F a = ∏ i, f i (a i)) → D n F = ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) ∧
      (∀ F, Tendsto (fun n => D n F) cofinite (𝓝 0)) := by
  induction g with
  | zero =>
    refine ⟨fun _ => { toFun := fun F => F 0, map_add' := fun _ _ => rfl,
                       map_smul' := fun _ _ => rfl }, fun n F => F.norm_coe_le_norm _,
      fun n f F hF => by simpa using hF 0, fun F => ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot
  | succ g ih =>
    obtain ⟨D, h1, h2, h3⟩ := ih
    refine ⟨fun n => (D (Fin.tail n)).comp (diffFirst (n 0)), fun n F => ?_,
      fun n f F hF => ?_, fun F => ?_⟩
    · exact (h1 _ _).trans ((IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 _ 0 _).trans
        (norm_curryFirst_le F))
    · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, f i.succ (a i), by fun_prop⟩
      have hP : diffFirst (n 0) F = (fwdDiff (1 : ℤ_[q]))^[n 0] (f 0) 0 • P := by
        rw [diffFirst_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift,
          Finset.sum_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_assoc]
        congr 1
        ext a
        simp [curryFirst_apply, hF, Fin.prod_univ_succ, P]
      rw [LinearMap.comp_apply, hP, map_smul, h2 _ (fun i => f i.succ) P (fun _ => rfl),
        Fin.prod_univ_succ]
      rfl
    · refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
      have hA := NormedAddGroup.tendsto_nhds_zero.mp (fwdDiff_tendsto_zero' (curryFirst F)) ε hε
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hA
      have hB : ∀ m, {n' : Fin g → ℕ | ¬ ‖D n' (diffFirst m F)‖ < ε}.Finite := fun m =>
        Filter.eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp (h3 _) ε hε)
      rw [Filter.eventually_cofinite]
      refine (hA.biUnion fun m _ => (hB m).image
        (fun n' => (Fin.cons m n' : Fin (g + 1) → ℕ))).subset fun n hn => ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, not_lt] at hn ⊢
      exact ⟨n 0, hn.trans (h1 _ _), Fin.tail n, hn, Fin.cons_self_tail n⟩

noncomputable def binomC (k : ℕ) : C(ℤ_[q], ℂ_[q]) :=
  ⟨fun x => algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q]),
    (continuous_algebraMap _ _).comp (continuous_subtype_val.comp (mahler k).continuous)⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q])‖ ≤ 1`. Rewrite using `[norm_algebraMap']`. Conclude with `PadicInt.norm_le_one _`.
-/
theorem norm_binomC_le (k : ℕ) (x : ℤ_[q]) : ‖binomC k x‖ ≤ 1 := by
  change ‖algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q])‖ ≤ 1
  rw [norm_algebraMap']
  exact PadicInt.norm_le_one _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap ℚ_[q] ℂ_[q] ((mahler k (n : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = _`. Rewrite using `[mahler_natCast_eq, PadicInt.coe_natCast, map_natCast]`.
-/
theorem binomC_natCast (k n : ℕ) : binomC k (n : ℤ_[q]) = (n.choose k : ℂ_[q]) := by
  change algebraMap ℚ_[q] ℂ_[q] ((mahler k (n : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = _
  rw [mahler_natCast_eq, PadicInt.coe_natCast, map_natCast]

/- English proof (translation)
Establish `h` using `fwdDiff_iter_choose_zero k m`. Rewrite `h`, the goal using `[fwdDiff_iter_eq_sum_shift]`. Establish `h'` using `congrArg (Int.cast : ℤ → ℂ_[q]) h`. Simplify using `only [zero_add, nsmul_one, binomC_natCast] at h' ⊢`. Simplify using `using h'`.
-/
theorem fwdDiff_binomC (k m : ℕ) :
    (fwdDiff (1 : ℤ_[q]))^[m] (binomC (q := q) k) 0 = if m = k then 1 else 0 := by
  have h := fwdDiff_iter_choose_zero k m
  rw [fwdDiff_iter_eq_sum_shift] at h ⊢
  have h' := congrArg (Int.cast : ℤ → ℂ_[q]) h
  simp only [zero_add, nsmul_one, binomC_natCast] at h' ⊢
  simpa using h'

/- English proof (translation)
Introduce `q _ g c ⟨B₀, hB₀⟩`. Take `⟨D, h1, h2, h3⟩` from `exists_multiDiff (q := q) g`. Establish `hs : ∀ F, Summable fun n => c n * D n F` using `fun F => by`. Use `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_` and prove the remaining obligations. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`.

Use `(tendsto_zero_iff_norm_tendsto_zero.mp (h3 F)).const_mul B₀` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB₀ n) (norm_nonneg _)`.

Set `L : C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q]` to `{ toFun := fun F => ∑' n, c n * D n F map_add' := fun F G => by`. Simplify using `only [map_add, mul_add]`. Conclude with `(hs F).tsum_add (hs G)`. Use the proof step `map_smul' := fun r F => by`. Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`.

Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr fun n => by ring }`. Establish `hL : ∀ B : ℝ, (∀ n, ‖c n‖ ≤ B) → ∀ F, ‖L F‖ ≤ B * ‖F‖` using `fun B hB F => by`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (hB n) (h1 n F) (norm_nonneg _) ((norm_nonneg _).trans (hB n))`. Establish `hsum : ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ a, F a = ∏ i, f i (a i)) → HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (L F)`. Introduce `f F hF`. Use `(hs F).hasSum` as an intermediate fact. Simplify using `only [fun n => h2 n f F hF] at this`.

Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `tsum_congr fun n => by rw [h2 n f F hF]`. Use `⟨L.mkContinuous B₀ (hL B₀ hB₀), fun B hB => ⟨fun hμ n => ?_, fun h => ?_⟩, hsum⟩` and prove the remaining obligations. Set `P : C(Fin g → ℤ_[q], ℂ_[q])` to `⟨fun a => ∏ i, binomC (n i) (a i), by fun_prop⟩`. Establish `hP : ‖P‖ ≤ 1`.

Rewrite using `[ContinuousMap.norm_le _ zero_le_one]`. Introduce `a`. Express the relevant statement in the definitionally equal form `‖∏ i, binomC (n i) (a i)‖ ≤ 1`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_binomC_le _ _`.

Establish `hv : L P = c n`. Use `(hsum (fun i => binomC (n i)) P fun _ => rfl).unique ?_` and prove the remaining obligations. Use `hasSum_single (f := fun m : Fin g → ℕ => c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (binomC (q := q) (n i)) 0) n ?_ using 1` and compare the differences between its conclusion and the goal. Simplify using `[fwdDiff_binomC]`. Introduce `m hm`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hm`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (by rw [fwdDiff_binomC, if_neg hi]), mul_zero]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `ContinuousLinearMap.opNorm_le_bound _ hB (hL B h)`.
-/
theorem exists_measure_of_bounded_moments :
    ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (c : (Fin g → ℕ) → ℂ_[q]), (∃ B : ℝ, ∀ n, ‖c n‖ ≤ B) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q],
        (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ n, ‖c n‖ ≤ B)) ∧
        ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ a, F a = ∏ i, f i (a i)) →
          HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (μ F) := by
  intro q _ g c ⟨B₀, hB₀⟩
  obtain ⟨D, h1, h2, h3⟩ := exists_multiDiff (q := q) g
  have hs : ∀ F, Summable fun n => c n * D n F := fun F => by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.mp (h3 F)).const_mul B₀
    rw [mul_zero] at this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB₀ n) (norm_nonneg _)
  let L : C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q] :=
    { toFun := fun F => ∑' n, c n * D n F
      map_add' := fun F G => by
        simp only [map_add, mul_add]
        exact (hs F).tsum_add (hs G)
      map_smul' := fun r F => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring }
  have hL : ∀ B : ℝ, (∀ n, ‖c n‖ ≤ B) → ∀ F, ‖L F‖ ≤ B * ‖F‖ := fun B hB F => by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
    rw [norm_mul]
    exact mul_le_mul (hB n) (h1 n F) (norm_nonneg _) ((norm_nonneg _).trans (hB n))
  have hsum : ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
      (∀ a, F a = ∏ i, f i (a i)) →
      HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (L F) := by
    intro f F hF
    have := (hs F).hasSum
    simp only [fun n => h2 n f F hF] at this
    convert this using 1
    exact tsum_congr fun n => by rw [h2 n f F hF]
  refine ⟨L.mkContinuous B₀ (hL B₀ hB₀), fun B hB => ⟨fun hμ n => ?_, fun h => ?_⟩, hsum⟩
  · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, binomC (n i) (a i), by fun_prop⟩
    have hP : ‖P‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro a
      change ‖∏ i, binomC (n i) (a i)‖ ≤ 1
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_binomC_le _ _
    have hv : L P = c n := by
      refine (hsum (fun i => binomC (n i)) P fun _ => rfl).unique ?_
      convert hasSum_single (f := fun m : Fin g → ℕ =>
        c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (binomC (q := q) (n i)) 0) n ?_ using 1
      · simp [fwdDiff_binomC]
      · intro m hm
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [fwdDiff_binomC, if_neg hi]), mul_zero]
    calc ‖c n‖ = ‖L.mkContinuous B₀ (hL B₀ hB₀) P‖ := by rw [← hv]; rfl
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := mul_le_mul hμ hP (norm_nonneg _) hB
      _ = B := mul_one _
  · exact ContinuousLinearMap.opNorm_le_bound _ hB (hL B h)

end GlobalTheory.MultiMahler
