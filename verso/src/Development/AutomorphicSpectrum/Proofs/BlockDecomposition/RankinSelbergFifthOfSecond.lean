import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open ValuativeRel
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RSPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ball (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set (Fin 2 → F) := {r | ∀ i, r i ∈ valBall F n}

def shell (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set (Fin 2 → F) := ball F n \ ball F (n + 1)

def uu (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : ℝ≥0 := (residueCard F : ℝ≥0) ^ (-n)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use extensionality with `r`. Simplify using `[ball]`.
-/
theorem ball_eq (n : ℤ) : ball F n = Set.pi Set.univ fun _ => (valBall F n : Set F) := by
  ext r; simp [ball]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Introduce `_ hr i` and use `valBall_antitone h (hr i)`.
-/
theorem ball_anti {n m : ℤ} (h : n ≤ m) : ball F m ⊆ ball F n :=
  fun _ hr i => valBall_antitone h (hr i)

/- English proof (translation)
Rewrite using `[ball_eq]`. Conclude with `MeasurableSet.univ_pi fun _ => measurableSet_valBall n`.
-/
theorem measurableSet_ball (n : ℤ) : MeasurableSet (ball F n) := by
  rw [ball_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_valBall n

/- English proof (translation)
The claim follows from `(measurableSet_ball n).diff (measurableSet_ball (n + 1))`.
-/
theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell F n) :=
  (measurableSet_ball n).diff (measurableSet_ball (n + 1))

/- English proof (translation)
Unfold `Ad3.R.m2`. Use `infer_instance`.
-/
theorem plane_measure_isAddHaar (ψ : AddChar F Circle) : (Ad3.R.m2 ψ).IsAddHaarMeasure := by
  unfold Ad3.R.m2; infer_instance

/- English proof (translation)
Establish `h1 : selfDualMeasure ψ (valBall F n : Set F) = (uu F n : ℝ≥0∞)`. Rewrite using `[measure_valBall, coe_valBall_zero, selfDualMeasure_integers, hψ.2.2]`. Simplify using `[uu]`. Rewrite using `[Ad3.R.m2, ball_eq, Measure.pi_pi]`. Simplify using `[h1, Fin.prod_univ_two, sq]`.
-/
theorem plane_measure_ball {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (n : ℤ) :
    Ad3.R.m2 ψ (ball F n) = ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have h1 : selfDualMeasure ψ (valBall F n : Set F) = (uu F n : ℝ≥0∞) := by
    rw [measure_valBall, coe_valBall_zero, selfDualMeasure_integers, hψ.2.2]
    simp [uu]
  rw [Ad3.R.m2, ball_eq, Measure.pi_pi]
  simp [h1, Fin.prod_univ_two, sq]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[uu, uu, neg_add, zpow_add₀ residueCard_nnreal_ne_zero, _root_.zpow_neg_one]`.
-/
theorem uu_succ (n : ℤ) : uu F (n + 1) = uu F n * ((residueCard F : ℝ≥0))⁻¹ := by
  rw [uu, uu, neg_add, zpow_add₀ residueCard_nnreal_ne_zero, _root_.zpow_neg_one]

def cc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] : ℝ≥0 :=
  1 - ((residueCard F : ℝ≥0)⁻¹) ^ 2

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `h : ((residueCard F : ℝ≥0)⁻¹) ^ 2 < 1` using `pow_lt_one₀ zero_le' (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal) two_ne_zero`. Conclude with `(tsub_pos_of_lt h).ne'`.
-/
theorem cc_ne_zero : cc F ≠ 0 := by
  have h : ((residueCard F : ℝ≥0)⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ zero_le' (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal) two_ne_zero
  exact (tsub_pos_of_lt h).ne'

/- English proof (translation)
Use `plane_measure_isAddHaar ψ` as an intermediate fact. Rewrite using `[shell, measure_diff (ball_anti (by omega)) (measurableSet_ball _).nullMeasurableSet (by rw [plane_measure_ball hψ]; exact ENNReal.coe_ne_top), plane_measure_ball hψ, plane_measure_ball hψ, uu_succ, ← ENNReal.coe_sub]`. Use `congr 1`. Rewrite using `[cc, tsub_mul, one_mul, mul_pow, mul_comm]`.
-/
theorem plane_measure_shell {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (n : ℤ) :
    Ad3.R.m2 ψ (shell F n) = ((cc F * uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have := plane_measure_isAddHaar ψ
  rw [shell, measure_diff (ball_anti (by omega)) (measurableSet_ball _).nullMeasurableSet
    (by rw [plane_measure_ball hψ]; exact ENNReal.coe_ne_top), plane_measure_ball hψ, plane_measure_ball hψ, uu_succ, ← ENNReal.coe_sub]
  congr 1
  rw [cc, tsub_mul, one_mul, mul_pow, mul_comm]

/- English proof (translation)
Establish `ht : Tendsto (fun n : ℕ => uu F (n : ℤ)) atTop (𝓝 0)`. Establish `h` using `tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((residueCard F : ℝ≥0))⁻¹) zero_le' (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal)`. Use `h.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[uu, _root_.zpow_neg, zpow_natCast, inv_pow]`. Establish `ht2 : Tendsto (fun n : ℕ => ((uu F (n : ℤ) ^ 2 : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0)`.

Use `(ht.pow 2)` as an intermediate fact. Simplify using `using ENNReal.tendsto_coe.mpr this`. Use `le_antisymm (ge_of_tendsto' ht2 fun n => ?_) zero_le'` and prove the remaining obligations. Rewrite using `[← plane_measure_ball hψ]`. Conclude with `measure_mono fun r hr i => by rw [Set.mem_singleton_iff.mp hr]; exact zero_mem _`.
-/
theorem plane_measure_zero {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) : Ad3.R.m2 ψ {0} = 0 := by
  have ht : Tendsto (fun n : ℕ => uu F (n : ℤ)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((residueCard F : ℝ≥0))⁻¹) zero_le'
      (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal)
    refine h.congr fun n => ?_
    rw [uu, _root_.zpow_neg, zpow_natCast, inv_pow]
  have ht2 : Tendsto (fun n : ℕ => ((uu F (n : ℤ) ^ 2 : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    have := (ht.pow 2)
    simpa using ENNReal.tendsto_coe.mpr this
  refine le_antisymm (ge_of_tendsto' ht2 fun n => ?_) zero_le'
  rw [← plane_measure_ball hψ]
  exact measure_mono fun r hr i => by rw [Set.mem_singleton_iff.mp hr]; exact zero_mem _

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use extensionality with `r`. Simplify using `only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, hn'⟩ rfl`. Conclude with `hn' fun i => zero_mem _`.

Introduce `hr`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, r i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hr (funext h)`.

Establish `hex : ∃ n : ℤ, r ∈ ball F n`. Take `⟨a, ha⟩` from `exists_mem_valBall_neg_nat (r 0)`. Take `⟨b, hb⟩` from `exists_mem_valBall_neg_nat (r 1)`. Use `⟨-((max a b : ℕ) : ℤ), fun j => ?_⟩` and prove the remaining obligations. Use `fin_cases j`.

Conclude with `valBall_antitone (by push_cast; omega) ha`. Conclude with `valBall_antitone (by push_cast; omega) hb`. Establish `hbd : ∀ n : ℤ, r ∈ ball F n → n ≤ ord (r i)` using `fun n hn => (mem_valBall_iff_le_ord hi).mp (hn i)`. Take `⟨n, hn, hmax⟩` from `Int.exists_greatest_of_bdd ⟨_, hbd⟩ hex`. Conclude with `⟨n, hn, fun h => by have := hmax _ h; omega⟩`.
-/
theorem iUnion_shell : ⋃ n, shell F n = ({0} : Set (Fin 2 → F))ᶜ := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, hn'⟩ rfl
    exact hn' fun i => zero_mem _
  · intro hr
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hr (funext h)
    have hex : ∃ n : ℤ, r ∈ ball F n := by
      obtain ⟨a, ha⟩ := exists_mem_valBall_neg_nat (r 0)
      obtain ⟨b, hb⟩ := exists_mem_valBall_neg_nat (r 1)
      refine ⟨-((max a b : ℕ) : ℤ), fun j => ?_⟩
      fin_cases j
      · exact valBall_antitone (by push_cast; omega) ha
      · exact valBall_antitone (by push_cast; omega) hb
    have hbd : ∀ n : ℤ, r ∈ ball F n → n ≤ ord (r i) := fun n hn =>
      (mem_valBall_iff_le_ord hi).mp (hn i)
    obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd ⟨_, hbd⟩ hex
    exact ⟨n, hn, fun h => by have := hmax _ h; omega⟩

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `key : ∀ n m : ℤ, n < m → Disjoint (shell F n) (shell F m)` using `fun n m h => Set.disjoint_left.mpr fun r hr hr' => hr.2 (ball_anti (by omega) hr'.1)`. Introduce `n m hnm`. Break down `lt_or_gt_of_ne hnm with h | h` into its components or cases. Conclude with `key n m h`. Conclude with `(key m n h).symm`.
-/
theorem disjoint_shell : Pairwise (Function.onFun Disjoint (shell F)) := by
  have key : ∀ n m : ℤ, n < m → Disjoint (shell F n) (shell F m) := fun n m h =>
    Set.disjoint_left.mpr fun r hr hr' => hr.2 (ball_anti (by omega) hr'.1)
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact key n m h
  · exact (key m n h).symm

/- English proof (translation)
Establish `hae : ∀ᵐ r ∂μ, r ∈ ⋃ n, shell F n`. Rewrite using `[iUnion_shell]`. Conclude with `measure_eq_zero_iff_ae_notMem.mp h0`. Rewrite using `[← Measure.restrict_eq_self_of_ae_mem hae, lintegral_iUnion measurableSet_shell disjoint_shell]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[Measure.restrict_eq_self_of_ae_mem hae, setLIntegral_congr_fun (measurableSet_shell n) (hH n), setLIntegral_const]`.
-/
theorem lintegral_shells (μ : Measure (Fin 2 → F)) (h0 : μ {0} = 0) (H : (Fin 2 → F) → ℝ≥0∞)
    (h : ℤ → ℝ≥0∞) (hH : ∀ n, ∀ r ∈ shell F n, H r = h n) :
    ∫⁻ r, H r ∂μ = ∑' n, h n * μ (shell F n) := by
  have hae : ∀ᵐ r ∂μ, r ∈ ⋃ n, shell F n := by
    rw [iUnion_shell]
    exact measure_eq_zero_iff_ae_notMem.mp h0
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_iUnion measurableSet_shell disjoint_shell]
  refine tsum_congr fun n => ?_
  rw [Measure.restrict_eq_self_of_ae_mem hae,
    setLIntegral_congr_fun (measurableSet_shell n) (hH n), setLIntegral_const]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Take `⟨c, hc, hcn⟩` from `exists_ord_eq F n`. Conclude with `⟨Units.mk0 c hc, hcn⟩`.
-/
theorem exists_unit_ord (n : ℤ) : ∃ t : Fˣ, ord (t : F) = n := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq F n
  exact ⟨Units.mk0 c hc, hcn⟩

def tt (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Fˣ := (exists_unit_ord n).choose

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `(exists_unit_ord n).choose_spec`.
-/
theorem ord_tt (n : ℤ) : ord (tt F n : F) = n := (exists_unit_ord n).choose_spec

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]`.
-/
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Simplify using `[h0]`. Establish `ht0 : (t : F) ≠ 0` using `t.ne_zero`. Rewrite using `[mem_integer_iff_ord (mul_ne_zero (inv_ne_zero ht0) h0), ord_mul (inv_ne_zero ht0) h0, ord_inv ht0, ht]`. Use `(mem_valBall_iff_le_ord h0).mp hx` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem integral_div {x : F} {n : ℤ} (hx : x ∈ valBall F n) (t : Fˣ) (ht : ord (t : F) = n) :
    (t : F)⁻¹ * x ∈ 𝒪[F] := by
  by_cases h0 : x = 0
  · simp [h0]
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero ht0) h0), ord_mul (inv_ne_zero ht0) h0,
    ord_inv ht0, ht]
  have := (mem_valBall_iff_le_ord h0).mp hx
  omega

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Break down `hu with ⟨h0, hi⟩ | ⟨h0, hi⟩` into its components or cases. Use `⟨⟨!![0, -a⁻¹; a, b], !![b, a⁻¹; -a, 0], ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]`. Rewrite using `[GLnLocal.mem_integralGL_iff]`.

Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]`. Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Use `⟨⟨!![b⁻¹, 0; a, b], !![b, 0; -a, b⁻¹], ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]`. Rewrite using `[GLnLocal.mem_integralGL_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]`. Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem exists_K_row {a b : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F])
    (hu : (a ≠ 0 ∧ a⁻¹ ∈ 𝒪[F]) ∨ (b ≠ 0 ∧ b⁻¹ ∈ 𝒪[F])) :
    ∃ κ ∈ integralGL F 2, ![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) = ![a, b] := by
  rcases hu with ⟨h0, hi⟩ | ⟨h0, hi⟩
  · refine ⟨⟨!![0, -a⁻¹; a, b], !![b, a⁻¹; -a, 0], ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · rw [GLnLocal.mem_integralGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
    · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![b⁻¹, 0; a, b], !![b, 0; -a, b⁻¹], ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · rw [GLnLocal.mem_integralGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
    · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `ht0 : (tt F n : F) ≠ 0` using `(tt F n).ne_zero`. Establish `hint` using `fun i => integral_div (hr.1 i) (tt F n) (ord_tt n)`. Establish `hunit : ∃ i, (tt F n : F)⁻¹ * r i ≠ 0 ∧ ((tt F n : F)⁻¹ * r i)⁻¹ ∈ 𝒪[F]`. Use `hr.2` as an intermediate fact. Simplify using `only [ball, Set.mem_setOf_eq, not_forall] at this`.

Take `⟨i, hi⟩` from `this`. Establish `h0 : r i ≠ 0` using `fun h => hi (h ▸ zero_mem _)`. Establish `h1` using `(mem_valBall_iff_le_ord h0).mp (hr.1 i)`. Establish `h2` using `mt (mem_valBall_iff_le_ord h0).mpr hi`. Establish `hn : (tt F n : F)⁻¹ * r i ≠ 0` using `mul_ne_zero (inv_ne_zero ht0) h0`.

Use `⟨i, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_integer_iff_ord (inv_ne_zero hn), ord_inv hn, ord_mul (inv_ne_zero ht0) h0, ord_inv ht0, ord_tt]`. Use linear arithmetic over natural numbers and integers. Establish `hu : ((tt F n : F)⁻¹ * r 0 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 0)⁻¹ ∈ 𝒪[F]) ∨ ((tt F n : F)⁻¹ * r 1 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 1)⁻¹ ∈ 𝒪[F])`. Take `⟨i, hi⟩` from `hunit`.

Use `fin_cases i`. Conclude with `Or.inl hi`. Conclude with `Or.inr hi`. Take `⟨κ, hκ, he⟩` from `exists_K_row (hint 0) (hint 1) hu`. Use `⟨κ, hκ, ?_⟩` and prove the remaining obligations.

Establish `hs : ![0, (tt F n : F)] = (tt F n : F) • ![0, 1]`. Apply the tactic sequence `ext j; fin_cases j <;> simp`. Rewrite using `[hs, Matrix.smul_vecMul, he]`. Apply the tactic sequence `ext j; fin_cases j <;> simp [ht0]`.
-/
theorem exists_K_shell {n : ℤ} {r : Fin 2 → F} (hr : r ∈ shell F n) :
    ∃ κ ∈ integralGL F 2, r = ![0, (tt F n : F)] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) := by
  have ht0 : (tt F n : F) ≠ 0 := (tt F n).ne_zero
  have hint := fun i => integral_div (hr.1 i) (tt F n) (ord_tt n)
  have hunit : ∃ i, (tt F n : F)⁻¹ * r i ≠ 0 ∧ ((tt F n : F)⁻¹ * r i)⁻¹ ∈ 𝒪[F] := by
    have := hr.2
    simp only [ball, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨i, hi⟩ := this
    have h0 : r i ≠ 0 := fun h => hi (h ▸ zero_mem _)
    have h1 := (mem_valBall_iff_le_ord h0).mp (hr.1 i)
    have h2 := mt (mem_valBall_iff_le_ord h0).mpr hi
    have hn : (tt F n : F)⁻¹ * r i ≠ 0 := mul_ne_zero (inv_ne_zero ht0) h0
    refine ⟨i, hn, ?_⟩
    rw [mem_integer_iff_ord (inv_ne_zero hn), ord_inv hn, ord_mul (inv_ne_zero ht0) h0,
      ord_inv ht0, ord_tt]
    omega
  have hu : ((tt F n : F)⁻¹ * r 0 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 0)⁻¹ ∈ 𝒪[F]) ∨
      ((tt F n : F)⁻¹ * r 1 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 1)⁻¹ ∈ 𝒪[F]) := by
    obtain ⟨i, hi⟩ := hunit
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨κ, hκ, he⟩ := exists_K_row (hint 0) (hint 1) hu
  refine ⟨κ, hκ, ?_⟩
  have hs : ![0, (tt F n : F)] = (tt F n : F) • ![0, 1] := by
    ext j; fin_cases j <;> simp
  rw [hs, Matrix.smul_vecMul, he]
  ext j; fin_cases j <;> simp [ht0]

section Act

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

def act (r : Fin 2 → F) (κ : integralGL F 2) : Fin 2 → F := r ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] in
/- English proof (translation)
Simplify using `[act, Matrix.vecMul_vecMul]`.
-/
theorem act_act (r : Fin 2 → F) (κ κ' : integralGL F 2) : act (act r κ) κ' = act r (κ * κ') := by
  simp [act, Matrix.vecMul_vecMul]

/- English proof (translation)
The claim follows from `((GLnLocal.continuous_entry F 2 i j).comp continuous_subtype_val).measurable`.
-/
theorem measurable_entry (i j : Fin 2) :
    Measurable fun κ : integralGL F 2 => (κ.1 : Matrix (Fin 2) (Fin 2) F) i j :=
  ((GLnLocal.continuous_entry F 2 i j).comp continuous_subtype_val).measurable

/- English proof (translation)
Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `h : (fun p : (Fin 2 → F) × integralGL F 2 => act p.1 p.2 j) = fun p => p.1 0 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 0 j + p.1 1 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 1 j`. Use function extensionality and compare the values at `p`. Simplify using `[act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Rewrite using `[h]`.

Apply the tactic sequence `exact (((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_entry 0 j).comp measurable_snd)).add (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_entry 1 j).comp measurable_snd))`.
-/
theorem measurable_act : Measurable fun p : (Fin 2 → F) × integralGL F 2 => act p.1 p.2 := by
  refine measurable_pi_lambda _ fun j => ?_
  have h : (fun p : (Fin 2 → F) × integralGL F 2 => act p.1 p.2 j) = fun p =>
      p.1 0 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 0 j + p.1 1 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    funext p
    simp [act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h]
  exact (((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_entry 0 j).comp measurable_snd)).add
    (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_entry 1 j).comp measurable_snd))

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] in
/- English proof (translation)
Introduce `j`. Establish `he` using `((GLnLocal.mem_integralGL_iff F 2).mp κ.2).1`. Establish `h : act r κ j = r 0 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 0 j + r 1 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 1 j`. Simplify using `[act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Rewrite using `[h, mem_valBall_zero_iff]`.

Conclude with `Subring.add_mem _ (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 0)) (he 0 j)) (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 1)) (he 1 j))`.
-/
theorem act_mem_ball {r : Fin 2 → F} (hr : r ∈ ball F 0) (κ : integralGL F 2) : act r κ ∈ ball F 0 := by
  intro j
  have he := ((GLnLocal.mem_integralGL_iff F 2).mp κ.2).1
  have h : act r κ j = r 0 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 0 j +
      r 1 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    simp [act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h, mem_valBall_zero_iff]
  exact Subring.add_mem _ (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 0)) (he 0 j))
    (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 1)) (he 1 j))

/- English proof (translation)
Use `plane_measure_isAddHaar ψ` as an intermediate fact. Set `M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)` to `{ toFun := fun r => act r κ⁻¹ invFun := fun r => act r κ map_add' := fun x y => by simp [act, Matrix.add_vecMul] map_smul' := fun c x => by simp [act, Matrix.smul_vecMul] left_inv := fun r => by simp [act_act, act] right_inv := fun r => by simp [act_act, act] }`. Establish `hmeas : Measurable fun r : Fin 2 → F => act r κ` using `measurable_act.comp (measurable_id.prodMk measurable_const)`. Establish `h` using `GlobalTheory.ChangeVarPi.map_symm_eq_smul F (Fin 2) (Ad3.R.m2 ψ) M`. Establish `hfun : (M.symm : (Fin 2 → F) → (Fin 2 → F)) = fun r => act r κ` using `rfl`.

Rewrite `h` using `[hfun]`. Establish `hpre : (fun r => act r κ) ⁻¹' ball F 0 = ball F 0`. Use extensionality with `r`. Use `⟨fun hr => ?_, fun hr => act_mem_ball hr κ⟩` and prove the remaining obligations. Use `act_mem_ball hr κ⁻¹` as an intermediate fact.

Simplify `this` using `[act_act, act]`. Establish `hb` using `congrArg (fun μ : Measure (Fin 2 → F) => μ (ball F 0)) h`. Simplify using `only [Measure.map_apply hmeas (measurableSet_ball 0), hpre, Measure.smul_apply, plane_measure_ball hψ] at hb`. Establish `hu : uu F 0 = 1` using `by simp [uu]`. Rewrite `hb` using `[hu]`.

Establish `hc : distribHaarChar F (LinearEquiv.det M) = 1`. Simplify `hb.symm` using `[ENNReal.smul_def]`. Rewrite `h` using `[hc, one_smul]`. Conclude with `⟨hmeas, h⟩`.
-/
theorem measurePreserving_act {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (κ : integralGL F 2) :
    MeasurePreserving (fun r => act r κ) (Ad3.R.m2 ψ) (Ad3.R.m2 ψ) := by
  have := plane_measure_isAddHaar ψ
  let M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
    { toFun := fun r => act r κ⁻¹
      invFun := fun r => act r κ
      map_add' := fun x y => by simp [act, Matrix.add_vecMul]
      map_smul' := fun c x => by simp [act, Matrix.smul_vecMul]
      left_inv := fun r => by simp [act_act, act]
      right_inv := fun r => by simp [act_act, act] }
  have hmeas : Measurable fun r : Fin 2 → F => act r κ :=
    measurable_act.comp (measurable_id.prodMk measurable_const)
  have h := GlobalTheory.ChangeVarPi.map_symm_eq_smul F (Fin 2) (Ad3.R.m2 ψ) M
  have hfun : (M.symm : (Fin 2 → F) → (Fin 2 → F)) = fun r => act r κ := rfl
  rw [hfun] at h
  have hpre : (fun r => act r κ) ⁻¹' ball F 0 = ball F 0 := by
    ext r
    refine ⟨fun hr => ?_, fun hr => act_mem_ball hr κ⟩
    have := act_mem_ball hr κ⁻¹
    simpa [act_act, act] using this
  have hb := congrArg (fun μ : Measure (Fin 2 → F) => μ (ball F 0)) h
  simp only [Measure.map_apply hmeas (measurableSet_ball 0), hpre, Measure.smul_apply, plane_measure_ball hψ] at hb
  have hu : uu F 0 = 1 := by simp [uu]
  rw [hu] at hb
  have hc : distribHaarChar F (LinearEquiv.det M) = 1 := by
    simpa [ENNReal.smul_def] using hb.symm
  rw [hc, one_smul] at h
  exact ⟨hmeas, h⟩

end Act

section Main

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

def avg (m : Measure (integralGL F 2)) (f : (Fin 2 → F) → ℝ≥0∞) (r : Fin 2 → F) : ℝ≥0∞ :=
  ∫⁻ κ, f (act r κ) ∂m

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Simplify using `only [avg, act_act]`. Conclude with `lintegral_mul_left_eq_self (fun κ => f (act r κ)) κ₀`.
-/
theorem avg_act (m : Measure (integralGL F 2)) [m.IsHaarMeasure] (f : (Fin 2 → F) → ℝ≥0∞)
    (r : Fin 2 → F) (κ₀ : integralGL F 2) : avg m f (act r κ₀) = avg m f r := by
  simp only [avg, act_act]
  exact lintegral_mul_left_eq_self (fun κ => f (act r κ)) κ₀

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Take `⟨κ, hκ, rfl⟩` from `exists_K_shell hr`. Conclude with `avg_act m f _ ⟨κ, hκ⟩`.
-/
theorem avg_shell (m : Measure (integralGL F 2)) [m.IsHaarMeasure] (f : (Fin 2 → F) → ℝ≥0∞)
    {n : ℤ} {r : Fin 2 → F} (hr : r ∈ shell F n) : avg m f r = avg m f ![0, (tt F n : F)] := by
  obtain ⟨κ, hκ, rfl⟩ := exists_K_shell hr
  exact avg_act m f _ ⟨κ, hκ⟩

/- English proof (translation)
The claim follows from `Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → F) × integralGL F 2 => f (act p.1 p.2)) (hf.comp measurable_act)`.
-/
theorem measurable_avg (m : Measure (integralGL F 2)) [IsProbabilityMeasure m]
    {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) : Measurable (avg m f) :=
  Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → F) × integralGL F 2 => f (act p.1 p.2))
    (hf.comp measurable_act)

/- English proof (translation)
Use `plane_measure_isAddHaar ψ` as an intermediate fact. Simplify using `only [avg]`. Establish `hae : AEMeasurable (Function.uncurry fun (r : Fin 2 → F) (κ : integralGL F 2) => f (act r κ)) ((Ad3.R.m2 ψ).prod m)` using `(hf.comp measurable_act).aemeasurable`. Rewrite using `[lintegral_lintegral_swap hae]`. Establish `h : ∀ κ : integralGL F 2, ∫⁻ r, f (act r κ) ∂Ad3.R.m2 ψ = ∫⁻ r, f r ∂Ad3.R.m2 ψ` using `fun κ => (measurePreserving_act hψ κ).lintegral_comp hf`.

Simplify using `[h]`.
-/
theorem lintegral_avg {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (m : Measure (integralGL F 2))
    [IsProbabilityMeasure m] {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, avg m f r ∂Ad3.R.m2 ψ = ∫⁻ r, f r ∂Ad3.R.m2 ψ := by
  have := plane_measure_isAddHaar ψ
  simp only [avg]
  have hae : AEMeasurable (Function.uncurry fun (r : Fin 2 → F) (κ : integralGL F 2) => f (act r κ))
      ((Ad3.R.m2 ψ).prod m) := (hf.comp measurable_act).aemeasurable
  rw [lintegral_lintegral_swap hae]
  have h : ∀ κ : integralGL F 2, ∫⁻ r, f (act r κ) ∂Ad3.R.m2 ψ = ∫⁻ r, f r ∂Ad3.R.m2 ψ :=
    fun κ => (measurePreserving_act hψ κ).lintegral_comp hf
  simp [h]

/- English proof (translation)
Rewrite using `[← lintegral_avg hψ m hf, lintegral_shells _ (plane_measure_zero hψ) _ (fun n => avg m f ![0, (tt F n : F)]) (fun n r hr => avg_shell m f hr)]`. Repeatedly rewrite using `[plane_measure_shell hψ]`.
-/
theorem lintegral_plane_measure_shells {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (m : Measure (integralGL F 2))
    [m.IsHaarMeasure] [IsProbabilityMeasure m] {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂Ad3.R.m2 ψ =
      ∑' n, avg m f ![0, (tt F n : F)] * ((cc F * uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [← lintegral_avg hψ m hf, lintegral_shells _ (plane_measure_zero hψ) _ (fun n => avg m f ![0, (tt F n : F)])
    (fun n r hr => avg_shell m f hr)]
  simp_rw [plane_measure_shell hψ]

end Main

def ushell (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set Fˣ := {z | ord (z : F) = n}

/- English proof (translation)
Establish `h : ushell F n = Units.val ⁻¹' ((valBall F n : Set F) \ valBall F (n + 1))`. Use extensionality with `z`. Simplify using `only [ushell, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, mem_valBall_iff_le_ord z.ne_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h]`.

Conclude with `measurableEmbedding_units_val.measurable ((measurableSet_valBall n).diff (measurableSet_valBall (n + 1)))`.
-/
theorem measurableSet_ushell (n : ℤ) : MeasurableSet (ushell F n) := by
  have h : ushell F n = Units.val ⁻¹' ((valBall F n : Set F) \ valBall F (n + 1)) := by
    ext z
    simp only [ushell, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe,
      mem_valBall_iff_le_ord z.ne_zero]
    omega
  rw [h]
  exact measurableEmbedding_units_val.measurable
    ((measurableSet_valBall n).diff (measurableSet_valBall (n + 1)))

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0 : x ∈ valBall F 0` using `mem_valBall_zero_iff.mpr (le_of_eq h)`. Establish `h1 : x ∉ valBall F 1` using `fun h' => (mem_valBall_one_iff.mp h').ne h`. Establish `a` using `(mem_valBall_iff_le_ord hx).mp h0`.

Establish `b` using `mt (mem_valBall_iff_le_ord hx).mpr h1`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Establish `h0 : x ∈ valBall F 0` using `(mem_valBall_iff_le_ord hx).mpr h.ge`. Establish `h1 : x ∉ valBall F 1` using `fun h' => by`.

Use `(mem_valBall_iff_le_ord hx).mp h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hle : valuation F x ≤ 1` using `mem_valBall_zero_iff.mp h0`. Establish `hnlt : ¬ valuation F x < 1` using `fun h' => h1 (mem_valBall_one_iff.mpr h')`. Conclude with `le_antisymm hle (not_lt.mp hnlt)`.
-/
theorem valuation_eq_one_iff {x : F} (hx : x ≠ 0) : valuation F x = 1 ↔ ord x = 0 := by
  constructor
  · intro h
    have h0 : x ∈ valBall F 0 := mem_valBall_zero_iff.mpr (le_of_eq h)
    have h1 : x ∉ valBall F 1 := fun h' => (mem_valBall_one_iff.mp h').ne h
    have a := (mem_valBall_iff_le_ord hx).mp h0
    have b := mt (mem_valBall_iff_le_ord hx).mpr h1
    omega
  · intro h
    have h0 : x ∈ valBall F 0 := (mem_valBall_iff_le_ord hx).mpr h.ge
    have h1 : x ∉ valBall F 1 := fun h' => by
      have := (mem_valBall_iff_le_ord hx).mp h'
      omega
    have hle : valuation F x ≤ 1 := mem_valBall_zero_iff.mp h0
    have hnlt : ¬ valuation F x < 1 := fun h' => h1 (mem_valBall_one_iff.mpr h')
    exact le_antisymm hle (not_lt.mp hnlt)

/- English proof (translation)
Establish `h : ushell F n = (fun z => (tt F n)⁻¹ * z) ⁻¹' (unitFiltrationUnits F 0 : Set Fˣ)`. Use extensionality with `z`. Establish `ht0 : (tt F n : F) ≠ 0` using `(tt F n).ne_zero`. Simplify using `only [ushell, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff, Units.val_mul, Units.val_inv_eq_inv_val]`. Rewrite using `[valuation_eq_one_iff (mul_ne_zero (inv_ne_zero ht0) z.ne_zero), ord_mul (inv_ne_zero ht0) z.ne_zero, ord_inv ht0, ord_tt]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h, measure_preimage_mul, multHaar_unitFiltrationUnits_zero]`.
-/
theorem multHaar_ushell (n : ℤ) : multHaar F (ushell F n) = 1 := by
  have h : ushell F n = (fun z => (tt F n)⁻¹ * z) ⁻¹' (unitFiltrationUnits F 0 : Set Fˣ) := by
    ext z
    have ht0 : (tt F n : F) ≠ 0 := (tt F n).ne_zero
    simp only [ushell, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      mem_unitFiltrationUnits_zero_iff, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [valuation_eq_one_iff (mul_ne_zero (inv_ne_zero ht0) z.ne_zero),
      ord_mul (inv_ne_zero ht0) z.ne_zero, ord_inv ht0, ord_tt]
    omega
  rw [h, measure_preimage_mul, multHaar_unitFiltrationUnits_zero]

/- English proof (translation)
Establish `hU : ⋃ n, ushell F n = Set.univ` using `Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr ⟨_, rfl⟩`. Establish `hd : Pairwise (Function.onFun Disjoint (ushell F))` using `fun n m hnm => Set.disjoint_left.mpr fun z hz hz' => hnm (hz.symm.trans hz')`. Rewrite using `[← setLIntegral_univ, ← hU, lintegral_iUnion measurableSet_ushell hd]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[setLIntegral_congr_fun (measurableSet_ushell n) (hH n), setLIntegral_const, multHaar_ushell, mul_one]`.
-/
theorem lintegral_ushells (H : Fˣ → ℝ≥0∞) (h : ℤ → ℝ≥0∞) (hH : ∀ n, ∀ z ∈ ushell F n, H z = h n) :
    ∫⁻ z, H z ∂multHaar F = ∑' n, h n := by
  have hU : ⋃ n, ushell F n = Set.univ :=
    Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr ⟨_, rfl⟩
  have hd : Pairwise (Function.onFun Disjoint (ushell F)) := fun n m hnm =>
    Set.disjoint_left.mpr fun z hz hz' => hnm (hz.symm.trans hz')
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion measurableSet_ushell hd]
  refine tsum_congr fun n => ?_
  rw [setLIntegral_congr_fun (measurableSet_ushell n) (hH n), setLIntegral_const, multHaar_ushell,
    mul_one]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `⟨fun i => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `fin_cases i`. Conclude with `zero_mem _`. Conclude with `(mem_valBall_iff_le_ord z.ne_zero).mpr hz.ge`. Use `(mem_valBall_iff_le_ord z.ne_zero).mp (h 1)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem row_mem_shell {n : ℤ} {z : Fˣ} (hz : ord (z : F) = n) : ![0, (z : F)] ∈ shell F n := by
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i
    · exact zero_mem _
    · exact (mem_valBall_iff_le_ord z.ne_zero).mpr hz.ge
  · have := (mem_valBall_iff_le_ord z.ne_zero).mp (h 1)
    omega

def dens (z : Fˣ) : ℝ≥0∞ := ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)

/- English proof (translation)
Unfold `dens`. Conclude with `ENNReal.measurable_ofReal.comp (((measurable_modulus.comp measurableEmbedding_units_val.measurable).coe_nnreal_real).pow_const 2)`.
-/
theorem measurable_dens : Measurable (dens : Fˣ → ℝ≥0∞) := by
  unfold dens
  exact ENNReal.measurable_ofReal.comp
    (((measurable_modulus.comp measurableEmbedding_units_val.measurable).coe_nnreal_real).pow_const 2)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Rewrite using `[dens, modulus_of_ne_zero z.ne_zero, hz, uu, ← ENNReal.ofReal_coe_nnreal]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem dens_of_ord {n : ℤ} {z : Fˣ} (hz : ord (z : F) = n) :
    dens z = ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [dens, modulus_of_ne_zero z.ne_zero, hz, uu, ← ENNReal.ofReal_coe_nnreal]
  push_cast
  rfl

/- English proof (translation)
Establish `h1 : SecondCountableTopology Fˣ` using `(isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology`. Establish `h2 : LocallyCompactSpace Fˣ` using `(isOpenEmbedding_units_val (K := F)).locallyCompactSpace`. Use `infer_instance`.
-/
theorem sFinite_multHaar : SFinite (multHaar F) := by
  have h1 : SecondCountableTopology Fˣ :=
    (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology
  have h2 : LocallyCompactSpace Fˣ := (isOpenEmbedding_units_val (K := F)).locallyCompactSpace
  infer_instance

/- English proof (translation)
Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Use `fin_cases j`. Conclude with `measurable_const`. Conclude with `measurableEmbedding_units_val.measurable`.
-/
theorem measurable_row : Measurable fun z : Fˣ => (![0, (z : F)] : Fin 2 → F) := by
  refine measurable_pi_lambda _ fun j => ?_
  fin_cases j
  · exact measurable_const
  · exact measurableEmbedding_units_val.measurable

section Push

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

/- English proof (translation)
The claim follows from `measurable_act.comp ((measurable_row.comp measurable_snd).prodMk measurable_fst)`.
-/
theorem measurable_push : Measurable fun p : integralGL F 2 × Fˣ =>
    (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F) : Fin 2 → F) :=
  measurable_act.comp ((measurable_row.comp measurable_snd).prodMk measurable_fst)

/- English proof (translation)
Use `sFinite_multHaar (F := F)` as an intermediate fact. Rewrite using `[lintegral_map hf measurable_push, lintegral_prod_symm (fun p : integralGL F 2 × Fˣ => f (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F))) (hf.comp measurable_push).aemeasurable]`. Establish `hA : Measurable fun z : Fˣ => avg m f ![0, (z : F)]` using `(measurable_avg m hf).comp measurable_row`. Establish `e : ∫⁻ z, ∫⁻ κ : integralGL F 2, f (![0, (z : F)] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)) ∂m ∂((multHaar F).withDensity dens) = ∫⁻ z, avg m f ![0, (z : F)] ∂((multHaar F).withDensity dens)` using `rfl`. Rewrite using `[e, lintegral_withDensity_eq_lintegral_mul _ measurable_dens hA]`.

Use `lintegral_ushells _ _ fun n z hz => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Rewrite using `[dens_of_ord hz, avg_shell m f (row_mem_shell hz), mul_comm]`.
-/
theorem lintegral_push (m : Measure (integralGL F 2)) [m.IsHaarMeasure] [IsProbabilityMeasure m]
    {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂(Measure.map (fun p : integralGL F 2 × Fˣ =>
        (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F) : Fin 2 → F))
      (m.prod ((multHaar F).withDensity dens))) =
      ∑' n, avg m f ![0, (tt F n : F)] * ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have := sFinite_multHaar (F := F)
  rw [lintegral_map hf measurable_push, lintegral_prod_symm (fun p : integralGL F 2 × Fˣ =>
    f (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F))) (hf.comp measurable_push).aemeasurable]
  have hA : Measurable fun z : Fˣ => avg m f ![0, (z : F)] := (measurable_avg m hf).comp measurable_row
  have e : ∫⁻ z, ∫⁻ κ : integralGL F 2, f (![0, (z : F)] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)) ∂m
      ∂((multHaar F).withDensity dens) =
      ∫⁻ z, avg m f ![0, (z : F)] ∂((multHaar F).withDensity dens) := rfl
  rw [e, lintegral_withDensity_eq_lintegral_mul _ measurable_dens hA]
  refine lintegral_ushells _ _ fun n z hz => ?_
  simp only [Pi.mul_apply]
  rw [dens_of_ord hz, avg_shell m f (row_mem_shell hz), mul_comm]

end Push

/- English proof (translation)
Introduce `_ F _ _ _ _ _ _ ψ hψ _ _ m _ _`. Use `⟨cc F, cc_ne_zero, Measure.ext fun s hs => ?_⟩` and prove the remaining obligations. Establish `hf : Measurable (s.indicator (1 : (Fin 2 → F) → ℝ≥0∞))` using `measurable_one.indicator hs`. Establish `h1` using `lintegral_plane_measure_shells hψ m hf`. Establish `h2` using `lintegral_push m hf`.

Rewrite `h1`, `h2` using `[lintegral_indicator_one hs]`. Establish `e : (fun z : Fˣ => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)) = dens` using `rfl`. Rewrite using `[Measure.smul_apply, e, h1, h2, ENNReal.smul_def, smul_eq_mul, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem measure_plane_eq_rows : Ad3.R.A2 → Ad3.R.A5 := by
  intro _ F _ _ _ _ _ _ ψ hψ _ _ m _ _
  refine ⟨cc F, cc_ne_zero, Measure.ext fun s hs => ?_⟩
  have hf : Measurable (s.indicator (1 : (Fin 2 → F) → ℝ≥0∞)) := measurable_one.indicator hs
  have h1 := lintegral_plane_measure_shells hψ m hf
  have h2 := lintegral_push m hf
  rw [lintegral_indicator_one hs] at h1 h2
  have e : (fun z : Fˣ => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)) = dens := rfl
  rw [Measure.smul_apply, e, h1, h2, ENNReal.smul_def, smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [ENNReal.coe_mul]
  ring

end GlobalTheory.CompanionTheory.RSPlane

end
