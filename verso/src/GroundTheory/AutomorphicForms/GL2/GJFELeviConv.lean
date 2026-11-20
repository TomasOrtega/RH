import Mathlib
import GroundTheory.AutomorphicForms.GL2.IsAddHaarMeasureMatrixMeasureFinSq

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section OneBlock

variable {m : ℕ}

/- English proof (translation)
Rewrite using `[zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, coe_centralUnif, smul_pow, one_pow, smul_mul_assoc, one_mul]`.
-/
theorem coe_centralUnif_pow_mul (A : ℕ) (g : GL (Fin m) F) :
    ((centralUnif F m ^ (A : ℤ) * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (uniformizer F : F) ^ A • (g : Matrix (Fin m) (Fin m) F) := by
  rw [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, coe_centralUnif, smul_pow, one_pow,
    smul_mul_assoc, one_mul]

/- English proof (translation)
Take `⟨r, A, -, hA⟩` from `hΨ.exists_invariant`. Use `⟨A, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h1 : 0 ≤ ordDet (centralUnif F m ^ (A : ℤ) * g)`. Use `ord_nonneg_of_mem_integer (det_mem_integer fun i j => ?_) (det_ne_zero _)` and prove the remaining obligations. Rewrite using `[coe_centralUnif_pow_mul, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `hA _ hg i j`. Rewrite `h1` using `[ordDet_centralUnif_zpow_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem IsSchwartzBruhat.exists_le_ordDet {Ψ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΨ : IsSchwartzBruhat Ψ) :
    ∃ A : ℕ, ∀ g : GL (Fin m) F, Ψ (g : Matrix (Fin m) (Fin m) F) ≠ 0 →
      -((A : ℤ) * m) ≤ ordDet g := by
  obtain ⟨r, A, -, hA⟩ := hΨ.exists_invariant
  refine ⟨A, fun g hg => ?_⟩
  have h1 : 0 ≤ ordDet (centralUnif F m ^ (A : ℤ) * g) := by
    refine ord_nonneg_of_mem_integer (det_mem_integer fun i j => ?_) (det_ne_zero _)
    rw [coe_centralUnif_pow_mul, Matrix.smul_apply, smul_eq_mul]
    exact hA _ hg i j
  rw [ordDet_centralUnif_zpow_mul] at h1
  linarith

variable (m) in

def centralSat (C : Set (GL (Fin m) F)) : Set (GL (Fin m) F) :=
  {g | ∃ j : ℤ, centralUnif F m ^ j * g ∈ C}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨k + j, by rwa [_root_.zpow_add, mul_assoc]⟩`. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨k - j, by rwa [← mul_assoc, ← _root_.zpow_add, sub_add_cancel]⟩`.
-/
theorem centralUnif_zpow_mul_mem_centralSat {C : Set (GL (Fin m) F)} (j : ℤ) (g : GL (Fin m) F) :
    centralUnif F m ^ j * g ∈ centralSat m C ↔ g ∈ centralSat m C := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + j, by rwa [_root_.zpow_add, mul_assoc]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - j, by rwa [← mul_assoc, ← _root_.zpow_add, sub_add_cancel]⟩

/- English proof (translation)
Establish `hc : Continuous (ordDet : GL (Fin m) F → ℤ)` using `isLocallyConstant_ordDet_GL.continuous`. Establish `hK` using `hC.image hc`. Take `⟨a, ha⟩` from `hK.bddBelow`. Take `⟨b, hb⟩` from `hK.bddAbove`. Conclude with `⟨a, b, fun g hg => ⟨ha ⟨g, hg, rfl⟩, hb ⟨g, hg, rfl⟩⟩⟩`.
-/
theorem exists_bounds_ordDet {C : Set (GL (Fin m) F)} (hC : IsCompact C) :
    ∃ a b : ℤ, ∀ g ∈ C, a ≤ ordDet g ∧ ordDet g ≤ b := by
  have hc : Continuous (ordDet : GL (Fin m) F → ℤ) := isLocallyConstant_ordDet_GL.continuous
  have hK := hC.image hc
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  exact ⟨a, b, fun g hg => ⟨ha ⟨g, hg, rfl⟩, hb ⟨g, hg, rfl⟩⟩⟩

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

/- English proof (translation)
Establish `: centralSat m C = ⋃ j : ℤ, (fun g => centralUnif F m ^ j * g) ⁻¹' C`. Use extensionality with `g`. Simplify using `[centralSat]`. Rewrite using `[this]`. Conclude with `MeasurableSet.iUnion fun j => hC.isClosed.measurableSet.preimage (measurable_const_mul _)`.
-/
theorem measurableSet_centralSat {C : Set (GL (Fin m) F)} (hC : IsCompact C) :
    MeasurableSet (centralSat m C) := by
  have : centralSat m C = ⋃ j : ℤ, (fun g => centralUnif F m ^ j * g) ⁻¹' C := by
    ext g; simp [centralSat]
  rw [this]
  exact MeasurableSet.iUnion fun j =>
    hC.isClosed.measurableSet.preimage (measurable_const_mul _)

/- English proof (translation)
Take `⟨a, b, hab⟩` from `exists_bounds_ordDet hC`. Establish `hm : (1 : ℤ) ≤ m` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)`. Establish `hsub : tile F m 0 ∩ centralSat m C ⊆ ⋃ j ∈ Finset.Icc (-|a| - m) |b|, (fun g => centralUnif F m ^ j * g) ⁻¹' C`. Introduce and unpack `g ⟨⟨hg0, hg1⟩, j, hj⟩`. Simplify using `only [zero_mul, zero_add] at hg0 hg1`.

Take `⟨h1, h2⟩` from `hab _ hj`. Rewrite `h1`, `h2` using `[ordDet_centralUnif_zpow_mul]`. Use `Set.mem_biUnion (x := j) (Finset.mem_Icc.2 ⟨?_, ?_⟩) hj` and prove the remaining obligations. Assume the negation of the conclusion as `hc push Not at hc`. Establish `: j * m ≤ j` using `by nlinarith [abs_nonneg a]`.

Use `neg_abs_le a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hc push Not at hc`. Establish `: j ≤ j * m` using `by nlinarith [abs_nonneg b]`. Use `le_abs_self b` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_)` and prove the remaining obligations. Use `ENNReal.sum_lt_top.2 fun j _ => ?_` and prove the remaining obligations. Rewrite using `[measure_preimage_mul]`. Conclude with `hC.measure_lt_top`.
-/
theorem measure_tile_inter_centralSat_lt_top [NeZero m] (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {C : Set (GL (Fin m) F)} (hC : IsCompact C) :
    μ (tile F m 0 ∩ centralSat m C) < ⊤ := by
  classical
  obtain ⟨a, b, hab⟩ := exists_bounds_ordDet hC
  have hm : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hsub : tile F m 0 ∩ centralSat m C ⊆
      ⋃ j ∈ Finset.Icc (-|a| - m) |b|, (fun g => centralUnif F m ^ j * g) ⁻¹' C := by
    rintro g ⟨⟨hg0, hg1⟩, j, hj⟩
    simp only [zero_mul, zero_add] at hg0 hg1
    obtain ⟨h1, h2⟩ := hab _ hj
    rw [ordDet_centralUnif_zpow_mul] at h1 h2
    refine Set.mem_biUnion (x := j) (Finset.mem_Icc.2 ⟨?_, ?_⟩) hj
    · by_contra hc
      push Not at hc
      have : j * m ≤ j := by nlinarith [abs_nonneg a]
      have := neg_abs_le a
      linarith
    · by_contra hc
      push Not at hc
      have : j ≤ j * m := by nlinarith [abs_nonneg b]
      have := le_abs_self b
      linarith
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_)
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  rw [measure_preimage_mul]
  exact hC.measure_lt_top

/- English proof (translation)
Use `set S := centralSat m C with hS`. Establish `hSm : MeasurableSet S` using `measurableSet_centralSat hC`. Use `set f : GL (Fin m) F → ℝ := fun g => ‖Ψ (g : Matrix (Fin m) (Fin m) F)‖ * r ^ ordDet g with hf`. Establish `hfc : Continuous f`. Use `(hΨ.1.continuous.comp Units.continuous_val).norm.mul ?_` and prove the remaining obligations.

Conclude with `(continuous_of_discreteTopology (f := fun k : ℤ => r ^ k)).comp isLocallyConstant_ordDet_GL.continuous`. Establish `hf0 : ∀ g, 0 ≤ f g` using `fun g => mul_nonneg (norm_nonneg _) (zpow_nonneg hr0.le _)`. Use `And.intro (hfc.measurable.indicator hSm).aestronglyMeasurable ?_` and prove the remaining obligations. Take `⟨B, hB⟩ : ∃ B : ℝ, ∀ X, ‖Ψ X‖ ≤ B` from `hΨ.1.continuous.bounded_above_of_compact_support hΨ.2`. Take `⟨A, hA⟩` from `hΨ.exists_le_ordDet`.

Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB 0)`. Establish `hm : (1 : ℤ) ≤ m` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)`. Use `set T := μ (tile F m 0 ∩ S) with hT`. Establish `hTfin : T < ⊤` using `measure_tile_inter_centralSat_lt_top μ hC`. Use `set c : ℤ → ℝ≥0∞ := fun j => if -(A : ℤ) ≤ j then ENNReal.ofReal (B * r ^ (j * m)) else 0 with hc`.

Establish `hterm : ∀ j : ℤ, ∫⁻ g in tile F m 0, ‖S.indicator f (centralUnif F m ^ j * g)‖ₑ ∂μ ≤ c j * T`. Introduce `j`. Rewrite using `[hT, ← setLIntegral_const, ← lintegral_indicator ((measurableSet_tile 0).inter hSm), ← lintegral_indicator (measurableSet_tile 0)]`. Use `lintegral_mono fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ tile F m 0`.

Rewrite using `[Set.indicator_of_mem hg]`. Distinguish the cases in `hgS : g ∈ S`. Rewrite using `[Set.indicator_of_mem ((centralUnif_zpow_mul_mem_centralSat j g).2 hgS), Set.indicator_of_mem (Set.mem_inter hg hgS)]`. Rewrite using `[Real.enorm_eq_ofReal (hf0 _)]`. Distinguish the cases in `hΨ0 : Ψ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 0`.

Establish `h0 : f (centralUnif F m ^ j * g) = 0` using `by simp only [hf, hΨ0, norm_zero, zero_mul]`. Rewrite using `[h0, ENNReal.ofReal_zero]`. Conclude with `zero_le`. Establish `h1` using `hA _ hΨ0`. Rewrite `h1` using `[ordDet_centralUnif_zpow_mul]`.

Take `⟨hg0, hg1⟩` from `hg`. Simplify using `only [zero_mul, zero_add] at hg0 hg1`. Establish `hj : -(A : ℤ) ≤ j`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `: j * m ≤ (-(A : ℤ) - 1) * m` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [hc, if_pos hj]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[hf]`.

Simplify using `only`. Rewrite using `[ordDet_centralUnif_zpow_mul, zpow_add₀ hr0.ne']`. Establish `hle : r ^ ordDet g ≤ 1` using `zpow_le_one₀ hr0 hr1.le hg0`. Establish `hrj : 0 ≤ r ^ (j * (m : ℤ))` using `zpow_nonneg hr0.le _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_centralSat j g).1 hgS)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hg]`. Simplify using the standard rewrite rules. Establish `hsum : ∑' j : ℤ, c j < ⊤`.

Establish `hinj : Function.Injective fun k : ℕ => (k : ℤ) - A` using `fun k k' h => by`. Simplify using `using h`. Establish `hsupp : Function.support c ⊆ Set.range fun k : ℕ => (k : ℤ) - A`. Introduce `j hj`. Establish `hj' : -(A : ℤ) ≤ j`.

Assume the negation of the conclusion as `hcon`. Conclude with `hj (by simp [hc, hcon])`. Use `⟨(j + A).toNat, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Int.toNat_of_nonneg (by linarith)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hinj.tsum_eq hsupp]`. Establish `hr' : 0 < r ^ (m : ℕ)` using `pow_pos hr0 _`. Establish `hrm : r ^ (m : ℕ) < 1` using `pow_lt_one₀ hr0.le hr1 (NeZero.ne m)`. Establish `heq : ∀ k : ℕ, c ((k : ℤ) - A) = ENNReal.ofReal (B * r ^ (-(A : ℤ) * m)) * ENNReal.ofReal (r ^ (m : ℕ)) ^ k`.

Introduce `k`. Establish `hk : -(A : ℤ) ≤ (k : ℤ) - A` using `by linarith [Int.natCast_nonneg k]`. Simplify using `only [hc, if_pos hk]`. Rewrite using `[← ENNReal.ofReal_pow hr'.le, ← ENNReal.ofReal_mul (mul_nonneg hB0 (zpow_nonneg hr0.le _))]`. Use `congr 1`.

Rewrite using `[mul_assoc]`. Use `congr 1`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hr0.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[heq]`. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_geometric]`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 ?_)` and prove the remaining obligations. Rewrite using `[tsub_pos_iff_lt, ENNReal.ofReal_lt_one]`. Conclude with `hrm`.

Use `show ∫⁻ g, ‖S.indicator f g‖ₑ ∂μ < ⊤`. Rewrite using `[lintegral_eq_tsum_tile μ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_block [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    {Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΨ : IsSchwartzBruhat Ψ) {C : Set (GL (Fin m) F)}
    (hC : IsCompact C) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Integrable (fun g : GL (Fin m) F => (centralSat m C).indicator
      (fun g => ‖Ψ (g : Matrix (Fin m) (Fin m) F)‖ * r ^ ordDet g) g) μ := by
  classical
  set S := centralSat m C with hS
  have hSm : MeasurableSet S := measurableSet_centralSat hC
  set f : GL (Fin m) F → ℝ := fun g => ‖Ψ (g : Matrix (Fin m) (Fin m) F)‖ * r ^ ordDet g with hf
  have hfc : Continuous f := by
    refine (hΨ.1.continuous.comp Units.continuous_val).norm.mul ?_
    exact (continuous_of_discreteTopology (f := fun k : ℤ => r ^ k)).comp
      isLocallyConstant_ordDet_GL.continuous
  have hf0 : ∀ g, 0 ≤ f g := fun g => mul_nonneg (norm_nonneg _) (zpow_nonneg hr0.le _)
  refine And.intro (hfc.measurable.indicator hSm).aestronglyMeasurable ?_
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ X, ‖Ψ X‖ ≤ B := hΨ.1.continuous.bounded_above_of_compact_support hΨ.2
  obtain ⟨A, hA⟩ := hΨ.exists_le_ordDet
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hm : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  set T := μ (tile F m 0 ∩ S) with hT
  have hTfin : T < ⊤ := measure_tile_inter_centralSat_lt_top μ hC
  set c : ℤ → ℝ≥0∞ := fun j => if -(A : ℤ) ≤ j then ENNReal.ofReal (B * r ^ (j * m)) else 0
    with hc
  have hterm : ∀ j : ℤ, ∫⁻ g in tile F m 0,
      ‖S.indicator f (centralUnif F m ^ j * g)‖ₑ ∂μ ≤ c j * T := by
    intro j
    rw [hT, ← setLIntegral_const, ← lintegral_indicator ((measurableSet_tile 0).inter hSm),
      ← lintegral_indicator (measurableSet_tile 0)]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ tile F m 0
    · rw [Set.indicator_of_mem hg]
      by_cases hgS : g ∈ S
      · rw [Set.indicator_of_mem ((centralUnif_zpow_mul_mem_centralSat j g).2 hgS),
          Set.indicator_of_mem (Set.mem_inter hg hgS)]
        rw [Real.enorm_eq_ofReal (hf0 _)]
        by_cases hΨ0 : Ψ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 0
        · have h0 : f (centralUnif F m ^ j * g) = 0 := by simp only [hf, hΨ0, norm_zero, zero_mul]
          rw [h0, ENNReal.ofReal_zero]
          exact zero_le
        · have h1 := hA _ hΨ0
          rw [ordDet_centralUnif_zpow_mul] at h1
          obtain ⟨hg0, hg1⟩ := hg
          simp only [zero_mul, zero_add] at hg0 hg1
          have hj : -(A : ℤ) ≤ j := by
            by_contra hcon
            push Not at hcon
            have : j * m ≤ (-(A : ℤ) - 1) * m := by nlinarith
            nlinarith
          simp only [hc, if_pos hj]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hf]
          simp only
          rw [ordDet_centralUnif_zpow_mul, zpow_add₀ hr0.ne']
          have hle : r ^ ordDet g ≤ 1 := zpow_le_one₀ hr0 hr1.le hg0
          have hrj : 0 ≤ r ^ (j * (m : ℤ)) := zpow_nonneg hr0.le _
          calc ‖Ψ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)‖ *
                (r ^ (j * (m : ℤ)) * r ^ ordDet g) ≤ B * (r ^ (j * (m : ℤ)) * 1) :=
                mul_le_mul (hB _) (mul_le_mul_of_nonneg_left hle hrj) (by positivity) hB0
            _ = B * r ^ (j * (m : ℤ)) := by ring
      · rw [Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_centralSat j g).1 hgS)]
        simp
    · rw [Set.indicator_of_notMem hg]
      simp
  have hsum : ∑' j : ℤ, c j < ⊤ := by
    have hinj : Function.Injective fun k : ℕ => (k : ℤ) - A := fun k k' h => by
      simpa using h
    have hsupp : Function.support c ⊆ Set.range fun k : ℕ => (k : ℤ) - A := by
      intro j hj
      have hj' : -(A : ℤ) ≤ j := by
        by_contra hcon
        exact hj (by simp [hc, hcon])
      refine ⟨(j + A).toNat, ?_⟩
      simp only
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    rw [← hinj.tsum_eq hsupp]
    have hr' : 0 < r ^ (m : ℕ) := pow_pos hr0 _
    have hrm : r ^ (m : ℕ) < 1 := pow_lt_one₀ hr0.le hr1 (NeZero.ne m)
    have heq : ∀ k : ℕ, c ((k : ℤ) - A) =
        ENNReal.ofReal (B * r ^ (-(A : ℤ) * m)) * ENNReal.ofReal (r ^ (m : ℕ)) ^ k := by
      intro k
      have hk : -(A : ℤ) ≤ (k : ℤ) - A := by linarith [Int.natCast_nonneg k]
      simp only [hc, if_pos hk]
      rw [← ENNReal.ofReal_pow hr'.le, ← ENNReal.ofReal_mul (mul_nonneg hB0 (zpow_nonneg hr0.le _))]
      congr 1
      rw [mul_assoc]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hr0.ne']
      congr 1
      ring
    simp_rw [heq]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 ?_)
    rw [tsub_pos_iff_lt, ENNReal.ofReal_lt_one]
    exact hrm
  show ∫⁻ g, ‖S.indicator f g‖ₑ ∂μ < ⊤
  rw [lintegral_eq_tsum_tile μ]
  calc ∑' j : ℤ, ∫⁻ g in tile F m 0, ‖S.indicator f (centralUnif F m ^ j * g)‖ₑ ∂μ
      ≤ ∑' j : ℤ, c j * T := ENNReal.tsum_le_tsum hterm
    _ = (∑' j : ℤ, c j) * T := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hsum hTfin

end OneBlock

section Scalars

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Establish `hinv : ∀ v, ρ g⁻¹ v = α⁻¹ • v` using `fun v => by`. Establish `h1 : ρ g (ρ g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite `h1` using `[hα]`. Rewrite using `[← h1, smul_smul, inv_mul_cancel₀ hα0, one_smul, h1]`.

Proceed by induction on `k using Int.induction_on generalizing v with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[_root_.zpow_add_one, map_mul, Module.End.mul_apply, hα, map_smul, ih, smul_smul, zpow_add_one₀ hα0, mul_comm]`. Consider the case `pred k ih`.

Rewrite using `[_root_.zpow_sub_one, map_mul, Module.End.mul_apply, hinv, map_smul, ih, smul_smul, zpow_sub_one₀ hα0, mul_comm]`.
-/
theorem apply_zpow_of_apply_eq_smul (ρ : Representation ℂ G W) {g : G} {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, ρ g v = α • v) (k : ℤ) (v : W) : ρ (g ^ k) v = α ^ k • v := by
  have hinv : ∀ v, ρ g⁻¹ v = α⁻¹ • v := fun v => by
    have h1 : ρ g (ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hα] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hα0, one_smul, h1]
  induction k using Int.induction_on generalizing v with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, map_mul, Module.End.mul_apply, hα, map_smul, ih, smul_smul,
      zpow_add_one₀ hα0, mul_comm]
  | pred k ih =>
    rw [_root_.zpow_sub_one, map_mul, Module.End.mul_apply, hinv, map_smul, ih, smul_smul,
      zpow_sub_one₀ hα0, mul_comm]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.2 fun g => ?_)` and prove the remaining obligations. Use `⟨(fun x => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G), hv.preimage (continuous_const.mul continuous_id), by simp [one_mem], fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : ρ (g⁻¹ * x) v = v` using `mem_stabilizerOf.1 hx`. Establish `: x = g * (g⁻¹ * x)` using `by group`. Rewrite using `[this, map_mul, Module.End.mul_apply, hx']`.
-/
theorem continuous_coeff_of_smooth (ρ : Representation ℂ G W) {v : W}
    (hv : v ∈ smoothVectors ρ) (ℓ : Module.Dual ℂ W) : Continuous fun g => ℓ (ρ g v) := by
  refine IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G),
    hv.preimage (continuous_const.mul continuous_id), by simp [one_mem], fun x hx => ?_⟩
  have hx' : ρ (g⁻¹ * x) v = v := mem_stabilizerOf.1 hx
  have : x = g * (g⁻¹ * x) := by group
  rw [this, map_mul, Module.End.mul_apply, hx']

end Scalars

section Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
  {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]

def multiA (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W)
    (Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (x : ∀ i, GL (Fin (d i)) F) : ℂ :=
  (∏ i, Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) s) * ℓ (ρ (x, 1) w)

def multiB (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W)
    (Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (x : ∀ i, GL (Fin (d i)) F) : ℂ :=
  (∏ i, Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) ((d i : ℂ) - s)) *
    ℓ (ρ (x⁻¹, 1) w)

/- English proof (translation)
Establish `key : ∀ S : Finset ι, ∀ v, ρ ((fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1), 1) v = (∏ i ∈ S, α i ^ j i) • v`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `v`.

Use `show ρ 1 v = _`. Simplify using the standard rewrite rules. Consider the case `insert a S ha ih`. Introduce `v`. Establish `hpow : ((Pi.mulSingle a (centralUnif F (d a) ^ j a) : ∀ i, GL (Fin (d i)) F), (1 : H)) = (Pi.mulSingle a (centralUnif F (d a)), (1 : H)) ^ j a`.

Establish `e` using `map_zpow ((MonoidHom.inl (∀ i, GL (Fin (d i)) F) H).comp (MonoidHom.mulSingle (fun i => GL (Fin (d i)) F) a)) (centralUnif F (d a)) (j a)`. Simplify using `using e`. Establish `hfun : (fun i => if i ∈ insert a S then centralUnif F (d i) ^ j i else 1) = (Pi.mulSingle a (centralUnif F (d a) ^ j a) : ∀ i, GL (Fin (d i)) F) * (fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = a`.

Substitute `hi` using the available equality. Simplify using `[ha]`. Simplify using `[hi]`. Establish `hsplit : ((fun i => if i ∈ insert a S then centralUnif F (d i) ^ j i else 1), (1 : H)) = (Pi.mulSingle a (centralUnif F (d a)), (1 : H)) ^ j a * ((fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1), 1)`. Rewrite using `[← hpow, hfun, Prod.mk_mul_mk, mul_one]`.

Rewrite using `[hsplit, map_mul, Module.End.mul_apply, ih, map_smul, apply_zpow_of_apply_eq_smul ρ (hα0 a) (hα a) (j a), smul_smul, Finset.prod_insert ha, mul_comm]`. Use `key Finset.univ v` as an intermediate fact. Simplify using `using this`.
-/
theorem apply_centralPow (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W) {α : ι → ℂ}
    (hα0 : ∀ i, α i ≠ 0)
    (hα : ∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v) (j : ι → ℤ) (v : W) :
    ρ ((fun i => centralUnif F (d i) ^ j i), 1) v = (∏ i, α i ^ j i) • v := by
  classical
  have key : ∀ S : Finset ι, ∀ v, ρ ((fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1), 1) v =
      (∏ i ∈ S, α i ^ j i) • v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro v
      show ρ 1 v = _
      simp
    | insert a S ha ih =>
      intro v
      have hpow : ((Pi.mulSingle a (centralUnif F (d a) ^ j a) : ∀ i, GL (Fin (d i)) F), (1 : H)) =
          (Pi.mulSingle a (centralUnif F (d a)), (1 : H)) ^ j a := by
        have e := map_zpow ((MonoidHom.inl (∀ i, GL (Fin (d i)) F) H).comp
          (MonoidHom.mulSingle (fun i => GL (Fin (d i)) F) a)) (centralUnif F (d a)) (j a)
        simpa using e
      have hfun : (fun i => if i ∈ insert a S then centralUnif F (d i) ^ j i else 1) =
          (Pi.mulSingle a (centralUnif F (d a) ^ j a) : ∀ i, GL (Fin (d i)) F) *
            (fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [ha]
        · simp [hi]
      have hsplit : ((fun i => if i ∈ insert a S then centralUnif F (d i) ^ j i else 1),
          (1 : H)) = (Pi.mulSingle a (centralUnif F (d a)), (1 : H)) ^ j a *
            ((fun i => if i ∈ S then centralUnif F (d i) ^ j i else 1), 1) := by
        rw [← hpow, hfun, Prod.mk_mul_mk, mul_one]
      rw [hsplit, map_mul, Module.End.mul_apply, ih, map_smul,
        apply_zpow_of_apply_eq_smul ρ (hα0 a) (hα a) (j a), smul_smul, Finset.prod_insert ha,
        mul_comm]
  have := key Finset.univ v
  simpa using this

omit [DecidableEq ι] in

/- English proof (translation)
Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hc.continuousOn`. Establish `hB0 : ∀ x ∈ C, 0 ≤ B` using `fun x hx => (norm_nonneg _).trans (hB x hx)`. Use `set ρ : ι → ℝ := fun i => ‖β i‖ ^ ((d i : ℝ)⁻¹) with hρ`. Establish `hρ0 : ∀ i, 0 < ρ i` using `fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 (hβ0 i)) _`. Establish `hρd : ∀ i, ρ i ^ (d i : ℤ) = ‖β i‖` using `fun i => by`.

Rewrite using `[zpow_natCast, hρ]`. Simplify using `only`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ (by exact_mod_cast NeZero.ne (d i)), Real.rpow_one]`. Establish `hCi : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C)` using `fun i => hC.image (continuous_apply i)`. Use `choose a b hab using fun i => exists_bounds_ordDet (hCi i)`.

Use `set D : ι → ℝ := fun i => ρ i ^ (-a i) + ρ i ^ (-b i) with hD`. Establish `hD0 : ∀ i, 0 ≤ D i` using `fun i => add_nonneg (zpow_nonneg (hρ0 i).le _) (zpow_nonneg (hρ0 i).le _)`. Distinguish the cases in `hCe : C.Nonempty`. Use `swap`. Use `⟨0, le_rfl, fun x => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : c x = 0`. Simplify using `[hx]`. Take `⟨j, hj⟩` from `hsupp x hx`. Conclude with `absurd ⟨_, hj⟩ hCe`. Take `⟨x₀, hx₀⟩` from `hCe`.

Use `⟨B * ∏ i, D i, mul_nonneg (hB0 x₀ hx₀) (Finset.prod_nonneg fun i _ => hD0 i), fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : c x = 0`. Rewrite using `[hx, norm_zero]`. Conclude with `mul_nonneg (mul_nonneg (hB0 x₀ hx₀) (Finset.prod_nonneg fun i _ => hD0 i)) (Finset.prod_nonneg fun i _ => zpow_nonneg (hρ0 i).le _)`. Take `⟨j, hj⟩` from `hsupp x hx`.

Use `set y := (fun i => centralUnif F (d i) ^ j i) * x with hy`. Establish `hcy` using `hβ j x`. Establish `hprod : ‖∏ i, β i ^ j i‖ = ∏ i, ρ i ^ ((d i : ℤ) * j i)`. Rewrite using `[norm_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_zpow, ← hρd i, ← _root_.zpow_mul]`. Establish `hprod0 : 0 < ∏ i, ρ i ^ ((d i : ℤ) * j i)` using `Finset.prod_pos fun i _ => zpow_pos (hρ0 i) _`. Establish `hcx : ‖c x‖ = ‖c y‖ * ∏ i, ρ i ^ (-((d i : ℤ) * j i))`. Establish `: ‖c y‖ = (∏ i, ρ i ^ ((d i : ℤ) * j i)) * ‖c x‖`. Rewrite using `[hcy, norm_mul, hprod]`.

Rewrite using `[this, mul_comm (∏ i, _), mul_assoc, ← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_congr rfl fun i _ => (zpow_add₀ (hρ0 i).ne' _ _).symm]`. Simplify using the standard rewrite rules. Establish `hord : ∀ i, ordDet (y i) = j i * d i + ordDet (x i)` using `fun i => ordDet_centralUnif_zpow_mul (j i) (x i)`. Establish `hyC : ∀ i, y i ∈ (fun y : ∀ i, GL (Fin (d i)) F => y i) '' C` using `fun i => ⟨y, hj, rfl⟩`.

Establish `hfac : ∀ i, ρ i ^ (-((d i : ℤ) * j i)) ≤ D i * ρ i ^ ordDet (x i)` using `fun i => by`. Establish `e : -((d i : ℤ) * j i) = ordDet (x i) + -ordDet (y i)` using `by rw [hord]; ring`. Rewrite using `[e, zpow_add₀ (hρ0 i).ne', mul_comm]`. Use `mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (hρ0 i).le _)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hab i _ (hyC i)`.

Break down `le_or_gt 1 (ρ i) with hρ1 | hρ1` into its components or cases. Establish `: ρ i ^ (-ordDet (y i)) ≤ ρ i ^ (-a i)` using `zpow_le_zpow_right₀ hρ1 (by linarith)`. Combine the linear relations using `[zpow_nonneg (hρ0 i).le (-b i)]`. Establish `: ρ i ^ (-ordDet (y i)) ≤ ρ i ^ (-b i)` using `zpow_le_zpow_right_of_le_one₀ (hρ0 i) hρ1.le (by linarith)`. Combine the linear relations using `[zpow_nonneg (hρ0 i).le (-a i)]`.

Rewrite using `[hcx]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound_of_central [∀ i, NeZero (d i)] {c : (∀ i, GL (Fin (d i)) F) → ℂ}
    (hc : Continuous c) {β : ι → ℂ} (hβ0 : ∀ i, β i ≠ 0)
    (hβ : ∀ (j : ι → ℤ) x, c ((fun i => centralUnif F (d i) ^ j i) * x) = (∏ i, β i ^ j i) * c x)
    {C : Set (∀ i, GL (Fin (d i)) F)} (hC : IsCompact C)
    (hsupp : ∀ x, c x ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖c x‖ ≤ M * ∏ i, (‖β i‖ ^ ((d i : ℝ)⁻¹)) ^ ordDet (x i) := by
  classical
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have hB0 : ∀ x ∈ C, 0 ≤ B := fun x hx => (norm_nonneg _).trans (hB x hx)
  set ρ : ι → ℝ := fun i => ‖β i‖ ^ ((d i : ℝ)⁻¹) with hρ
  have hρ0 : ∀ i, 0 < ρ i := fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 (hβ0 i)) _
  have hρd : ∀ i, ρ i ^ (d i : ℤ) = ‖β i‖ := fun i => by
    rw [zpow_natCast, hρ]
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      inv_mul_cancel₀ (by exact_mod_cast NeZero.ne (d i)), Real.rpow_one]
  have hCi : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C) := fun i =>
    hC.image (continuous_apply i)
  choose a b hab using fun i => exists_bounds_ordDet (hCi i)
  set D : ι → ℝ := fun i => ρ i ^ (-a i) + ρ i ^ (-b i) with hD
  have hD0 : ∀ i, 0 ≤ D i := fun i => add_nonneg (zpow_nonneg (hρ0 i).le _)
    (zpow_nonneg (hρ0 i).le _)
  by_cases hCe : C.Nonempty
  swap
  · refine ⟨0, le_rfl, fun x => ?_⟩
    by_cases hx : c x = 0
    · simp [hx]
    · obtain ⟨j, hj⟩ := hsupp x hx
      exact absurd ⟨_, hj⟩ hCe
  obtain ⟨x₀, hx₀⟩ := hCe
  refine ⟨B * ∏ i, D i, mul_nonneg (hB0 x₀ hx₀) (Finset.prod_nonneg fun i _ => hD0 i),
    fun x => ?_⟩
  by_cases hx : c x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg (mul_nonneg (hB0 x₀ hx₀) (Finset.prod_nonneg fun i _ => hD0 i))
      (Finset.prod_nonneg fun i _ => zpow_nonneg (hρ0 i).le _)
  obtain ⟨j, hj⟩ := hsupp x hx
  set y := (fun i => centralUnif F (d i) ^ j i) * x with hy
  have hcy := hβ j x
  have hprod : ‖∏ i, β i ^ j i‖ = ∏ i, ρ i ^ ((d i : ℤ) * j i) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_zpow, ← hρd i, ← _root_.zpow_mul]
  have hprod0 : 0 < ∏ i, ρ i ^ ((d i : ℤ) * j i) :=
    Finset.prod_pos fun i _ => zpow_pos (hρ0 i) _
  have hcx : ‖c x‖ = ‖c y‖ * ∏ i, ρ i ^ (-((d i : ℤ) * j i)) := by
    have : ‖c y‖ = (∏ i, ρ i ^ ((d i : ℤ) * j i)) * ‖c x‖ := by
      rw [hcy, norm_mul, hprod]
    rw [this, mul_comm (∏ i, _), mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun i _ => (zpow_add₀ (hρ0 i).ne' _ _).symm]
    simp
  have hord : ∀ i, ordDet (y i) = j i * d i + ordDet (x i) := fun i =>
    ordDet_centralUnif_zpow_mul (j i) (x i)
  have hyC : ∀ i, y i ∈ (fun y : ∀ i, GL (Fin (d i)) F => y i) '' C := fun i => ⟨y, hj, rfl⟩
  have hfac : ∀ i, ρ i ^ (-((d i : ℤ) * j i)) ≤ D i * ρ i ^ ordDet (x i) := fun i => by
    have e : -((d i : ℤ) * j i) = ordDet (x i) + -ordDet (y i) := by rw [hord]; ring
    rw [e, zpow_add₀ (hρ0 i).ne', mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (hρ0 i).le _)
    obtain ⟨h1, h2⟩ := hab i _ (hyC i)
    rcases le_or_gt 1 (ρ i) with hρ1 | hρ1
    · have : ρ i ^ (-ordDet (y i)) ≤ ρ i ^ (-a i) := zpow_le_zpow_right₀ hρ1 (by linarith)
      linarith [zpow_nonneg (hρ0 i).le (-b i)]
    · have : ρ i ^ (-ordDet (y i)) ≤ ρ i ^ (-b i) :=
        zpow_le_zpow_right_of_le_one₀ (hρ0 i) hρ1.le (by linarith)
      linarith [zpow_nonneg (hρ0 i).le (-a i)]
  rw [hcx]
  calc ‖c y‖ * ∏ i, ρ i ^ (-((d i : ℤ) * j i)) ≤ B * ∏ i, (D i * ρ i ^ ordDet (x i)) :=
        mul_le_mul (hB y hj) (Finset.prod_le_prod (fun i _ => zpow_nonneg (hρ0 i).le _)
          fun i _ => hfac i) (Finset.prod_nonneg fun i _ => zpow_nonneg (hρ0 i).le _)
          (hB0 x₀ hx₀)
    _ = B * (∏ i, D i) * ∏ i, ρ i ^ ordDet (x i) := by rw [Finset.prod_mul_distrib]; ring

/- English proof (translation)
Rewrite using `[← Real.rpow_logb (by linarith) hq.ne' hρ, ← Real.rpow_add (by linarith)]`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)`.
-/
theorem rpow_neg_mul_lt_one {q ρ σ : ℝ} (hq : 1 < q) (hρ : 0 < ρ) (h : Real.logb q ρ < σ) :
    q ^ (-σ) * ρ < 1 := by
  rw [← Real.rpow_logb (by linarith) hq.ne' hρ, ← Real.rpow_add (by linarith)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

variable [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hq : (0 : ℝ) < LocalField.residueCard F`. Conclude with `(Nat.pos_of_ne_zero LocalField.residueCard_ne_zero)` after adjusting the coercions. Use `set r : ι → ℝ := fun i => (LocalField.residueCard F : ℝ) ^ (-(s i).re) * ρ i with hr`. Establish `hr0 : ∀ i, 0 < r i` using `fun i => mul_pos (Real.rpow_pos_of_pos hq _) (hρ0 i)`. Use `set g : ∀ i, GL (Fin (d i)) F → ℝ := fun i => (centralSat (d i) (C i)).indicator (fun y => ‖Ψ i (y : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet y) with hg`.

Establish `hgi : ∀ i, Integrable (g i) (μ i)` using `fun i => integrable_block (μ i) (hΨ i) (hC i) (hr0 i) (hs i)`. Establish `hG : Integrable (fun x : ∀ i, GL (Fin (d i)) F => M * ∏ i, g i (x i)) (Measure.pi μ)` using `(Integrable.fintype_prod_dep hgi).const_mul M`. Establish `hcont : Continuous fun x : ∀ i, GL (Fin (d i)) F => (∏ i, Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) (s i)) * c x`. Use `Continuous.mul (continuous_finsetProd _ fun i _ => ?_) hc` and prove the remaining obligations. Conclude with `((hΨ i).1.continuous.comp (Units.continuous_val.comp (continuous_apply i))).mul ((continuous_detPow (s i)).comp (continuous_apply i))`.

Use `hG.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hcx : c x = 0`. Rewrite using `[hcx, mul_zero, norm_zero]`. Conclude with `mul_nonneg hM (Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (zpow_nonneg (hr0 i).le _)) _)`. Establish `hmem` using `hCs x hcx`.

Establish `hgx : ∀ i, g i (x i) = ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet (x i)` using `fun i => Set.indicator_of_mem (hmem i) _`. Simplify using `only [hgx]`. Rewrite using `[norm_mul, norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul (le_of_eq (Finset.prod_congr rfl fun i _ => ?_)) (hbound x) (norm_nonneg _) (Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (zpow_nonneg (Real.rpow_pos_of_pos hq _).le _))` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_detPow]`. Use `_ = M * ∏ i, ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet (x i) := by`. Rewrite using `[mul_left_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hr, mul_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_of_bound [∀ i, NeZero (d i)] (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, (μ i).IsHaarMeasure] {Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ}
    (hΨ : ∀ i, IsSchwartzBruhat (Ψ i)) {c : (∀ i, GL (Fin (d i)) F) → ℂ} (hc : Continuous c)
    {C : ∀ i, Set (GL (Fin (d i)) F)} (hC : ∀ i, IsCompact (C i))
    (hCs : ∀ x, c x ≠ 0 → ∀ i, x i ∈ centralSat (d i) (C i)) {M : ℝ} (hM : 0 ≤ M) {ρ : ι → ℝ}
    (hρ0 : ∀ i, 0 < ρ i) (hbound : ∀ x, ‖c x‖ ≤ M * ∏ i, ρ i ^ ordDet (x i)) (s : ι → ℂ)
    (hs : ∀ i, (LocalField.residueCard F : ℝ) ^ (-(s i).re) * ρ i < 1) :
    Integrable (fun x : ∀ i, GL (Fin (d i)) F =>
      (∏ i, Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) (s i)) * c x)
      (Measure.pi μ) := by
  classical
  have hq : (0 : ℝ) < LocalField.residueCard F := by
    exact_mod_cast (Nat.pos_of_ne_zero LocalField.residueCard_ne_zero)
  set r : ι → ℝ := fun i => (LocalField.residueCard F : ℝ) ^ (-(s i).re) * ρ i with hr
  have hr0 : ∀ i, 0 < r i := fun i => mul_pos (Real.rpow_pos_of_pos hq _) (hρ0 i)
  set g : ∀ i, GL (Fin (d i)) F → ℝ := fun i => (centralSat (d i) (C i)).indicator
    (fun y => ‖Ψ i (y : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet y) with hg
  have hgi : ∀ i, Integrable (g i) (μ i) := fun i =>
    integrable_block (μ i) (hΨ i) (hC i) (hr0 i) (hs i)
  have hG : Integrable (fun x : ∀ i, GL (Fin (d i)) F => M * ∏ i, g i (x i)) (Measure.pi μ) :=
    (Integrable.fintype_prod_dep hgi).const_mul M
  have hcont : Continuous fun x : ∀ i, GL (Fin (d i)) F =>
      (∏ i, Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) (s i)) * c x := by
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) hc
    exact ((hΨ i).1.continuous.comp (Units.continuous_val.comp (continuous_apply i))).mul
      ((continuous_detPow (s i)).comp (continuous_apply i))
  refine hG.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hcx : c x = 0
  · rw [hcx, mul_zero, norm_zero]
    exact mul_nonneg hM (Finset.prod_nonneg fun i _ => Set.indicator_nonneg
      (fun y _ => mul_nonneg (norm_nonneg _) (zpow_nonneg (hr0 i).le _)) _)
  have hmem := hCs x hcx
  have hgx : ∀ i, g i (x i) = ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet (x i) :=
    fun i => Set.indicator_of_mem (hmem i) _
  simp only [hgx]
  rw [norm_mul, norm_prod]
  calc (∏ i, ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F) * detPow (x i) (s i)‖) * ‖c x‖
      ≤ (∏ i, ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F)‖ *
          ((LocalField.residueCard F : ℝ) ^ (-(s i).re)) ^ ordDet (x i)) *
        (M * ∏ i, ρ i ^ ordDet (x i)) := by
        refine mul_le_mul (le_of_eq (Finset.prod_congr rfl fun i _ => ?_)) (hbound x)
          (norm_nonneg _) (Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _)
            (zpow_nonneg (Real.rpow_pos_of_pos hq _).le _))
        rw [norm_mul, norm_detPow]
    _ = M * ∏ i, ‖Ψ i (x i : Matrix (Fin (d i)) (Fin (d i)) F)‖ * r i ^ ordDet (x i) := by
        rw [mul_left_comm, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hr, mul_zpow]
        ring

/- English proof (translation)
Use `set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef`. Establish `hq1 : 1 < q` using `by rw [hqdef]; exact_mod_cast (LocalField.one_lt_residueCard (K := F))`. Use `set L : ι → ℝ := fun i => Real.logb q (‖α i‖ ^ ((d i : ℝ)⁻¹)) with hL`. Use `⟨∑ i, |L i|, fun Ψ hΨ w ℓ hℓ => ?_⟩` and prove the remaining obligations. Establish `hLle : ∀ i, |L i| ≤ ∑ i, |L i|` using `fun i => Finset.single_le_sum (f := fun i => |L i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)`.

Establish `hw : w ∈ smoothVectors ρ` using `hρ w`. Establish `hcont : Continuous fun x : ∀ i, GL (Fin (d i)) F => ℓ (ρ (x, 1) w)` using `(continuous_coeff_of_smooth ρ hw ℓ).comp (continuous_id.prodMk continuous_const)`. Take `⟨C, hC, hCs⟩` from `hsupp w ℓ hℓ`. Establish `hCi : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C)` using `fun i => hC.image (continuous_apply i)`. Establish `hρα : ∀ i, 0 < ‖α i‖ ^ ((d i : ℝ)⁻¹)` using `fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 (hα0 i)) _`.

Establish `hmul : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F) (v : W), ρ ((fun i => centralUnif F (d i) ^ j i) * x, 1) v = (∏ i, α i ^ j i) • ρ (x, 1) v`. Introduce `j x v`. Rewrite using `[show ((fun i => centralUnif F (d i) ^ j i) * x, (1 : H)) = ((fun i => centralUnif F (d i) ^ j i), (1 : H)) * (x, 1) by rw [Prod.mk_mul_mk, mul_one], map_mul, Module.End.mul_apply, apply_centralPow ρ hα0 hα]`. Prove the components needed by the constructor for the conclusion. Introduce `s hs`.

Take `⟨M, hM, hbound⟩` from `exists_bound_of_central hcont hα0 (fun j x => by rw [hmul, map_smul, smul_eq_mul]) hC hCs`. Use `integrable_of_bound μ hΨ hcont hCi ?_ hM hρα hbound (fun _ => s) fun i => ?_` and prove the remaining obligations. Introduce `x hx i`. Take `⟨j, hj⟩` from `hCs x hx`. Conclude with `⟨j i, _, hj, rfl⟩`.

Use `rpow_neg_mul_lt_one hq1 (hρα i) ?_ show L i < s.re` and prove the remaining obligations. Combine the linear relations using `[le_abs_self (L i), hLle i]`. Introduce `s hs`. Establish `hcont' : Continuous fun x : ∀ i, GL (Fin (d i)) F => ℓ (ρ (x⁻¹, 1) w)` using `hcont.comp continuous_inv`. Establish `hinvz : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F), ((fun i => centralUnif F (d i) ^ j i) * x)⁻¹ = (fun i => centralUnif F (d i) ^ (-j) i) * x⁻¹`.

Introduce `j x`. Use function extensionality and compare the values at `i`. Use `show (centralUnif F (d i) ^ j i * x i)⁻¹ = centralUnif F (d i) ^ (-j i) * (x i)⁻¹`. Rewrite using `[_root_.mul_inv_rev, ← _root_.zpow_neg, centralUnif_zpow_mul_comm]`. Establish `hβ : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F), ℓ (ρ (((fun i => centralUnif F (d i) ^ j i) * x)⁻¹, 1) w) = (∏ i, (α i)⁻¹ ^ j i) * ℓ (ρ (x⁻¹, 1) w)`.

Introduce `j x`. Rewrite using `[hinvz, hmul, map_smul, smul_eq_mul]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.neg_apply, _root_.inv_zpow']`.

Establish `hsupp' : ∀ x : ∀ i, GL (Fin (d i)) F, ℓ (ρ (x⁻¹, 1) w) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C⁻¹`. Introduce `x hx`. Take `⟨j, hj⟩` from `hCs _ hx`. Use `⟨-j, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_inv, hinvz, neg_neg]`.

Conclude with `hj`. Establish `hα0' : ∀ i, (α i)⁻¹ ≠ 0` using `fun i => inv_ne_zero (hα0 i)`. Take `⟨M, hM, hbound⟩` from `exists_bound_of_central hcont' hα0' hβ hC.inv hsupp'`. Establish `hρα' : ∀ i, 0 < ‖(α i)⁻¹‖ ^ ((d i : ℝ)⁻¹)` using `fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 (hα0' i)) _`. Establish `hCi' : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C⁻¹)` using `fun i => hC.inv.image (continuous_apply i)`.

Use `integrable_of_bound μ hΨ hcont' hCi' ?_ hM hρα' hbound (fun i => (d i : ℂ) - s) fun i => ?_` and prove the remaining obligations. Introduce `x hx i`. Take `⟨j, hj⟩` from `hsupp' x hx`. Conclude with `⟨j i, _, hj, rfl⟩`. Use `rpow_neg_mul_lt_one hq1 (hρα' i) ?_` and prove the remaining obligations.

Establish `hlog : Real.logb q (‖(α i)⁻¹‖ ^ ((d i : ℝ)⁻¹)) = -L i`. Rewrite using `[norm_inv, Real.inv_rpow (norm_nonneg _), Real.logb_inv]`. Rewrite using `[hlog]`. Establish `hd : (1 : ℝ) ≤ d i` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne (d i))`. Use `show -L i < ((d i : ℂ) - s).re`.

Rewrite using `[Complex.sub_re, Complex.natCast_re]`. Combine the linear relations using `[neg_abs_le (L i), hLle i]`.
-/
theorem exists_integrable_multi [∀ i, NeZero (d i)] [TopologicalSpace H] [IsTopologicalGroup H]
    (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W) (hρ : IsSmooth ρ) {α : ι → ℂ}
    (hα0 : ∀ i, α i ≠ 0) (hα : ∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
      ∃ C : Set (∀ i, GL (Fin (d i)) F), IsCompact C ∧
        ∀ x, ℓ (ρ (x, 1) v) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C)
    (μ : ∀ i, Measure (GL (Fin (d i)) F)) [∀ i, (μ i).IsHaarMeasure] :
    ∃ s₁ : ℝ, ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ, (∀ i, IsSchwartzBruhat (Ψ i)) →
      ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        (∀ s : ℂ, s₁ < s.re → Integrable (multiA ρ Ψ w ℓ s) (Measure.pi μ)) ∧
        (∀ s : ℂ, s.re < -s₁ → Integrable (multiB ρ Ψ w ℓ s) (Measure.pi μ)) := by
  classical
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq1 : 1 < q := by rw [hqdef]; exact_mod_cast (LocalField.one_lt_residueCard (K := F))
  set L : ι → ℝ := fun i => Real.logb q (‖α i‖ ^ ((d i : ℝ)⁻¹)) with hL
  refine ⟨∑ i, |L i|, fun Ψ hΨ w ℓ hℓ => ?_⟩
  have hLle : ∀ i, |L i| ≤ ∑ i, |L i| := fun i =>
    Finset.single_le_sum (f := fun i => |L i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hw : w ∈ smoothVectors ρ := hρ w
  have hcont : Continuous fun x : ∀ i, GL (Fin (d i)) F => ℓ (ρ (x, 1) w) :=
    (continuous_coeff_of_smooth ρ hw ℓ).comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC, hCs⟩ := hsupp w ℓ hℓ
  have hCi : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C) := fun i =>
    hC.image (continuous_apply i)
  have hρα : ∀ i, 0 < ‖α i‖ ^ ((d i : ℝ)⁻¹) := fun i =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (hα0 i)) _
  have hmul : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F) (v : W),
      ρ ((fun i => centralUnif F (d i) ^ j i) * x, 1) v = (∏ i, α i ^ j i) • ρ (x, 1) v := by
    intro j x v
    rw [show ((fun i => centralUnif F (d i) ^ j i) * x, (1 : H)) =
      ((fun i => centralUnif F (d i) ^ j i), (1 : H)) * (x, 1) by rw [Prod.mk_mul_mk, mul_one],
      map_mul, Module.End.mul_apply, apply_centralPow ρ hα0 hα]
  constructor
  · intro s hs
    obtain ⟨M, hM, hbound⟩ := exists_bound_of_central hcont hα0
      (fun j x => by rw [hmul, map_smul, smul_eq_mul]) hC hCs
    refine integrable_of_bound μ hΨ hcont hCi ?_ hM hρα hbound (fun _ => s) fun i => ?_
    · intro x hx i
      obtain ⟨j, hj⟩ := hCs x hx
      exact ⟨j i, _, hj, rfl⟩
    · refine rpow_neg_mul_lt_one hq1 (hρα i) ?_
      show L i < s.re
      linarith [le_abs_self (L i), hLle i]
  · intro s hs

    have hcont' : Continuous fun x : ∀ i, GL (Fin (d i)) F => ℓ (ρ (x⁻¹, 1) w) :=
      hcont.comp continuous_inv
    have hinvz : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F),
        ((fun i => centralUnif F (d i) ^ j i) * x)⁻¹ =
          (fun i => centralUnif F (d i) ^ (-j) i) * x⁻¹ := by
      intro j x
      funext i
      show (centralUnif F (d i) ^ j i * x i)⁻¹ = centralUnif F (d i) ^ (-j i) * (x i)⁻¹
      rw [_root_.mul_inv_rev, ← _root_.zpow_neg, centralUnif_zpow_mul_comm]
    have hβ : ∀ (j : ι → ℤ) (x : ∀ i, GL (Fin (d i)) F),
        ℓ (ρ (((fun i => centralUnif F (d i) ^ j i) * x)⁻¹, 1) w) =
          (∏ i, (α i)⁻¹ ^ j i) * ℓ (ρ (x⁻¹, 1) w) := by
      intro j x
      rw [hinvz, hmul, map_smul, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.neg_apply, _root_.inv_zpow']
    have hsupp' : ∀ x : ∀ i, GL (Fin (d i)) F, ℓ (ρ (x⁻¹, 1) w) ≠ 0 →
        ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C⁻¹ := by
      intro x hx
      obtain ⟨j, hj⟩ := hCs _ hx
      refine ⟨-j, ?_⟩
      rw [Set.mem_inv, hinvz, neg_neg]
      exact hj
    have hα0' : ∀ i, (α i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hα0 i)
    obtain ⟨M, hM, hbound⟩ := exists_bound_of_central hcont' hα0' hβ hC.inv hsupp'
    have hρα' : ∀ i, 0 < ‖(α i)⁻¹‖ ^ ((d i : ℝ)⁻¹) := fun i =>
      Real.rpow_pos_of_pos (norm_pos_iff.2 (hα0' i)) _
    have hCi' : ∀ i, IsCompact ((fun y : ∀ i, GL (Fin (d i)) F => y i) '' C⁻¹) := fun i =>
      hC.inv.image (continuous_apply i)
    refine integrable_of_bound μ hΨ hcont' hCi' ?_ hM hρα' hbound (fun i => (d i : ℂ) - s)
      fun i => ?_
    · intro x hx i
      obtain ⟨j, hj⟩ := hsupp' x hx
      exact ⟨j i, _, hj, rfl⟩
    · refine rpow_neg_mul_lt_one hq1 (hρα' i) ?_
      have hlog : Real.logb q (‖(α i)⁻¹‖ ^ ((d i : ℝ)⁻¹)) = -L i := by
        rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.logb_inv]
      rw [hlog]
      have hd : (1 : ℝ) ≤ d i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne (d i))
      show -L i < ((d i : ℂ) - s).re
      rw [Complex.sub_re, Complex.natCast_re]
      linarith [neg_abs_le (L i), hLle i]

end Multi

end GodementJacquet

end GroundTheory.Automorphic
