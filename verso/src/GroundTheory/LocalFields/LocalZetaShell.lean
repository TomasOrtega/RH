import Mathlib
import GroundTheory.LocalFields.LocalFourier

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Order

variable (K) in
/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem exists_units_ord_eq_one : ∃ π : Kˣ, ord (π : K) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩

variable (K) in

def unifUnit : Kˣ := (exists_units_ord_eq_one K).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ord_unifUnit : ord (unifUnit K : K) = 1 := (exists_units_ord_eq_one K).choose_spec

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ord_units_mul (u v : Kˣ) : ord ((u * v : Kˣ) : K) = ord (u : K) + ord (v : K) := by
  rw [Units.val_mul, ord_mul u.ne_zero v.ne_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ord_units_zpow (u : Kˣ) (k : ℤ) : ord ((u ^ k : Kˣ) : K) = k * ord (u : K) := by
  rw [Units.val_zpow_eq_zpow_val]
  simp [ord, map_zpow₀, WithZero.log_zpow]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ord_units_inv (u : Kˣ) : ord ((u⁻¹ : Kˣ) : K) = -ord (u : K) := by
  rw [Units.val_inv_eq_inv_val, ord_inv u.ne_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ord_unifUnit_zpow (k : ℤ) : ord ((unifUnit K ^ k : Kˣ) : K) = k := by
  rw [ord_units_zpow, ord_unifUnit, mul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_eq_one_iff_ord_eq_zero {x : K} (hx : x ≠ 0) :
    valuation K x = 1 ↔ ord x = 0 := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  have h1 := mem_valBall_iff_le_ord (n := 1) hx
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  rw [mem_valBall_one_iff] at h1
  constructor
  · intro h
    have a := h0.mp h.le
    have b : ¬ 1 ≤ ord x := fun hb => (h1.mpr hb).ne h
    omega
  · intro h
    refine le_antisymm (h0.mpr h.ge) (not_lt.mp fun hl => ?_)
    have := h1.mp hl
    omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_unitFiltrationUnits_zero_iff_ord {u : Kˣ} :
    u ∈ unitFiltrationUnits K 0 ↔ ord (u : K) = 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, valuation_eq_one_iff_ord_eq_zero u.ne_zero]

end Order

section Shell

variable (K) in

def ordShell (k : ℤ) : Set Kˣ := {u | ord (u : K) = k}

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_ordShell {k : ℤ} {u : Kˣ} : u ∈ ordShell K k ↔ ord (u : K) = k := Iff.rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ordShell_zero : ordShell K 0 = (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext u
  rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff_ord]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem mul_mem_ordShell_iff (v : Kˣ) {k : ℤ} {u : Kˣ} :
    v * u ∈ ordShell K (ord (v : K) + k) ↔ u ∈ ordShell K k := by
  simp only [mem_ordShell, ord_units_mul]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pairwise_disjoint_ordShell : Pairwise (Function.onFun Disjoint (ordShell K)) := by
  intro i j hij
  exact Set.disjoint_left.mpr fun u hi hj => hij (hi.symm.trans hj)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iUnion_ordShell : ⋃ k, ordShell K k = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_iUnion.mpr ⟨_, rfl⟩

end Shell

section Measure

variable [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurable_units_val : Measurable (Units.val : Kˣ → K) :=
  measurableEmbedding_units_val.measurable

instance instMeasurableMul₂UnitsLocalField : MeasurableMul₂ Kˣ where
  measurable_mul := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    have : (Units.val ∘ fun p : Kˣ × Kˣ => p.1 * p.2) = fun p => (p.1 : K) * (p.2 : K) := by
      funext p
      simp
    rw [this]
    exact (measurable_units_val.comp measurable_fst).mul (measurable_units_val.comp measurable_snd)

instance instBorelSpaceUnitsLocalField : BorelSpace Kˣ := by
  refine ⟨?_⟩
  calc (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := by
        rw [← BorelSpace.measurable_eq]
        rfl
    _ = borel Kˣ := by
        rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem measurableSet_ordShell (k : ℤ) : MeasurableSet (ordShell K k) := by
  have : ordShell K k = Units.val ⁻¹' ((valBall K k : Set K) \ valBall K (k + 1)) := by
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [this]
  exact ((measurableSet_valBall k).diff (measurableSet_valBall (k + 1))).preimage
    measurable_units_val

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.
-/
theorem multHaar_ordShell (k : ℤ) : multHaar K (ordShell K k) = 1 := by
  have h : (fun u => unifUnit K ^ k * u) ⁻¹' ordShell K k = ordShell K 0 := by
    ext u
    have := mul_mem_ordShell_iff (K := K) (unifUnit K ^ k) (k := 0) (u := u)
    rwa [ord_unifUnit_zpow, add_zero] at this
  rw [← measure_preimage_mul (multHaar K) (unifUnit K ^ k), h, ordShell_zero,
    multHaar_unitFiltrationUnits_zero]

instance instSigmaFiniteMultHaar : SigmaFinite (multHaar K) := by
  refine Measure.sigmaFinite_of_countable (S := Set.range (ordShell K)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [multHaar_ordShell]
    exact ENNReal.one_lt_top
  · rw [Set.sUnion_range, iUnion_ordShell]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lintegral_multHaar_eq_tsum (g : Kˣ → ℝ≥0∞) :
    ∫⁻ u, g u ∂multHaar K = ∑' k : ℤ, ∫⁻ u in ordShell K k, g u ∂multHaar K := by
  rw [← lintegral_iUnion measurableSet_ordShell pairwise_disjoint_ordShell, iUnion_ordShell,
    Measure.restrict_univ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.
-/
theorem lintegral_multHaar_le_tsum (g : Kˣ → ℝ≥0∞) (a : ℤ → ℝ≥0∞)
    (h : ∀ u, g u ≤ a (ord (u : K))) : ∫⁻ u, g u ∂multHaar K ≤ ∑' k, a k := by
  rw [lintegral_multHaar_eq_tsum]
  refine ENNReal.tsum_le_tsum fun k => ?_
  calc ∫⁻ u in ordShell K k, g u ∂multHaar K ≤ ∫⁻ _ in ordShell K k, a k ∂multHaar K :=
        setLIntegral_mono' (measurableSet_ordShell k) fun u hu => (h u).trans_eq (by rw [hu])
    _ = a k := by rw [setLIntegral_const, multHaar_ordShell, mul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem hasSum_setIntegral_ordShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Kˣ → E} (hF : Integrable F (multHaar K)) :
    HasSum (fun k : ℤ => ∫ u in ordShell K k, F u ∂multHaar K) (∫ u, F u ∂multHaar K) := by
  have := hasSum_integral_iUnion (μ := multHaar K) (measurableSet_ordShell (K := K))
    (pairwise_disjoint_ordShell (K := K)) (by rw [iUnion_ordShell]; exact hF.integrableOn)
  rwa [iUnion_ordShell, Measure.restrict_univ] at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem setIntegral_ordShell_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Kˣ → E) (v : Kˣ) (k : ℤ) :
    ∫ u in ordShell K (ord (v : K) + k), F u ∂multHaar K =
      ∫ u in ordShell K k, F (v * u) ∂multHaar K := by
  rw [← integral_indicator (measurableSet_ordShell _), ← integral_indicator (measurableSet_ordShell _),
    ← integral_mul_left_eq_self _ v]
  congr 1
  funext u
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((mul_mem_ordShell_iff v).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt (mul_mem_ordShell_iff v).mp hu)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.
-/
theorem integral_eq_zero_of_mul_eq {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (F : G → ℂ) (v : G) {a : ℂ} (ha : a ≠ 1)
    (hF : ∀ u, F (v * u) = a * F u) : ∫ u, F u ∂μ = 0 := by
  refine eq_zero_of_eq_mul_of_ne_one ha ?_
  calc ∫ u, F u ∂μ = ∫ u, F (v * u) ∂μ := (integral_mul_left_eq_self F v).symm
    _ = ∫ u, a * F u ∂μ := by simp only [hF]
    _ = a * ∫ u, F u ∂μ := integral_const_mul a _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem setIntegral_ordShell_eq_zero (F : Kˣ → ℂ) {v : Kˣ} (hv : ord (v : K) = 0) {a : ℂ}
    (ha : a ≠ 1) (k : ℤ) (hF : ∀ u ∈ ordShell K k, F (v * u) = a * F u) :
    ∫ u in ordShell K k, F u ∂multHaar K = 0 := by
  rw [← integral_indicator (measurableSet_ordShell k)]
  refine integral_eq_zero_of_mul_eq _ _ v ha fun u => ?_
  have hiff : v * u ∈ ordShell K k ↔ u ∈ ordShell K k := by
    have := mul_mem_ordShell_iff (K := K) v (k := k) (u := u)
    rwa [hv, zero_add] at this
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hiff.mpr hu), hF u hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hiff.mp hu), mul_zero]

end Measure

section Power

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem residueCard_pos_real : (0 : ℝ) < residueCard K := by
  exact_mod_cast zero_lt_one.trans one_lt_residueCard

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem residueCard_ne_zero_complex : (residueCard K : ℂ) ≠ 0 := by
  exact_mod_cast residueCard_ne_zero

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Put the polynomial expressions in normal form.
-/
theorem modulus_cpow_eq_zpow (u : Kˣ) (s : ℂ) :
    ((modulus (u : K) : ℝ) : ℂ) ^ s = ((residueCard K : ℂ) ^ (-s)) ^ ord (u : K) := by
  have hq := residueCard_pos_real (K := K)
  rw [modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  have hpos : (0 : ℝ) < (residueCard K : ℝ) ^ (-ord (u : K)) := zpow_pos hq _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul,
    ← Complex.ofReal_log hpos.le, Real.log_zpow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hq.le]
  push_cast
  ring_nf

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_qpow (s : ℂ) : ‖(residueCard K : ℂ) ^ (-s)‖ = (residueCard K : ℝ) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos residueCard_pos_real,
    Complex.neg_re]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem qpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex]
  exact Complex.exp_ne_zero _

end Power

end GroundTheory.LocalField
