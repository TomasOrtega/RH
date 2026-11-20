import Mathlib
import GroundTheory.LocalFields.LocalZetaShell

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Decomposition

/- English proof (translation)
Rewrite using `[mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unifUnit_zpow_neg_mul_mem (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]
  ring

/- English proof (translation)
Rewrite using `[← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]`.
-/
theorem eq_unifUnit_zpow_mul (u : Kˣ) :
    u = unifUnit K ^ ord (u : K) * (unifUnit K ^ (-ord (u : K)) * u) := by
  rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/- English proof (translation)
Establish `hS : IsCompact ((valBall K 0 : Set K) \ valBall K 1)` using `(isCompact_valBall 0).diff (isOpen_valBall 1)`. Establish `heq : (unitFiltrationUnits K 0 : Set Kˣ) = Units.val ⁻¹' ((valBall K 0 : Set K) \ valBall K 1)`. Rewrite using `[← ordShell_zero]`. Use extensionality with `u`. Simplify using `only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe, mem_valBall_iff_le_ord u.ne_zero]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[heq]`. Use `Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS ?_` and prove the remaining obligations. Introduce and unpack `x ⟨-, hx⟩`. Establish `hx0 : x ≠ 0` using `fun h => hx (h ▸ zero_mem _)`.

Conclude with `⟨Units.mk0 x hx0, rfl⟩`.
-/
theorem isCompact_unitFiltrationUnits_zero :
    IsCompact (unitFiltrationUnits K 0 : Set Kˣ) := by
  have hS : IsCompact ((valBall K 0 : Set K) \ valBall K 1) :=
    (isCompact_valBall 0).diff (isOpen_valBall 1)
  have heq : (unitFiltrationUnits K 0 : Set Kˣ) =
      Units.val ⁻¹' ((valBall K 0 : Set K) \ valBall K 1) := by
    rw [← ordShell_zero]
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [heq]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS ?_
  rintro x ⟨-, hx⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  exact ⟨Units.mk0 x hx0, rfl⟩

end Decomposition

section QuasiCharacter

variable (χ : Kˣ →* ℂˣ)

def IsUnramifiedChar : Prop := unitFiltrationUnits K 0 ≤ χ.ker

def quasiCharConductor : ℕ := sInf {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}

def quasiCharExponent : ℝ := -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖

variable {χ}

/- English proof (translation)
Use `⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩` and prove the remaining obligations. Conclude with `h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)`.
-/
theorem isUnramifiedChar_iff : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by
  refine ⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩
  exact h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)

/- English proof (translation)
Use `conv_lhs => rw [eq_unifUnit_zpow_mul u]`. Rewrite using `[map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]`.
-/
theorem quasiChar_apply_of_isUnramified (h : IsUnramifiedChar χ) (u : Kˣ) :
    χ u = χ (unifUnit K) ^ ord (u : K) := by
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]

/- English proof (translation)
Rewrite using `[quasiChar_apply_of_isUnramified h, hπ, zpow_one]`.
-/
theorem quasiChar_apply_eq_of_isUnramified (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by
  rw [quasiChar_apply_of_isUnramified h, hπ, zpow_one]

variable (hχ : Continuous χ)
include hχ

/- English proof (translation)
Use `exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_) GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)` and prove the remaining obligations. Take `⟨n, -, hn⟩` from `hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW`. Conclude with `⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩`.
-/
theorem exists_unitFiltrationUnits_le_ker : ∃ n, unitFiltrationUnits K n ≤ χ.ker := by
  refine exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_)
    GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW
  exact ⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩

/- English proof (translation)
The claim follows from `Nat.sInf_mem (exists_unitFiltrationUnits_le_ker hχ)`.
-/
theorem unitFiltrationUnits_quasiCharConductor_le_ker :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker :=
  Nat.sInf_mem (exists_unitFiltrationUnits_le_ker hχ)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `unitFiltrationUnits_quasiCharConductor_le_ker hχ` as an intermediate fact. Rewrite `this` using `[h]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `Nat.eq_zero_of_le_zero (Nat.sInf_le h)`.
-/
theorem quasiCharConductor_eq_zero_iff : quasiCharConductor χ = 0 ↔ IsUnramifiedChar χ := by
  constructor
  · intro h
    have := unitFiltrationUnits_quasiCharConductor_le_ker hχ
    rwa [h] at this
  · intro h
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

/- English proof (translation)
Establish `hc : quasiCharConductor χ ≠ 0` using `mt (quasiCharConductor_eq_zero_iff hχ).mp h`. Establish `hlt : quasiCharConductor χ - 1 < quasiCharConductor χ` using `by omega`. Establish `hnot` using `Nat.notMem_of_lt_sInf hlt`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)`.
-/
theorem exists_apply_ne_one_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) :
    ∃ v ∈ unitFiltrationUnits K (quasiCharConductor χ - 1), χ v ≠ 1 := by
  have hc : quasiCharConductor χ ≠ 0 := mt (quasiCharConductor_eq_zero_iff hχ).mp h
  have hlt : quasiCharConductor χ - 1 < quasiCharConductor χ := by omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  by_contra hcon
  push_neg at hcon
  exact hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)

omit hχ in
/- English proof (translation)
The claim follows from `Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)`.
-/
theorem quasiCharConductor_pos (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ :=
  Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)

/- English proof (translation)
Establish `hcont : Continuous fun v : Kˣ => ‖((χ v : ℂˣ) : ℂ)‖` using `(Units.continuous_val.comp hχ).norm`. Take `⟨C, hC⟩` from `isCompact_unitFiltrationUnits_zero.exists_bound_of_continuousOn hcont.continuousOn`. Establish `key : ∀ v ∈ unitFiltrationUnits K 0, ‖((χ v : ℂˣ) : ℂ)‖ ≤ 1`. Introduce `v hv`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Take `⟨n, hn⟩` from `((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists`. Use `hC (v ^ n) (pow_mem hv n)` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `key u hu`. Establish `h2` using `key u⁻¹ (inv_mem hu)`. Rewrite `h2` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`. Establish `hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖` using `norm_pos_iff.mpr (χ u).ne_zero`. Establish `: 1 ≤ ‖((χ u : ℂˣ) : ℂ)‖` using `by rwa [inv_le_one₀ hpos] at h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_quasiChar_apply_eq_one {u : Kˣ} (hu : u ∈ unitFiltrationUnits K 0) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hcont : Continuous fun v : Kˣ => ‖((χ v : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp hχ).norm
  obtain ⟨C, hC⟩ := isCompact_unitFiltrationUnits_zero.exists_bound_of_continuousOn
    hcont.continuousOn
  have key : ∀ v ∈ unitFiltrationUnits K 0, ‖((χ v : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
    have := hC (v ^ n) (pow_mem hv n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val,
      norm_pow] at this
    linarith
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ u).ne_zero
  have : 1 ≤ ‖((χ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  linarith

/- English proof (translation)
Establish `hq` using `residueCard_pos_real (K := K)`. Establish `hq1 : (residueCard K : ℝ) ≠ 1` using `by exact_mod_cast (one_lt_residueCard (K := K)).ne'`. Establish `hr : 0 < ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖` using `norm_pos_iff.mpr (χ _).ne_zero`. Use `conv_lhs => rw [eq_unifUnit_zpow_mul u]`. Rewrite using `[map_mul, Units.val_mul, norm_mul, norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow, modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul …`.

Rewrite using `[show ((-ord (u : K) : ℤ) : ℝ) * -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ = Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ * (ord (u : K) : ℝ) by push_cast; ring, Real.rpow_mul hq.le, Real.rpow_logb hq hq1 hr]`.
-/
theorem norm_quasiChar_apply (u : Kˣ) :
    ‖((χ u : ℂˣ) : ℂ)‖ = (modulus (u : K) : ℝ) ^ quasiCharExponent χ := by
  have hq := residueCard_pos_real (K := K)
  have hq1 : (residueCard K : ℝ) ≠ 1 := by exact_mod_cast (one_lt_residueCard (K := K)).ne'
  have hr : 0 < ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ _).ne_zero
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, Units.val_mul, norm_mul,
    norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
    Units.val_zpow_eq_zpow_val, norm_zpow, modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow,
    NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
    quasiCharExponent]
  rw [show ((-ord (u : K) : ℤ) : ℝ) * -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ =
      Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ * (ord (u : K) : ℝ) by push_cast; ring,
    Real.rpow_mul hq.le, Real.rpow_logb hq hq1 hr]

omit hχ in
/- English proof (translation)
Establish `: ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹`. Use function extensionality and compare the values at `u`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hχ.inv`.
-/
theorem continuous_quasiChar_inv (hχ : Continuous χ) : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := by
  have : ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
    funext u
    rfl
  rw [this]
  exact hχ.inv

omit hχ in

/- English proof (translation)
Simplify using `only [quasiCharExponent, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, Real.logb_inv, neg_neg]`.
-/
theorem quasiCharExponent_inv : quasiCharExponent χ⁻¹ = -quasiCharExponent χ := by
  simp only [quasiCharExponent, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv,
    Real.logb_inv, neg_neg]

end QuasiCharacter

section ShellIntegral

variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}

open scoped Classical in

/- English proof (translation)
Establish `hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k` using `by rw [ord_unifUnit_zpow, add_zero]`. Establish `e` using `setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0`. Rewrite `e` using `[hk]`. Rewrite using `[e]`. Simplify using `only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]`.

Rewrite using `[integral_const_mul]`. Use `split_ifs with h`. Establish `hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1` using `fun u hu => by`. Rewrite using `[(isUnramifiedChar_iff.mp h) u hu, Units.val_one]`. Rewrite using `[setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const, measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)`. Rewrite using `[setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ)) (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ)) (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]`.
-/
theorem setIntegral_ordShell_quasiChar (hχ : Continuous χ) (k : ℤ) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) ∂multHaar K =
      if IsUnramifiedChar χ then ((χ (unifUnit K) : ℂˣ) : ℂ) ^ k else 0 := by
  have hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k := by rw [ord_unifUnit_zpow, add_zero]
  have e := setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0
  rw [hk] at e
  rw [e]
  simp only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [integral_const_mul]
  split_ifs with h
  · have hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1 := fun u hu => by
      rw [(isUnramifiedChar_iff.mp h) u hu, Units.val_one]
    rw [setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const,
      measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]
  · obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
    rw [setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ))
      (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ))
      (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]

end ShellIntegral

end GroundTheory.LocalField
