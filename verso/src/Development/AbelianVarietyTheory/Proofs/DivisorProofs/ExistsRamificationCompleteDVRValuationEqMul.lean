import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

open scoped WithZero

namespace GlobalTheory.CdvrPlaceVal

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`. Conclude with `HeightOneSpectrum.valuation_le_one _ v`. Introduce `hx`. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (IsDiscreteValuationRing.maximalIdeal T.V) x hx`.

Establish `hu : IsUnit (d : T.V)`. Assume the negation of the conclusion as `hu`. Conclude with `d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)`. Take `⟨u, hu⟩` from `hu`. Use `⟨n * ↑u⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`.
-/
theorem mem_range_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (IsDiscreteValuationRing.maximalIdeal T.V) x hx
    have hu : IsUnit (d : T.V) := by
      by_contra hu
      exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
    obtain ⟨u, hu⟩ := hu
    refine ⟨n * ↑u⁻¹, ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

/- English proof (translation)
Set `v1 : Valuation K ℤᵐ⁰` to `(valV T.V).comap iK`. Establish `hv1 : ∀ z, v1 z = valV T.V (iK z)` using `fun z => rfl`. Establish `hle : ∀ z : K, v1 z ≤ 1 ↔ 𝔓.valuation K z ≤ 1` using `fun z => by`. Rewrite using `[← h z, mem_range_iff_valV_le_one, hv1]`. Establish `hunit : ∀ w : K, 𝔓.valuation K w = 1 → v1 w = 1`.

Introduce `w hw`. Establish `hw0 : w ≠ 0` using `by rintro rfl; simp at hw`. Establish `h0 : v1 w ≠ 0` using `(Valuation.ne_zero_iff _).2 hw0`. Establish `h1 : v1 w ≤ 1` using `(hle w).2 hw.le`. Establish `h2 : v1 w⁻¹ ≤ 1` using `(hle w⁻¹).2 (by rw [map_inv₀, hw, inv_one])`.

Rewrite `h2` using `[map_inv₀]`. Establish `h1'` using `(WithZero.log_le_log h0 one_ne_zero).2 h1`. Establish `h2'` using `(WithZero.log_le_log (inv_ne_zero h0) one_ne_zero).2 h2`. Rewrite `h2'` using `[WithZero.log_inv, WithZero.log_one]`. Rewrite `h1'` using `[WithZero.log_one]`.

Rewrite using `[← WithZero.exp_log h0, show WithZero.log (v1 w) = 0 by omega]`. Both sides reduce to the same expression. Take `⟨ϖ, hϖ⟩` from `𝔓.valuation_exists_uniformizer K`. Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hϖ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hv1ϖ0 : v1 ϖ ≠ 0` using `(Valuation.ne_zero_iff _).2 hϖ0`. Establish `hlt : v1 ϖ < 1`. Establish `hle1 : v1 ϖ ≤ 1` using `(hle ϖ).2 (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)`.

Use `lt_of_le_of_ne hle1 fun heq => ?_` and prove the remaining obligations. Establish `h3 : v1 ϖ⁻¹ ≤ 1` using `by rw [map_inv₀, heq, inv_one]`. Establish `h4` using `(hle ϖ⁻¹).1 h3`. Rewrite `h4` using `[map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]`. Rewrite `h4` using `[← WithZero.exp_zero, WithZero.exp_le_exp]`.

Evaluate the numerical expressions using `at h4`. Establish `ha : 0 < vV T.V (iK ϖ)`. Establish `h5 : WithZero.log (v1 ϖ) < WithZero.log 1` using `(WithZero.log_lt_log hv1ϖ0 one_ne_zero).2 hlt`. Rewrite `h5` using `[WithZero.log_one, hv1]`. Simplify using `only [vV]`.

Use linear arithmetic over natural numbers and integers. Use `⟨(vV T.V (iK ϖ)).toNat, by omega, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg ha.le]`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality.

Simplify using `[vV, vAdd]`. Establish `hz2 : 𝔓.valuation K z = WithZero.exp (-vAdd 𝔓 z)`. Simplify using `only [vAdd, neg_neg]`. Conclude with `(WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm`. Establish `hw : 𝔓.valuation K (z * ϖ ^ (-vAdd 𝔓 z)) = 1`.

Rewrite using `[map_mul, map_zpow₀, hϖ, hz2, ← WithZero.exp_zsmul, ← WithZero.exp_add]`. Simplify using the standard rewrite rules. Establish `hu` using `hunit _ hw`. Establish `hz' : z = (z * ϖ ^ (-vAdd 𝔓 z)) * ϖ ^ (vAdd 𝔓 z)`. Rewrite using `[mul_assoc, ← zpow_add₀ hϖ0]`.

Simplify using the standard rewrite rules. Establish `hv : v1 z = v1 ϖ ^ (vAdd 𝔓 z)` using `by conv_lhs => rw [hz']`. Rewrite using `[map_mul, hu, one_mul, map_zpow₀]`. Establish `e1 : vV T.V (iK z) = -WithZero.log (v1 z)` using `rfl`. Establish `e2 : vV T.V (iK ϖ) = -WithZero.log (v1 ϖ)` using `rfl`.

Rewrite using `[e1, e2, hv, WithZero.log_zpow, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vV_eq_mul_vAdd (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR)
    (iK : K →+* T.Fr)
    (h : ∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  let v1 : Valuation K ℤᵐ⁰ := (valV T.V).comap iK
  have hv1 : ∀ z, v1 z = valV T.V (iK z) := fun z => rfl
  have hle : ∀ z : K, v1 z ≤ 1 ↔ 𝔓.valuation K z ≤ 1 := fun z => by
    rw [← h z, mem_range_iff_valV_le_one, hv1]
  have hunit : ∀ w : K, 𝔓.valuation K w = 1 → v1 w = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have h0 : v1 w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    have h1 : v1 w ≤ 1 := (hle w).2 hw.le
    have h2 : v1 w⁻¹ ≤ 1 := (hle w⁻¹).2 (by rw [map_inv₀, hw, inv_one])
    rw [map_inv₀] at h2
    have h1' := (WithZero.log_le_log h0 one_ne_zero).2 h1
    have h2' := (WithZero.log_le_log (inv_ne_zero h0) one_ne_zero).2 h2
    rw [WithZero.log_inv, WithZero.log_one] at h2'
    rw [WithZero.log_one] at h1'
    rw [← WithZero.exp_log h0, show WithZero.log (v1 w) = 0 by omega]
    rfl
  obtain ⟨ϖ, hϖ⟩ := 𝔓.valuation_exists_uniformizer K
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hv1ϖ0 : v1 ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hlt : v1 ϖ < 1 := by
    have hle1 : v1 ϖ ≤ 1 := (hle ϖ).2 (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    refine lt_of_le_of_ne hle1 fun heq => ?_
    have h3 : v1 ϖ⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have h4 := (hle ϖ⁻¹).1 h3
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg] at h4
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h4
    norm_num at h4
  have ha : 0 < vV T.V (iK ϖ) := by
    have h5 : WithZero.log (v1 ϖ) < WithZero.log 1 := (WithZero.log_lt_log hv1ϖ0 one_ne_zero).2 hlt
    rw [WithZero.log_one, hv1] at h5
    simp only [vV]
    omega
  refine ⟨(vV T.V (iK ϖ)).toNat, by omega, fun z => ?_⟩
  rw [Int.toNat_of_nonneg ha.le]
  by_cases hz : z = 0
  · subst hz; simp [vV, vAdd]
  have hz2 : 𝔓.valuation K z = WithZero.exp (-vAdd 𝔓 z) := by
    simp only [vAdd, neg_neg]; exact (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm
  have hw : 𝔓.valuation K (z * ϖ ^ (-vAdd 𝔓 z)) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hz2, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu := hunit _ hw
  have hz' : z = (z * ϖ ^ (-vAdd 𝔓 z)) * ϖ ^ (vAdd 𝔓 z) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hv : v1 z = v1 ϖ ^ (vAdd 𝔓 z) := by
    conv_lhs => rw [hz']
    rw [map_mul, hu, one_mul, map_zpow₀]
  have e1 : vV T.V (iK z) = -WithZero.log (v1 z) := rfl
  have e2 : vV T.V (iK ϖ) = -WithZero.log (v1 ϖ) := rfl
  rw [e1, e2, hv, WithZero.log_zpow, smul_eq_mul]
  ring

end GlobalTheory.CdvrPlaceVal
