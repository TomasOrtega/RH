import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

/- English proof (translation)
Introduce `L _ _ _`. Take `⟨x₀, h0, h1⟩` from `NormedField.exists_norm_lt_one L`. Establish `hc : IsCompact (Metric.ball (0 : L) 1)` using `Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball`. Establish `hx : x₀ ∈ Metric.ball (0 : L) 1` using `by simpa using h1`. Take `⟨p, hp, hmax⟩` from `hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn`.

Establish `hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖` using `fun w hw => isMaxOn_iff.mp hmax w (by simpa using hw)`. Establish `hp1 : ‖p‖ < 1` using `by simpa using hp`. Establish `hp0 : 0 < ‖p‖` using `h0.trans_le (hmax' x₀ h1)`. Establish `hpne : p ≠ 0` using `norm_pos_iff.mp hp0`. Use `⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mk0]`. Establish `hxpos : 0 < ‖x‖` using `norm_pos_iff.mpr hx0`. Establish `hy : 1 < ‖p‖⁻¹` using `(one_lt_inv₀ hp0).mpr hp1`. Take `⟨n, hn1, hn2⟩` from `exists_mem_Ico_zpow hxpos hy`. Establish `hyn : 0 < ‖p‖⁻¹ ^ n` using `zpow_pos (inv_pos.mpr hp0) n`.

Use `set w : L := p ^ (-n) * x⁻¹ with hw`. Establish `hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖`. Rewrite using `[hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]`. Establish `hle : ‖w‖ ≤ 1`. Rewrite using `[hwn]`.

Conclude with `(div_le_one hxpos).mpr hn1`. Establish `hgt : ‖p‖ < ‖w‖`. Rewrite using `[hwn, lt_div_iff₀ hxpos]`. Establish `: ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹` using `by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : ‖w‖ = 1`. Assume the negation of the conclusion as `hne`. Conclude with `absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)`. Use `⟨-n, ?_⟩` and prove the remaining obligations. Rewrite `heq` using `[hwn, div_eq_one_iff_eq hxpos.ne']`.

Rewrite using `[← heq, _root_.inv_zpow']`.
-/
theorem exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  have hyn : 0 < ‖p‖⁻¹ ^ n := zpow_pos (inv_pos.mpr hp0) n
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']

end GlobalTheory.CompanionTheory.CartGL
