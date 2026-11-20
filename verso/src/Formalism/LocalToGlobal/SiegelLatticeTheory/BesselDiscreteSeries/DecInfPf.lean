import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

noncomputable section

namespace Formalism.L2.SG.BesselDiscreteSeries

open Formalism.FourierDecayAlt.ThreeDimData

/- English proof (translation)
Establish `hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n`. Establish `: ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n`. Unfold `ReciprocityTheory.ChartRestriction.DS.pOf`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions.

Establish `hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n`. Establish `: ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n`. Unfold `ReciprocityTheory.ChartRestriction.DS.qOf`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions.

Establish `hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n`. Establish `: ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ n`. Unfold `ReciprocityTheory.ChartRestriction.DS.S7.q0`. Conclude with `le_trans (min_le_right _ _) (by exact_mod_cast hq)`. Conclude with `this` after adjusting the coercions.

Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hp0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε` using `Nat.cast_nonneg _`. Establish `hqq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε` using `Nat.cast_nonneg _`. Establish `hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε` using `Nat.cast_nonneg _`. Establish `hsq : Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ 2 * n`.

Rewrite using `[Real.sqrt_le_left (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2` using `one_le_pow₀ hn1`. Establish `hn22 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Establish `hn2 : (n : ℝ) ≤ (n : ℝ) ^ 3` using `by nlinarith`. Unfold `ReciprocityTheory.ChartRestriction.DS.thrStar`. Apply `max_le` to reduce the goal to its premises. Establish `: (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.pOf ε * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ (n : ℝ) ^ 3`. Establish `h1 : (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ (n : ℝ) * n` using `mul_le_mul_of_nonneg_left hp (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : 16 * (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ 16 * (n : ℝ) ^ 3`. Establish `: (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ (n : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem thrStar_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.pOf
      calc (Finset.univ.filter fun a => ε a = true).card ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = n := Finset.card_fin n
    exact_mod_cast this
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.qOf
      calc (Finset.univ.filter fun a => ε a = false).card ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = n := Finset.card_fin n
    exact_mod_cast this
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0
      exact le_trans (min_le_right _ _) (by exact_mod_cast hq)
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := Nat.cast_nonneg _
  have hqq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := Nat.cast_nonneg _
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hsq : Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hn22 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * 1 := by ring
      _ ≤ (n : ℝ) ^ 2 * n := mul_le_mul_of_nonneg_left hn1 (by positivity)
      _ = (n : ℝ) ^ 3 := by ring
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  apply max_le
  · have : (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.pOf ε * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ (n : ℝ) ^ 3 := by
      have h1 : (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hp (by positivity)
      calc (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.pOf ε * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ (n : ℝ) * n * n :=
            mul_le_mul h1 hq hqq0 (by positivity)
        _ = (n : ℝ) ^ 3 := by ring
    nlinarith
  · have h1 : 16 * (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ 16 * (n : ℝ) ^ 3 := by
      have : (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith

/- English proof (translation)
Introduce `k r ε lam h H _ _ _ σ hlam hσ hgap hok v0 hv0`. Take `⟨hk, h120, hA, -⟩` from `hok`. Establish `hn : 1 ≤ 2 * r + k + 1` using `by omega`. Use `set a : ℝ := aOf r h with ha_def`. Establish `hn3' : (0 : ℝ) < (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3` using `by positivity`.

Establish `hh0 : 0 < h` using `by linarith`. Establish `hsqrt : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1))`. Rewrite using `[Real.le_sqrt (by norm_num) (by positivity)]`. Establish `: (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ha0 : 0 ≤ a`. Simplify using `only [ha_def, aOf]`. Check the signs of the components of the expression. Establish `ha8 : a ≤ h / 8`. Simplify using `only [ha_def, aOf]`.

Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Use `set m : ℕ := ⌈a - 1⌉₊ with hm_def`. Establish `hm_ge : a - 1 ≤ (m : ℝ)` using `Nat.le_ceil _`. Establish `hm_le : (m : ℝ) ≤ a`.

Distinguish the cases in `h1 : 0 ≤ a - 1`. Use `Nat.ceil_lt_add_one h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: m = 0`. Simplify using `only [hm_def]`.

Conclude with `Nat.ceil_eq_zero.mpr (by linarith)`. Rewrite using `[this]`. Simplify using `using ha0`. Establish `hthr : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h`. Establish `h1` using `thrStar_le hn ε`.

Establish `h120' : 120 * (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3 ≤ h` using `h120`. Establish `hn3 : (0 : ℝ) < (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨C, Ws, hWs, hC⟩` from `ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hthr hσ`. Establish `hv0s : v0 ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := (Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth) k r ε lam H σ (by exact hlam) hσ v0 hv0`.

Use `set ν0 : ℝ := (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v0‖).sum with hν0`. Use `⟨C * ν0, Ws, fun W hW X hX => (hWs W hW).2 X hX, ?_⟩` and prove the remaining obligations. Introduce `w hw x hx`. Establish `hNI` using `(Formalism.FourierDecayAlt.P.norm_inverse_bound k r).2 x hx`. Establish `hg1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x` using `hNI.2`.

Establish `hgpos : 0 < Formalism.FourierDecayAlt.B.gN x` using `by linarith`. Establish `key` using `hC w hw v0 hv0s x hx`. Establish `hsumeq : (Ws.map fun W => ‖PI.UpqRep.dsigW (k` using `k) (r := r) σ W w‖).sum = (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W w‖).sum := by`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `W _`. Rewrite using `[Formalism.MainNotions.BridgeCS3d.dsigW_eq]`. Rewrite using `[hsumeq]`. Use `set νw : ℝ := (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W w‖).sum with hνw`. Use `set I : ℝ := ‖inner ℂ v0 (σ x w)‖ with hI`.

Establish `hI0 : 0 ≤ I` using `norm_nonneg _`. Establish `hgm : 1 ≤ Formalism.FourierDecayAlt.B.gN x ^ m` using `one_le_pow₀ hg1`. Establish `hB : 0 ≤ C * νw * ν0` using `le_trans (mul_nonneg (by linarith) hI0) key`. Establish `hI1 : I ≤ C * νw * ν0 * (Formalism.FourierDecayAlt.B.gN x ^ m)⁻¹`. Rewrite using `[le_mul_inv_iff₀ (by positivity)]`.

Combine the linear relations using `[mul_comm I (Formalism.FourierDecayAlt.B.gN x ^ m)]`. Establish `hpow : (Formalism.FourierDecayAlt.B.gN x ^ m)⁻¹ ≤ Formalism.FourierDecayAlt.B.gN x ^ (1 - a)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_neg hgpos.le]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decInf : Formalism.FourierDecayAlt.ThreeDimData.DecInf := by
  intro k r ε lam h H _ _ _ σ hlam hσ hgap hok v0 hv0
  obtain ⟨hk, h120, hA, -⟩ := hok
  have hn : 1 ≤ 2 * r + k + 1 := by omega

  set a : ℝ := aOf r h with ha_def
  have hn3' : (0 : ℝ) < (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3 := by positivity
  have hh0 : 0 < h := by linarith
  have hsqrt : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have ha0 : 0 ≤ a := by
    simp only [ha_def, aOf]; positivity
  have ha8 : a ≤ h / 8 := by
    simp only [ha_def, aOf]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set m : ℕ := ⌈a - 1⌉₊ with hm_def
  have hm_ge : a - 1 ≤ (m : ℝ) := Nat.le_ceil _
  have hm_le : (m : ℝ) ≤ a := by
    by_cases h1 : 0 ≤ a - 1
    · have := Nat.ceil_lt_add_one h1
      linarith
    · have : m = 0 := by
        simp only [hm_def]
        exact Nat.ceil_eq_zero.mpr (by linarith)
      rw [this]; simpa using ha0
  have hthr : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h := by
    have h1 := thrStar_le hn ε
    have h120' : 120 * (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3 ≤ h := h120
    have hn3 : (0 : ℝ) < (((2 * r + k + 1 : ℕ) : ℝ)) ^ 3 := by positivity
    nlinarith
  obtain ⟨C, Ws, hWs, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hthr hσ

  have hv0s : v0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    (Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth) k r ε lam H σ (by exact hlam) hσ v0 hv0
  set ν0 : ℝ := (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v0‖).sum with hν0
  refine ⟨C * ν0, Ws, fun W hW X hX => (hWs W hW).2 X hX, ?_⟩
  intro w hw x hx
  have hNI := (Formalism.FourierDecayAlt.P.norm_inverse_bound k r).2 x hx
  have hg1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := hNI.2
  have hgpos : 0 < Formalism.FourierDecayAlt.B.gN x := by linarith
  have key := hC w hw v0 hv0s x hx
  have hsumeq : (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum =
      (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W w‖).sum := by
    congr 1
    apply List.map_congr_left
    intro W _
    rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq]
  rw [hsumeq]
  set νw : ℝ := (Ws.map fun W => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W w‖).sum with hνw
  set I : ℝ := ‖inner ℂ v0 (σ x w)‖ with hI
  have hI0 : 0 ≤ I := norm_nonneg _
  have hgm : 1 ≤ Formalism.FourierDecayAlt.B.gN x ^ m := one_le_pow₀ hg1

  have hB : 0 ≤ C * νw * ν0 := le_trans (mul_nonneg (by linarith) hI0) key
  have hI1 : I ≤ C * νw * ν0 * (Formalism.FourierDecayAlt.B.gN x ^ m)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith [mul_comm I (Formalism.FourierDecayAlt.B.gN x ^ m)]
  have hpow : (Formalism.FourierDecayAlt.B.gN x ^ m)⁻¹ ≤ Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hgpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
  calc ‖inner ℂ v0 (σ x w)‖ = I := rfl
    _ ≤ C * νw * ν0 * (Formalism.FourierDecayAlt.B.gN x ^ m)⁻¹ := hI1
    _ ≤ C * νw * ν0 * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := mul_le_mul_of_nonneg_left hpow hB
    _ = C * ν0 * νw * Formalism.FourierDecayAlt.B.gN x ^ (1 - aOf r h) := by rw [ha_def]; ring

end Formalism.L2.SG.BesselDiscreteSeries
