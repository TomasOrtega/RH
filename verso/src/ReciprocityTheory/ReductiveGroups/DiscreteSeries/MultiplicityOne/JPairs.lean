import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairsA

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

/- English proof (translation)
Establish `h'` using `h`. Unfold `UnitaryGroupStructuralFacts ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at h'`. Take `⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -⟩, -⟩` from `h'`. Introduce `k r Wp _ _ _ D X _ _ d hd a₁ a₂ u hu v hv`. Use `set a := min a₁ a₂ with ha_def`.

Use `set b := AG k r + 1 with hb_def`. Establish `hone : (1 : Mat k r) ∈ GV k r` using `by show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules. Establish `hlow : ∀ x ∈ GV k r, 1 ≤ gN x` using `fun x hx => hLow k r x hx`. Establish `hb0 : 0 ≤ b`.

Establish `: 0 ≤ AG k r` using `by unfold AG; positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hab : b ≤ a`. Use `swap`. Use `⟨‖u‖ * ‖v‖, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h1 : ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 1 ≤ gN x ^ (-(min a₁ a₂ - AG k r - 1))`. Apply `Real.one_le_rpow (hlow x hx)` to reduce the goal to its premises. Rewrite using `[← ha_def]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Take `⟨C₁, hC₁⟩` from `hu`. Take `⟨C₂, hC₂⟩` from `hv`. Establish `hpos : ∀ x ∈ GV k r, 0 < gN x` using `fun x hx => lt_of_lt_of_le one_pos (hlow x hx)`.

Establish `hC₁0 : 0 ≤ C₁`. Establish `h1` using `hC₁ 1 hone`. Establish `h2` using `Real.rpow_pos_of_pos (hpos 1 hone) (-a₁)`. Assume the negation of the conclusion as `hneg'`. Establish `hneg` using `lt_of_not_ge hneg'`.

Establish `: C₁ * gN (1 : Mat k r) ^ (-a₁) < 0` using `mul_neg_of_neg_of_pos hneg h2`. Combine the linear relations using `[norm_nonneg (mc X u X.w 1)]`. Establish `hC₂0 : 0 ≤ C₂`. Establish `h1` using `hC₂ 1 hone`. Establish `h2` using `Real.rpow_pos_of_pos (hpos 1 hone) (-a₂)`.

Assume the negation of the conclusion as `hneg'`. Establish `hneg` using `lt_of_not_ge hneg'`. Establish `: C₂ * gN (1 : Mat k r) ^ (-a₂) < 0` using `mul_neg_of_neg_of_pos hneg h2`. Combine the linear relations using `[norm_nonneg (mc X v X.w 1)]`. Use `set c := gN (Hpk k r) ^ 2 with hc_def`.

Establish `hc : 0 < c`. Establish `h1 : gN (1 : Mat k r) ≤ gN (Hpk k r) * gN (Hpk k r)`. Use `gN_mul_le (Hpk k r) (Hpk k r)` as an intermediate fact. Rewrite `this` using `[Hpk_sq]`. Then use the resulting hypothesis. Establish `h2` using `hlow 1 hone`.

Rewrite using `[hc_def]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmeas : Measurable (fun g : Mt k r => gN (Matrix.of g))`. Unfold `gN`. Use `fun_prop`.

Establish `hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r`. Rewrite using `[ae_iff]`. Conclude with `D.haarG.conc`. Establish `hAB : AB k r ≤ b` using `AB_le_AG k r`. Establish `hfin` using `hInt k r D.μG b D.haarG hAB`.

Establish `hI : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-b)) D.μG`. Use `⟨(hmeas.pow_const _).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal]`. Conclude with `hfin`. Conclude with `Filter.Eventually.of_forall fun g => Real.rpow_nonneg (by unfold gN; positivity) _`.

Use `set I := ∫ g : Mt k r, gN (Matrix.of g) ^ (-b) ∂D.μG with hI_def`. Use `⟨d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hd0 : 0 < d` using `hd.1`. Take `⟨-, hEq⟩` from `hd.2 (X.σ x u) X.w v X.w`. Establish `hww : ⟪X.w, X.w⟫_ℂ = 1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, X.w_norm]`. Simplify using the standard rewrite rules. Rewrite `hEq` using `[hww, mul_one]`. Use `set F : Mt k r → ℂ := fun g => mc X (X.σ x u) X.w (Matrix.of g) * star (mc X v X.w (Matrix.of g)) with hF_def`. Establish `hmc : mc X u v x = (d : ℂ) * ∫ g, F g ∂D.μG`.

Rewrite using `[hEq]`. Establish `: (d : ℂ) ≠ 0` using `by exact_mod_cast hd0.ne'`. Express the relevant statement in the definitionally equal form `⟪v, X.σ x u⟫_ℂ = (d : ℂ) * (⟪v, X.σ x u⟫_ℂ / (d : ℂ))`. Clear the denominators using the available nonvanishing facts. Use `set G : Mt k r → ℝ := fun g => C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) with hG_def`.

Establish `hGi : Integrable G D.μG` using `hI.const_mul _`. Establish `hpt : ∀ᵐ g ∂D.μG, ‖F g‖ ≤ G g` using `by filter_upwards [hae] with g hg`. Establish `hgx : Matrix.of g * x ∈ GV k r` using `GV_mul k r hg hx`. Establish `hFg : ‖F g‖ = ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖`. Rewrite using `[hF_def]`.

Simplify using `only [norm_mul, norm_star]`. Use `congr 1`. Use `show ‖⟪X.w, X.σ (Matrix.of g) (X.σ x u)⟫_ℂ‖ = ‖⟪X.w, X.σ (Matrix.of g * x) u⟫_ℂ‖`. Rewrite using `[X.rep.1.2 _ hg _ hx]`. Both sides reduce to the same expression.

Establish `hA1` using `hlow _ hgx`. Establish `hB1` using `hlow _ hg`. Establish `e1 : ‖mc X u X.w (Matrix.of g * x)‖ ≤ C₁ * gN (Matrix.of g * x) ^ (-a)`. Use `(hC₁ _ hgx).trans ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `min_le_left a₁ a₂`. Establish `e2 : ‖mc X v X.w (Matrix.of g)‖ ≤ C₂ * gN (Matrix.of g) ^ (-a)`. Use `(hC₂ _ hg).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `min_le_right a₁ a₂`.

Establish `key` using `real_key hA1 hB1 (hpos x hx) hc hb0 hab (gN_le_mul hg x)`. Rewrite using `[hFg, hG_def]`. Combine the equalities or inequalities in the displayed calculation. Establish `hbound : ‖∫ g, F g ∂D.μG‖ ≤ ∫ g, G g ∂D.μG` using `(norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGi hpt)`. Establish `hGint : ∫ g, G g ∂D.μG = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I`.

Rewrite using `[hG_def, integral_const_mul]`. Establish `hsplit : (gN x * c⁻¹) ^ (-(a - b)) = gN x ^ (-(a - b)) * (c⁻¹) ^ (-(a - b))` using `Real.mul_rpow (hpos x hx).le (inv_nonneg.mpr hc.le)`. Establish `hexp : -(min a₁ a₂ - AG k r - 1) = -(a - b)`. Rewrite using `[ha_def, hb_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hmc, norm_mul, hexp]`. Establish `hdn : ‖(d : ℂ)‖ = d`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]`. Rewrite using `[hdn]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hGint]`. Conclude with `mul_le_mul_of_nonneg_left hbound hd0.le`. Use `_ = d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))) * gN x ^ (-(a - b)) := by`. Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stPairs (h : UnitaryGroupStructuralFacts) : StPairs := by
  have h' := h
  unfold UnitaryGroupStructuralFacts ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at h'
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -⟩, -⟩ := h'
  intro k r Wp _ _ _ D X _ _ d hd a₁ a₂ u hu v hv
  set a := min a₁ a₂ with ha_def
  set b := AG k r + 1 with hb_def
  have hone : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hlow : ∀ x ∈ GV k r, 1 ≤ gN x := fun x hx => hLow k r x hx
  have hb0 : 0 ≤ b := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  by_cases hab : b ≤ a
  swap
  · refine ⟨‖u‖ * ‖v‖, fun x hx => ?_⟩
    have h1 : ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := by
      calc ‖mc X u v x‖ = ‖⟪v, X.σ x u⟫_ℂ‖ := rfl
        _ ≤ ‖v‖ * ‖X.σ x u‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [X.rep.2.1 x hx u]; ring
    have h2 : 1 ≤ gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by
      apply Real.one_le_rpow (hlow x hx)
      rw [← ha_def]
      linarith
    calc ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := h1
      _ = ‖u‖ * ‖v‖ * 1 := by ring
      _ ≤ ‖u‖ * ‖v‖ * gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by gcongr
  obtain ⟨C₁, hC₁⟩ := hu
  obtain ⟨C₂, hC₂⟩ := hv
  have hpos : ∀ x ∈ GV k r, 0 < gN x := fun x hx => lt_of_lt_of_le one_pos (hlow x hx)
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := hC₁ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₁)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₁ * gN (1 : Mat k r) ^ (-a₁) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X u X.w 1)]
  have hC₂0 : 0 ≤ C₂ := by
    have h1 := hC₂ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₂)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₂ * gN (1 : Mat k r) ^ (-a₂) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X v X.w 1)]
  set c := gN (Hpk k r) ^ 2 with hc_def
  have hc : 0 < c := by
    have h1 : gN (1 : Mat k r) ≤ gN (Hpk k r) * gN (Hpk k r) := by
      have := gN_mul_le (Hpk k r) (Hpk k r)
      rwa [Hpk_sq] at this
    have h2 := hlow 1 hone
    rw [hc_def]
    nlinarith
  have hmeas : Measurable (fun g : Mt k r => gN (Matrix.of g)) := by
    unfold gN
    fun_prop
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r := by
    rw [ae_iff]
    exact D.haarG.conc
  have hAB : AB k r ≤ b := AB_le_AG k r
  have hfin := hInt k r D.μG b D.haarG hAB
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-b)) D.μG := by
    refine ⟨(hmeas.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hfin
    · exact Filter.Eventually.of_forall fun g => Real.rpow_nonneg (by unfold gN; positivity) _
  set I := ∫ g : Mt k r, gN (Matrix.of g) ^ (-b) ∂D.μG with hI_def
  refine ⟨d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))), fun x hx => ?_⟩
  have hd0 : 0 < d := hd.1
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x u) X.w v X.w
  have hww : ⟪X.w, X.w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hww, mul_one] at hEq
  set F : Mt k r → ℂ := fun g => mc X (X.σ x u) X.w (Matrix.of g) * star (mc X v X.w (Matrix.of g)) with hF_def
  have hmc : mc X u v x = (d : ℂ) * ∫ g, F g ∂D.μG := by
    rw [hEq]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    change ⟪v, X.σ x u⟫_ℂ = (d : ℂ) * (⟪v, X.σ x u⟫_ℂ / (d : ℂ))
    field_simp
  set G : Mt k r → ℝ := fun g => C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) with hG_def
  have hGi : Integrable G D.μG := hI.const_mul _
  have hpt : ∀ᵐ g ∂D.μG, ‖F g‖ ≤ G g := by
    filter_upwards [hae] with g hg
    have hgx : Matrix.of g * x ∈ GV k r := GV_mul k r hg hx
    have hFg : ‖F g‖ = ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖ := by
      rw [hF_def]
      simp only [norm_mul, norm_star]
      congr 1
      show ‖⟪X.w, X.σ (Matrix.of g) (X.σ x u)⟫_ℂ‖ = ‖⟪X.w, X.σ (Matrix.of g * x) u⟫_ℂ‖
      rw [X.rep.1.2 _ hg _ hx]
      rfl
    have hA1 := hlow _ hgx
    have hB1 := hlow _ hg
    have e1 : ‖mc X u X.w (Matrix.of g * x)‖ ≤ C₁ * gN (Matrix.of g * x) ^ (-a) := by
      refine (hC₁ _ hgx).trans ?_
      gcongr
      exact min_le_left a₁ a₂
    have e2 : ‖mc X v X.w (Matrix.of g)‖ ≤ C₂ * gN (Matrix.of g) ^ (-a) := by
      refine (hC₂ _ hg).trans ?_
      gcongr
      exact min_le_right a₁ a₂
    have key := real_key hA1 hB1 (hpos x hx) hc hb0 hab (gN_le_mul hg x)
    rw [hFg, hG_def]
    calc ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖
        ≤ (C₁ * gN (Matrix.of g * x) ^ (-a)) * (C₂ * gN (Matrix.of g) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hC₁0 (Real.rpow_nonneg (hpos _ hgx).le _))
      _ = C₁ * C₂ * (gN (Matrix.of g * x) ^ (-a) * gN (Matrix.of g) ^ (-a)) := by ring
      _ ≤ C₁ * C₂ * ((gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b)) := by
          gcongr
      _ = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) := by ring
  have hbound : ‖∫ g, F g ∂D.μG‖ ≤ ∫ g, G g ∂D.μG :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGi hpt)
  have hGint : ∫ g, G g ∂D.μG = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I := by
    rw [hG_def, integral_const_mul]
  have hsplit : (gN x * c⁻¹) ^ (-(a - b)) = gN x ^ (-(a - b)) * (c⁻¹) ^ (-(a - b)) :=
    Real.mul_rpow (hpos x hx).le (inv_nonneg.mpr hc.le)
  have hexp : -(min a₁ a₂ - AG k r - 1) = -(a - b) := by
    rw [ha_def, hb_def]; ring
  rw [hmc, norm_mul, hexp]
  have hdn : ‖(d : ℂ)‖ = d := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  rw [hdn]
  calc d * ‖∫ g, F g ∂D.μG‖ ≤ d * (C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I) := by
        rw [← hGint]; exact mul_le_mul_of_nonneg_left hbound hd0.le
    _ = d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))) * gN x ^ (-(a - b)) := by
        rw [hsplit]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
