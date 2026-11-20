import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TwoSidedBoostBounds

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `hσ' : 0 < σ⁻¹` using `inv_pos.2 hσ`. Establish `ha : 0 < σ ^ 2` using `by positivity`. Establish `hl` using `BoostLowerBounds.boost_lower (X := X) (τ := τ) (z := z) hz hee he0 hσ' (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)`. Simplify using `only [inv_inv] at hl`. Take `⟨hm, hff, hef, hfe⟩` from `BoostLowerBounds.plane_facts (X := X) (τ := τ) (z := z) hz hee he0`.

Rewrite `hl` using `[RankOneBoostIsometries.boost_comp X τ hm hee hff hef hfe hσ]`. Simplify using `only [inv_pow, inv_inv] at hl`. Establish `hmm : max (σ ^ 2) (σ ^ 2)⁻¹ * min (σ ^ 2)⁻¹ (σ ^ 2) = 1`. Break down `le_total (σ ^ 2) (σ ^ 2)⁻¹ with h | h` into its components or cases. Rewrite using `[max_eq_right h, min_eq_right h, inv_mul_cancel₀ ha.ne']`.

Rewrite using `[max_eq_left h, min_eq_left h, mul_inv_cancel₀ ha.ne']`. Establish `hM : 0 ≤ max (σ ^ 2) (σ ^ 2)⁻¹` using `le_max_of_le_left ha.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, hmm, one_mul]`. Use `_ ≤ max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := mul_le_mul_of_nonneg_left hl hM`.
-/
theorem boost_upper (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
    (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) ≤
      max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := by
  have hσ' : 0 < σ⁻¹ := inv_pos.2 hσ
  have ha : 0 < σ ^ 2 := by positivity
  have hl := BoostLowerBounds.boost_lower (X := X) (τ := τ) (z := z) hz hee he0 hσ'
    (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
  simp only [inv_inv] at hl
  obtain ⟨hm, hff, hef, hfe⟩ := BoostLowerBounds.plane_facts (X := X) (τ := τ) (z := z) hz hee he0
  rw [RankOneBoostIsometries.boost_comp X τ hm hee hff hef hfe hσ] at hl
  simp only [inv_pow, inv_inv] at hl
  have hmm : max (σ ^ 2) (σ ^ 2)⁻¹ * min (σ ^ 2)⁻¹ (σ ^ 2) = 1 := by
    rcases le_total (σ ^ 2) (σ ^ 2)⁻¹ with h | h
    · rw [max_eq_right h, min_eq_right h, inv_mul_cancel₀ ha.ne']
    · rw [max_eq_left h, min_eq_left h, mul_inv_cancel₀ ha.ne']
  have hM : 0 ≤ max (σ ^ 2) (σ ^ 2)⁻¹ := le_max_of_le_left ha.le
  calc X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
      = max (σ ^ 2) (σ ^ 2)⁻¹ * (min (σ ^ 2)⁻¹ (σ ^ 2) *
          X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)) := by
        rw [← mul_assoc, hmm, one_mul]
    _ ≤ max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := mul_le_mul_of_nonneg_left hl hM

/- English proof (translation)
Unfold `Data.c`. Establish `h : τ.1 X.ξ0 ≠ 0` using `(map_ne_zero _).2 X.ξ0_ne`. Use `norm_pos_iff.2 h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
  have := norm_pos_iff.2 h
  linarith

/- English proof (translation)
Take `⟨_, hξξ, hξ0⟩` from `hξ`. Establish `hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0` using `fun τ => by`. Rewrite using `[hermC_emb, hξξ, map_zero]`. Establish `he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0` using `fun τ h => hξ0 (funext fun a => by`. Use `congrFun h a` as an intermediate fact.

Simplify `this)` using `[Data.emb]`. Establish `hIsoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ)` using `fun τ => ⟨hiso τ, he0 τ⟩`. Establish `hm0 : 0 ≤ X.maj x τ (Data.emb τ.1 ξ)` using `MajorantConjugateTransfer.maj_nonneg X hx τ _`. Establish `hc0 : 0 ≤ X.c τ` using `(c_pos X τ).le`. Establish `hyd : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom` using `((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx (fun τ => ((s τ).re : ℂ))).1).2 (fun τ => by simp)`.

Establish `hsplit` using `flow_split (X := X) (ξ := ξ) hiso s x`. Establish `hyd2 : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom` using `hsplit ▸ hy`. Establish `hmy : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) = X.maj x τ (Data.emb τ.1 ξ)`. Rewrite using `[majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) (Data.emb τ.1 ξ), Data.flow_fix (X := X) (τ := τ) (ξ := ξ) _ _ (hiso τ)]`. Establish `hq : 0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ)`.

Establish `h` using `((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx s).1).1 hy τ`. Simplify using `only [Data.ttV, div_div_eq_mul_div, div_one] at h`. Establish `e1 : (s τ).im * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) = X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq' : 0 < 1 + X.c τ * (s τ).im * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)`.

Rewrite using `[hmy]`. Conclude with `hq`. Establish `hlow` using `ImaginaryMajorants.maj_imag_flow (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w`. Establish `heq` using `ImaginaryMajorants.maj_imag_eq (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w`. Establish `hsq : 0 < Real.sqrt (1 + X.c τ * (s τ).im * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ))` using `Real.sqrt_pos.2 hq'`.

Establish `hup` using `boost_upper X τ hyd (hiso τ) (he0 τ) hsq w`. Rewrite `hup` using `[Real.sq_sqrt hq'.le]`. Simplify using `only [hmy] at hlow heq hup`. Establish `hyw` using `majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) w`. Establish `hup1` using `FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx (-(s τ).re) w`.

Simplify using `only [Complex.ofReal_neg, abs_neg] at hup1`. Establish `hlo1` using `FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx ((s τ).re) (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) w)`. Rewrite `hlo1` using `[FlowMatrixMajorants.flowMat_inv (X := X) (τ := τ) (ξ := ξ) (hiso τ)]`. Rewrite `hup1`, `hlo1` using `[← hyw]`. Establish `hP : 0 < (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2` using `by positivity`.

Establish `hmin0 : 0 ≤ min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ)) (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹` using `le_min hq.le (inv_nonneg.2 hq.le)`. Establish `hmax0 : 0 ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ)) (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹` using `le_max_of_le_left hq.le`. Establish `hdiv : X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤ X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w`. Rewrite using `[div_le_iff₀ hP, mul_comm]`. Conclude with `hlo1`.

Rewrite using `[hsplit]`. Use `⟨hq, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[heq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem maj_two_sided {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hy : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) ∧
    min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w ≤
      X.maj (X.flow ξ s x) τ w ∧
    X.maj (X.flow ξ s x) τ w ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w := by
  obtain ⟨_, hξξ, hξ0⟩ := hξ
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
    rw [hermC_emb, hξξ, map_zero]
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := fun τ h => hξ0 (funext fun a => by
    have := congrFun h a
    simpa [Data.emb] using this)
  have hIsoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ => ⟨hiso τ, he0 τ⟩
  have hm0 : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := MajorantConjugateTransfer.maj_nonneg X hx τ _
  have hc0 : 0 ≤ X.c τ := (c_pos X τ).le
  have hyd : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom :=
    ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx (fun τ => ((s τ).re : ℂ))).1).2
      (fun τ => by simp)
  have hsplit := flow_split (X := X) (ξ := ξ) hiso s x
  have hyd2 : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom :=
    hsplit ▸ hy
  have hmy : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) =
      X.maj x τ (Data.emb τ.1 ξ) := by
    rw [majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) (Data.emb τ.1 ξ),
      Data.flow_fix (X := X) (τ := τ) (ξ := ξ) _ _ (hiso τ)]
  have hq : 0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by
    have h := ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx s).1).1 hy τ
    simp only [Data.ttV, div_div_eq_mul_div, div_one] at h
    have e1 : (s τ).im * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by ring
    linarith
  have hq' : 0 < 1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) := by
    rw [hmy]; exact hq
  have hlow := ImaginaryMajorants.maj_imag_flow (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have heq := ImaginaryMajorants.maj_imag_eq (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have hsq : 0 < Real.sqrt (1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq'
  have hup := boost_upper X τ hyd (hiso τ) (he0 τ) hsq w
  rw [Real.sq_sqrt hq'.le] at hup
  simp only [hmy] at hlow heq hup
  have hyw := majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) w
  have hup1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx (-(s τ).re) w
  simp only [Complex.ofReal_neg, abs_neg] at hup1
  have hlo1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx ((s τ).re)
    (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) w)
  rw [FlowMatrixMajorants.flowMat_inv (X := X) (τ := τ) (ξ := ξ) (hiso τ)] at hlo1
  rw [← hyw] at hup1 hlo1
  have hP : 0 < (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 := by positivity
  have hmin0 : 0 ≤ min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_min hq.le (inv_nonneg.2 hq.le)
  have hmax0 : 0 ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_max_of_le_left hq.le
  have hdiv : X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w := by
    rw [div_le_iff₀ hP, mul_comm]
    exact hlo1
  rw [hsplit]
  refine ⟨hq, ?_, ?_⟩
  · calc _ = min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
          (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
          (X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hmin0
      _ ≤ _ := hlow
  · rw [heq]
    calc _ ≤ _ := hup
      _ ≤ _ := mul_le_mul_of_nonneg_left hup1 hmax0
      _ = _ := by ring

end TwoSidedBoostBounds

end ReciprocityTheory.ChartRestriction.G.FD
