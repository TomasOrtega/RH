import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQExpEq
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

/- English proof (translation)
Establish `h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p)` using `isMF_AA.mul (isMF_DD.pow p)`. Establish `h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ)` using `((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)`. Establish `h3` using `(h1.sub h2).pow 2`. Conclude with `h3.congr_weight (by push_cast; ring)`.
-/
theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

/- English proof (translation)
The claim follows from `(gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)`.
-/
theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

/- English proof (translation)
The claim follows from `(Gm_isMF' hp).add (kronSq_isMF p)`.
-/
theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

/- English proof (translation)
The claim follows from `convergesOnDisk_eisensteinFourCubeSeries`.
-/
theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
/- English proof (translation)
The claim follows from `convergesOnDisk_discriminantSeries`.
-/
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
/- English proof (translation)
Conclude with `evalSeries_eisensteinFourCubeSeries τ`.
-/
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
/- English proof (translation)
Conclude with `evalSeries_discriminantSeries τ`.
-/
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

/- English proof (translation)
Establish `hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1` using `fun τ => by`. Rewrite using `[qm_one_eq]`. Simplify using `using UpperHalfPlane.norm_qParam_lt_one 1 τ`. Establish `hG` using `Gm_isMF' hp`. Establish `c1 : Conv (aC * dC ^ p)` using `aC_conv.mul (dC_conv.pow p)`.

Establish `c2 : Conv (aC ^ p * dC)` using `(aC_conv.pow p).mul dC_conv`. Establish `c3 : Conv (aC * dC ^ p - aC ^ p * dC)` using `c1.sub c2`. Apply `(kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ), ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ), ev_pow aC_conv p (hq τ), aC_ev, dC_ev]`.

Both sides reduce to the same expression.
-/
theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

/- English proof (translation)
Take `⟨w, hw, hk⟩` from `kronSer hp`. Establish `hp0 : 0 < p` using `hp.pos`. Use `⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩` and prove the remaining obligations. Rewrite using `[kronFun_qExp hp]`. Use extensionality with `n`.

Establish `key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) = PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)`. Simplify using `[xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]`. Establish `hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) = prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2)`. Rewrite using `[← gmQ_xp hp0]`. Use extensionality with `m`.

Simplify using `only [xp, PowerSeries.coeff_mk, map_add]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← key, hsum, hk]`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]`.
-/
theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

/- English proof (translation)
Take `⟨w, hw, hqe⟩` from `kronFun_div hp`. Establish `hc0 : (1 - zetaC p) ≠ 0` using `one_sub_zeta_ne_zero hp`. Establish `hK` using `kronFun_isMF hp`. Set `f : ℍ → ℂ` to `fun τ => (1 - zetaC p)⁻¹ * kronFun p τ`. Establish `hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f` using `hK.const_mul (1 - zetaC p)⁻¹`.

Establish `hwq : qExpansion 1 f = w`. Apply `hf.qExp_eq` to reduce the goal to its premises. Establish `e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p)`. Rewrite using `[hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]`. Rewrite using `[e]`.

Conclude with `hK.conv.C_mul _`. Introduce `τ`. Establish `hs` using `(hK.hasSum τ).mul_left (1 - zetaC p)⁻¹`. Establish `hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n = (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n)`. Introduce `n`.

Rewrite using `[hqe, PowerSeries.coeff_C_mul]`. Clear the denominators using the available nonvanishing facts. Unfold `ev`. Repeatedly rewrite using `[hw']`. Conclude with `hs.tsum_eq`.

Take `⟨P, hPc, -, hPe⟩` from `qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)`. Use `⟨P, hPc, fun τ => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`. Use `_ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]`.
-/
theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

/- English proof (translation)
Take `⟨Q, hQ, hK⟩` from `kronFun_poly hp`. Establish `hD` using `DD_ne_zero τ`. Establish `hsq : ¬ IsSquare p` using `Irreducible.not_isSquare hp`. Establish `hj` using `jT_isIntegral hp.pos hsq h`. Establish `hint : IsIntegral ℤ (Q.eval (jT τ))`.

Rewrite using `[Polynomial.eval_eq_sum_range]`. Conclude with `IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)`. Use `⟨Q.eval (jT τ), hint, ?_⟩` and prove the remaining obligations. Establish `e1` using `hK τ`. Unfold `kronFun at e1`.

Rewrite `e1` using `[h, zero_add]`. Establish `hA : AA τ = jT τ * DD τ` using `by rw [jT, div_mul_cancel₀ _ hD]`. Rewrite `e1` using `[hA]`. Establish `e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) = (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1))`. Take the linear combination `e1`.

Conclude with `mul_right_cancel₀ (pow_ne_zero _ hD) e2`.
-/
theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
