import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.SelfCube

/- English proof (translation)
Take `⟨b, hb⟩ : ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (Fin g → ℂ), Submodule.span ℤ (Set.range b) = Λ` from `⟨_, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ⟩`. Establish `hK : IsCompact (closure (ZSpan.fundamentalDomain b))` using `(ZSpan.fundamentalDomain_isBounded b).isCompact_closure`. Take `⟨M, hM⟩` from `(hK.image hc).bddAbove`. Use `⟨M, fun z => ?_⟩` and prove the remaining obligations. Establish `hfl : (ZSpan.floor b z : Fin g → ℂ) ∈ Λ`.

Conclude with `Eq.mp (congrArg (fun S : Submodule ℤ (Fin g → ℂ) => (ZSpan.floor b z : Fin g → ℂ) ∈ S) hb) (ZSpan.floor b z).2`. Establish `hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ)`. Rewrite using `[ZSpan.fract_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[hz, hp _ _ hfl]`.

Conclude with `hM ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), rfl⟩`.
-/
private theorem exists_bound_of_continuous_lattice_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h : (Fin g → ℂ) → ℝ) (hc : Continuous h)
    (hp : ∀ z, ∀ l ∈ Λ, h (z + l) = h z) : ∃ M, ∀ z, h z ≤ M := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (Fin g → ℂ),
      Submodule.span ℤ (Set.range b) = Λ :=
    ⟨_, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ⟩
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨M, hM⟩ := (hK.image hc).bddAbove
  refine ⟨M, fun z => ?_⟩
  have hfl : (ZSpan.floor b z : Fin g → ℂ) ∈ Λ := by
    exact Eq.mp (congrArg (fun S : Submodule ℤ (Fin g → ℂ) => (ZSpan.floor b z : Fin g → ℂ) ∈ S) hb)
      (ZSpan.floor b z).2
  have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
    rw [ZSpan.fract_apply]; abel
  rw [hz, hp _ _ hfl]
  exact hM ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), rfl⟩

/- English proof (translation)
Assume the negation of the conclusion as `hneg'`. Establish `hneg` using `not_le.1 hneg'`. Take `⟨M, hM⟩` from `exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖ * Real.exp (-q z)) (hψ.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) (fun z l hl => hper z l hl)`. Establish `hM0 : 0 ≤ M` using `le_trans (by positivity) (hM 0)`. Establish `hbd : ∀ t : ℂ, ‖ψ (t • w)‖ ≤ M * Real.exp (‖t‖ ^ 2 * q w)`.

Introduce `t`. Establish `h1` using `hM (t • w)`. Simplify using `only [hs] at h1`. Establish `h2 : ‖ψ (t • w)‖ = ‖ψ (t • w)‖ * Real.exp (-(‖t‖ ^ 2 * q w)) * Real.exp (‖t‖ ^ 2 * q w)`. Rewrite using `[_root_.mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, _root_.mul_one]`.

Rewrite using `[h2]`. Conclude with `mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le`. Establish `hdiff : Differentiable ℂ (fun t : ℂ => ψ (t • w))` using `hψ.comp (differentiable_id.smul_const w)`. Establish `hb : Bornology.IsBounded (Set.range fun t : ℂ => ψ (t • w))`. Rewrite using `[isBounded_iff_forall_norm_le]`.

Use `⟨M, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Use `(hbd t).trans ?_` and prove the remaining obligations. Establish `he : Real.exp (‖t‖ ^ 2 * q w) ≤ 1` using `Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)`. Conclude with `mul_le_of_le_one_right hM0 he`.

Establish `hc : ∀ t : ℂ, ψ (t • w) = ψ 0` using `fun t => by`. Use `hdiff.apply_eq_apply_of_bounded hb t 0` as an intermediate fact. Simplify using `using this`. Establish `hlim : Filter.Tendsto (fun r : ℝ => M * Real.exp (‖(r : ℂ)‖ ^ 2 * q w)) Filter.atTop (𝓝 (M * 0))`. Use `Filter.Tendsto.const_mul M (Real.tendsto_exp_atBot.comp ?_)` and prove the remaining obligations.

Establish `h1 : Filter.Tendsto (fun r : ℝ => r ^ 2 * (-q w)) Filter.atTop Filter.atTop` using `(tendsto_pow_atTop two_ne_zero).atTop_mul_const (neg_pos.2 hneg)`. Use `(Filter.tendsto_neg_atTop_atBot.comp h1).congr (fun r => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hle : ‖ψ 0‖ ≤ M * 0` using `ge_of_tendsto' hlim (fun r => by rw [← hc (r : ℂ)]; exact hbd _)`.

Rewrite `hle` using `[mul_zero]`. Conclude with `h0 (norm_le_zero_iff.1 hle)`.
-/
theorem quad_nonneg {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ψ 0 ≠ 0)
    (q : (Fin g → ℂ) → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w)
    (hper : ∀ z, ∀ l ∈ Λ, ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z)) (w) :
    0 ≤ q w := by
  by_contra hneg'
  have hneg := not_le.1 hneg'
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖ * Real.exp (-q z))
    (hψ.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) (fun z l hl => hper z l hl)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hbd : ∀ t : ℂ, ‖ψ (t • w)‖ ≤ M * Real.exp (‖t‖ ^ 2 * q w) := by
    intro t
    have h1 := hM (t • w)
    simp only [hs] at h1
    have h2 : ‖ψ (t • w)‖ =
        ‖ψ (t • w)‖ * Real.exp (-(‖t‖ ^ 2 * q w)) * Real.exp (‖t‖ ^ 2 * q w) := by
      rw [_root_.mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, _root_.mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hdiff : Differentiable ℂ (fun t : ℂ => ψ (t • w)) :=
    hψ.comp (differentiable_id.smul_const w)
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => ψ (t • w)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨t, rfl⟩
    refine (hbd t).trans ?_
    have he : Real.exp (‖t‖ ^ 2 * q w) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)
    exact mul_le_of_le_one_right hM0 he
  have hc : ∀ t : ℂ, ψ (t • w) = ψ 0 := fun t => by
    have := hdiff.apply_eq_apply_of_bounded hb t 0
    simpa using this
  have hlim : Filter.Tendsto (fun r : ℝ => M * Real.exp (‖(r : ℂ)‖ ^ 2 * q w)) Filter.atTop
      (𝓝 (M * 0)) := by
    refine Filter.Tendsto.const_mul M (Real.tendsto_exp_atBot.comp ?_)
    have h1 : Filter.Tendsto (fun r : ℝ => r ^ 2 * (-q w)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_mul_const (neg_pos.2 hneg)
    refine (Filter.tendsto_neg_atTop_atBot.comp h1).congr (fun r => ?_)
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hle : ‖ψ 0‖ ≤ M * 0 :=
    ge_of_tendsto' hlim (fun r => by rw [← hc (r : ℂ)]; exact hbd _)
  rw [mul_zero] at hle
  exact h0 (norm_le_zero_iff.1 hle)

/- English proof (translation)
Establish `hadd2 : ∀ z w w', D z (w + w') = D z w + D z w'` using `fun z w w' => by`. Rewrite using `[hst, hadd, map_add, ← hst, ← hst]`. Establish `hsm2 : ∀ (t : ℂ) z w, D z (t • w) = starRingEnd ℂ t * D z w` using `fun t z w => by`. Rewrite using `[hst, hsm, map_mul, ← hst]`. Establish `hdiag_im : ∀ z, (D z z).im = 0` using `fun z => by`.

Use `congrArg Complex.im (hst z z)` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set q : (Fin g → ℂ) → ℝ := fun z => π / 2 * (D z z).re with hqdef`. Establish `hqc : Continuous q` using `continuous_const.mul (Complex.continuous_re.comp hc)`.

Establish `hqs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w` using `fun t w => by`. Simplify using `only [hqdef, hsm, hsm2]`. Rewrite using `[← _root_.mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hexpand : ∀ z l, D (z + l) (z + l) = D z z + D z l + D l z + D l l` using `fun z l => by`.

Rewrite using `[hadd, hadd2, hadd2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hreal : ∀ z l, (D l z).re = (D z l).re` using `fun z l => by rw [hst, Complex.conj_re]`. Establish `hnorm : ∀ z (l : Λ), ‖ψ (z + l)‖ = Real.exp (π * (D z l).re + π / 2 * (D l l).re) * ‖ψ z‖` using `fun z l => by`. Rewrite using `[hper, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]`.

Use `congr 2`. Simplify using `[Complex.add_re, Complex.mul_re, hdiag_im]`. Establish `hper_q : ∀ z (l : Λ), ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z)` using `fun z l => by`. Rewrite using `[hnorm, mul_comm (Real.exp _) _, _root_.mul_assoc, ← Real.exp_add]`. Use `congr 2`.

Simplify using `only [hqdef, hexpand, Complex.add_re, hreal z l]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq1 : ∀ w, 0 ≤ q w` using `fun w => quad_nonneg Λ ψ hψ (h0 0) q hqc hqs (fun z l hl => hper_q z ⟨l, hl⟩) w`. Establish `hq2 : ∀ w, 0 ≤ -q w` using `fun w => quad_nonneg Λ (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0)) (fun z => -q z) hqc.neg (fun t w => by simp only [hqs]; ring) (fun z l hl => by`. Use `hper_q z ⟨l, hl⟩` as an intermediate fact.

Simplify using `only [norm_inv, neg_neg]`. Establish `e1 : Real.exp (q (z + l)) = (Real.exp (-q (z + l)))⁻¹` using `by rw [Real.exp_neg, inv_inv]`. Establish `e2 : Real.exp (q z) = (Real.exp (-q z))⁻¹` using `by rw [Real.exp_neg, inv_inv]`. Rewrite using `[e1, e2, ← mul_inv, ← mul_inv]`. Conclude with `congrArg _ this) w`.

Establish `hdiag : ∀ z, D z z = 0` using `fun z => by`. Establish `hre : (D z z).re = 0`. Establish `h3 : q z = 0` using `le_antisymm (by linarith [hq2 z]) (hq1 z)`. Simplify using `only [hqdef] at h3`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases.

Conclude with `absurd h (by positivity)`. Conclude with `h`. Conclude with `Complex.ext_iff.2 ⟨by simpa using hre, by simpa using hdiag_im z⟩`. Establish `hD0 : ∀ z w, D z w = 0` using `fun z w => by`. Establish `e1` using `hexpand z w`.

Rewrite `e1` using `[hdiag, hdiag, hdiag]`. Establish `e2` using `hexpand (I • z) w`. Rewrite `e2` using `[hdiag, hdiag, hdiag, hsm, hsm2, Complex.conj_I]`. Establish `hb : D w z = -D z w` using `by linear_combination (-1 : ℂ) * e1`. Rewrite `e2` using `[hb]`.

Establish `h2 : (2 * I) * D z w = 0` using `by linear_combination -e2`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero two_ne_zero I_ne_zero)`. Conclude with `h`. Establish `hper' : ∀ z (l : Λ), ψ (z + l) = ρ l * ψ z` using `fun z l => by`.

Rewrite using `[hper, hD0, hD0]`. Simplify using the standard rewrite rules. Take `⟨M, hM⟩` from `exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖) hψ.continuous.norm (fun z l hl => (congrArg norm (hper' z ⟨l, hl⟩)).trans (by rw [norm_mul, hρ, _root_.one_mul]))`. Establish `hb : Bornology.IsBounded (Set.range ψ)`. Rewrite using `[isBounded_iff_forall_norm_le]`.

Conclude with `⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩`. Establish `hconst : ∀ z, ψ z = ψ 0` using `fun z => hψ.apply_eq_apply_of_bounded hb z 0`. Use `⟨hD0, fun l => ?_⟩` and prove the remaining obligations. Establish `h4` using `hper' 0 l`. Rewrite `h4` using `[hconst (0 + (l : Fin g → ℂ))]`.

Conclude with `mul_right_cancel₀ (h0 0) (h4.symm.trans (_root_.one_mul _).symm)`.
-/
theorem form_eq_zero_of_unit {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = starRingEnd ℂ (D z w))
    (ρ : Λ → ℂ) (hρ : ∀ l, ‖ρ l‖ = 1)
    (hper : ∀ z (l : Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ l, ρ l = 1 := by
  have hadd2 : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    rw [hst, hadd, map_add, ← hst, ← hst]
  have hsm2 : ∀ (t : ℂ) z w, D z (t • w) = starRingEnd ℂ t * D z w := fun t z w => by
    rw [hst, hsm, map_mul, ← hst]
  have hdiag_im : ∀ z, (D z z).im = 0 := fun z => by
    have := congrArg Complex.im (hst z z)
    rw [Complex.conj_im] at this
    linarith
  set q : (Fin g → ℂ) → ℝ := fun z => π / 2 * (D z z).re with hqdef
  have hqc : Continuous q := continuous_const.mul (Complex.continuous_re.comp hc)
  have hqs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w := fun t w => by
    simp only [hqdef, hsm, hsm2]
    rw [← _root_.mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    ring
  have hexpand : ∀ z l, D (z + l) (z + l) = D z z + D z l + D l z + D l l := fun z l => by
    rw [hadd, hadd2, hadd2]; ring
  have hreal : ∀ z l, (D l z).re = (D z l).re := fun z l => by rw [hst, Complex.conj_re]
  have hnorm : ∀ z (l : Λ),
      ‖ψ (z + l)‖ = Real.exp (π * (D z l).re + π / 2 * (D l l).re) * ‖ψ z‖ := fun z l => by
    rw [hper, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]
    congr 2
    simp [Complex.add_re, Complex.mul_re, hdiag_im]
  have hper_q : ∀ z (l : Λ),
      ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z) := fun z l => by
    rw [hnorm, mul_comm (Real.exp _) _, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    simp only [hqdef, hexpand, Complex.add_re, hreal z l]
    ring
  have hq1 : ∀ w, 0 ≤ q w := fun w =>
    quad_nonneg Λ ψ hψ (h0 0) q hqc hqs (fun z l hl => hper_q z ⟨l, hl⟩) w
  have hq2 : ∀ w, 0 ≤ -q w := fun w =>
    quad_nonneg Λ (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0)) (fun z => -q z) hqc.neg
      (fun t w => by simp only [hqs]; ring) (fun z l hl => by
        have := hper_q z ⟨l, hl⟩
        simp only [norm_inv, neg_neg]
        have e1 : Real.exp (q (z + l)) = (Real.exp (-q (z + l)))⁻¹ := by rw [Real.exp_neg, inv_inv]
        have e2 : Real.exp (q z) = (Real.exp (-q z))⁻¹ := by rw [Real.exp_neg, inv_inv]
        rw [e1, e2, ← mul_inv, ← mul_inv]
        exact congrArg _ this) w
  have hdiag : ∀ z, D z z = 0 := fun z => by
    have hre : (D z z).re = 0 := by
      have h3 : q z = 0 := le_antisymm (by linarith [hq2 z]) (hq1 z)
      simp only [hqdef] at h3
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (by positivity)
      · exact h
    exact Complex.ext_iff.2 ⟨by simpa using hre, by simpa using hdiag_im z⟩
  have hD0 : ∀ z w, D z w = 0 := fun z w => by
    have e1 := hexpand z w
    rw [hdiag, hdiag, hdiag] at e1
    have e2 := hexpand (I • z) w
    rw [hdiag, hdiag, hdiag, hsm, hsm2, Complex.conj_I] at e2
    have hb : D w z = -D z w := by linear_combination (-1 : ℂ) * e1
    rw [hb] at e2
    have h2 : (2 * I) * D z w = 0 := by linear_combination -e2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
    · exact h
  have hper' : ∀ z (l : Λ), ψ (z + l) = ρ l * ψ z := fun z l => by
    rw [hper, hD0, hD0]; simp
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖) hψ.continuous.norm (fun z l hl =>
    (congrArg norm (hper' z ⟨l, hl⟩)).trans (by rw [norm_mul, hρ, _root_.one_mul]))
  have hb : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩
  have hconst : ∀ z, ψ z = ψ 0 := fun z => hψ.apply_eq_apply_of_bounded hb z 0
  refine ⟨hD0, fun l => ?_⟩
  have h4 := hper' 0 l
  rw [hconst (0 + (l : Fin g → ℂ))] at h4
  exact mul_right_cancel₀ (h0 0) (h4.symm.trans (_root_.one_mul _).symm)

/- English proof (translation)
Use `choose c hc' using hcov`. Use `⟨fun z => G (c z) z, fun z => ?_, fun j z hz => hc _ _ _ (hc' z) hz⟩` and prove the remaining obligations. Establish `hev : (fun w => G (c w) w) =ᶠ[𝓝 z] G (c z)` using `by filter_upwards [(hD (c z)).mem_nhds (hc' z)] with w hw using hc _ _ _ (hc' w) hw`. Conclude with `((hG (c z)).differentiableAt ((hD (c z)).mem_nhds (hc' z))).congr_of_eventuallyEq hev`.
-/
theorem exists_glue {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose c hc' using hcov
  refine ⟨fun z => G (c z) z, fun z => ?_, fun j z hz => hc _ _ _ (hc' z) hz⟩
  have hev : (fun w => G (c w) w) =ᶠ[𝓝 z] G (c z) := by
    filter_upwards [(hD (c z)).mem_nhds (hc' z)] with w hw using hc _ _ _ (hc' w) hw
  exact ((hG (c z)).differentiableAt ((hD (c z)).mem_nhds (hc' z))).congr_of_eventuallyEq hev

section Herm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

/- English proof (translation)
Simplify using `only [hermForm, add_dotProduct]`.
-/
theorem herm_add_left (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp only [hermForm, add_dotProduct]

/- English proof (translation)
Simplify using `only [hermForm, star_add, mulVec_add, dotProduct_add]`.
-/
theorem herm_add_right (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [hermForm, smul_dotProduct, smul_eq_mul]`.
-/
theorem herm_smul_left (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hermForm, zero_dotProduct]`.
-/
theorem herm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp only [hermForm, zero_dotProduct]

/- English proof (translation)
Establish `hH' : Hmᴴ = Hm` using `hH`. Simplify using `only [hermForm]`. Rewrite using `[starRingEnd_apply, ← star_dotProduct_star, Matrix.star_mulVec, star_star, hH', Matrix.dotProduct_mulVec]`.
-/
theorem herm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
  have hH' : Hmᴴ = Hm := hH
  simp only [hermForm]
  rw [starRingEnd_apply, ← star_dotProduct_star, Matrix.star_mulVec, star_star, hH',
    Matrix.dotProduct_mulVec]

/- English proof (translation)
Simplify using `only [hermForm, dotProduct, mulVec]`. Use `fun_prop`.
-/
theorem herm_continuous {a b : (Fin g → ℂ) → Fin g → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun z => hermForm Hm (a z) (b z) := by
  simp only [hermForm, dotProduct, mulVec]
  fun_prop

end Herm

/- English proof (translation)
Rewrite using `[Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f (fun _ => rfl)]`. Rewrite using `[← Finset.powerset_univ, show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide, Finset.prod_powerset_insert (by decide), show ({1} : Finset (Fin 2)).powerset = {∅, {1}} by decide, Finset.prod_pair (by decide), Finset.prod_pair (by decide)]`. Establish `h0 : (insert (0 : Fin 2) (∅ : Finset (Fin 2))) = {0}` using `by decide`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_finset_fin_two (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f (fun _ => rfl)]
  rw [← Finset.powerset_univ, show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Finset.prod_powerset_insert (by decide),
    show ({1} : Finset (Fin 2)).powerset = {∅, {1}} by decide,
    Finset.prod_pair (by decide), Finset.prod_pair (by decide)]
  have h0 : (insert (0 : Fin 2) (∅ : Finset (Fin 2))) = {0} := by decide
  rw [h0]
  ring

/- English proof (translation)
Rewrite using `[show (π : ℂ) * I * n = n * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
theorem exp_pi_I_int (n : ℤ) : cexp (π * I * n) = (-1) ^ n := by
  rw [show (π : ℂ) * I * n = n * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty]`. Conclude with `differentiableOn_const 1`. Consider the case `insert a s ha ih => simp only [Finset.prod_insert ha]`. Conclude with `(hf a).mul ih`.
-/
theorem differentiableOn_prod' {g : ℕ} {α : Type*} {f : α → (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (s : Finset α) (hf : ∀ i, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const 1
  | insert a s ha ih => simp only [Finset.prod_insert ha]; exact (hf a).mul ih

open GlobalTheory.CubeValues

/- English proof (translation)
Establish `hp'` using `(le_preimage_inf x _ _).1 hp`. Establish `hq'` using `(le_preimage_inf x _ _).1 hq`. Establish `hL : ⊤ ≤ x ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2)` using `(le_preimage_inf x _ _).2 ⟨hp'.2, hq'.2⟩`. Establish `hW : ⊤ ≤ x ⁻¹ᵁ ((M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2))` using `(le_preimage_inf x _ _).2 ⟨hp, hq⟩`. Take `⟨e, he⟩` from `(hv X x).2.1 _ hW`.

Establish `hinv : ∀ u : Γ(X, (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2))ˣ, valAt' x _ (u⁻¹).val = (valAt' x _ u.val)⁻¹` using `fun u => by`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[he, he, ← map_mul, Units.inv_mul, map_one]`. Unfold `LB.div`. Simplify using `only`.

Rewrite using `[val_unit_mul x hv hW, hinv, val_res x hv _ hW, val_res x hv _ hW, inv_mul_cancel_right₀ (val_unit_ne_zero x hv hL _)]`.
-/
theorem val_div (hv : ValueRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (M L : LB X)
    (p q : M.ι × L.ι) (hp : ⊤ ≤ x ⁻¹ᵁ (M.U p.1 ⊓ L.U p.2)) (hq : ⊤ ≤ x ⁻¹ᵁ (M.U q.1 ⊓ L.U q.2)) :
    valAt' x ((LB.div M L).U p ⊓ (LB.div M L).U q) ((LB.div M L).g p q).val *
      valAt' x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2).val =
      valAt' x (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1).val := by
  have hp' := (le_preimage_inf x _ _).1 hp
  have hq' := (le_preimage_inf x _ _).1 hq
  have hL : ⊤ ≤ x ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) := (le_preimage_inf x _ _).2 ⟨hp'.2, hq'.2⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ ((M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) :=
    (le_preimage_inf x _ _).2 ⟨hp, hq⟩
  obtain ⟨e, he⟩ := (hv X x).2.1 _ hW
  have hinv : ∀ u : Γ(X, (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2))ˣ,
      valAt' x _ (u⁻¹).val = (valAt' x _ u.val)⁻¹ := fun u => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [he, he, ← map_mul, Units.inv_mul, map_one]
  unfold LB.div
  dsimp only
  rw [val_unit_mul x hv hW, hinv, val_res x hv _ hW, val_res x hv _ hW,
    inv_mul_cancel_right₀ (val_unit_ne_zero x hv hL _)]

/- English proof (translation)
Take `⟨hcov, -, -⟩` from `hL`. Establish `hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i)`. Rewrite using `[hcov]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hmem`.

Conclude with `⟨i, ((hv _ _).1 _).2 hi⟩`.
-/
theorem exists_chart (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) : ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  exact ⟨i, ((hv _ _).1 _).2 hi⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `hiso`. Establish `hpt : ∀ z (I : ULift.{0} (Finset (Fin n))), (u.ex z).left ≫ (psum A y I.down).left = (u.ex (∑ k ∈ I.down, Y k z)).left` using `fun z I => by`. Rewrite using `[← Over.comp_left, comp_psum u (u.ex z) y (fun k => Y k z) (fun k => hy k z)]`. Establish `hMc : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j ↔ ∀ I : ULift.{0} (Finset (Fin n)), ⊤ ≤ (u.ex (∑ k ∈ I.down, Y k z)).left ⁻¹ᵁ L.U (j I)` using `fun z j => by`. Establish `h1` using `le_preimage_wchart (u.ex z).left L (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left) j`.

Simplify using `only [hpt] at h1`. Conclude with `h1`. Establish `hMg : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' → valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j') ((cubeLB A y L).g j j').val = ∏ I : ULift.{0} (Finset (Fin n)), valAt' (u.ex …` using `fun z j j' hj hj' => by`. Establish `h1` using `val_linComb (u.ex z).left hv L (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left) (fun I => (-1 : ℤ) ^ (n - I.down.card)) j j' hj hj'`. Simplify using `only [hpt] at h1`.

Conclude with `h1`. Take `⟨Fc, hFc⟩ : ∃ Fc : (ULift.{0} (Finset (Fin n)) → L.ι) → (Fin g → ℂ) → ℂ, Fc = fun j z => ∏ I : ULift.{0} (Finset (Fin n)), u.fr (j I) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))` from `⟨_, rfl⟩`. Establish `hFc_ne : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → Fc j z ≠ 0` using `fun z j hj => by`. Simplify using `only [hFc]`. Conclude with `Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (u.fr_ne _ _ ((hMc z j).1 hj I))`.

Establish `hFc_g : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' → Fc j z = valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j') ((cubeLB A y L).g j j').val * Fc j' z` using `fun z j j' hj hj' => by`. Rewrite using `[hMg z j j' hj hj']`. Simplify using `only [hFc]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun I _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_zpow, ← u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨(hMc z j).1 hj I, (hMc z j').1 hj' I⟩)]`. Establish `hdiv : ∀ z (p : (LB.div (cubeLB A y L) L).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U p.1 ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2` using `fun z p => le_preimage_inf _ _ _`. Establish `hex : ∀ z l, l ∈ u.Λ → u.ex (z + l) = u.ex z` using `fun z l hl => by`. Rewrite using `[u.ex_add, (u.ker l).2 hl, _root_.mul_one]`. Take `⟨G, hG⟩ : ∃ G : (LB.div (cubeLB A y L) L).ι → (Fin g → ℂ) → ℂ, G = fun p z => valAt' (u.ex z).left ((LB.div (cubeLB A y L) L).U p) (w.s p).val * u.fr p.2 z / Fc p.1 z` from `⟨_, rfl⟩`.

Establish `hG_ne : ∀ p z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p → G p z ≠ 0`. Introduce `p z hz`. Establish `h2` using `(hdiv z p).1 hz`. Simplify using `only [hG]`. Conclude with `div_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hz _) (u.fr_ne _ _ h2.2)) (hFc_ne z _ h2.1)`.

Establish `hcov : ∀ z, ∃ p, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}` using `fun z => by`. Take `⟨i, hi⟩` from `exists_chart hv hL u z`. Use `choose j hj using fun I : ULift.{0} (Finset (Fin n)) => exists_chart hv hL u (∑ k ∈ I.down, Y k z)`. Conclude with `⟨(j, i), (hdiv z (j, i)).2 ⟨(hMc z j).2 hj, hi⟩⟩`. Establish `hopen : ∀ p, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}` using `fun p => (u.hol _ (w.s p).val).1`.

Establish `hYd : ∀ I : ULift.{0} (Finset (Fin n)), Differentiable ℂ (fun z => ∑ k ∈ I.down, Y k z)` using `fun I => by`. Establish `h : ∀ k, Differentiable ℂ (Y k)` using `fun k => by`. Simplify using `using (LinearMap.toContinuousLinearMap (Y k)).differentiable`. Establish `h2 : ∀ s : Finset (Fin n), Differentiable ℂ (fun z => ∑ k ∈ s, Y k z)`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `differentiable_const 0`. Consider the case `insert b s hb ih => simp only [Finset.sum_insert hb]`. Conclude with `(h b).add ih`.

Conclude with `h2 I.down`. Establish `hGd : ∀ p, DifferentiableOn ℂ (G p) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}` using `fun p => by`. Establish `hsub2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2}` using `fun z hz => ((hdiv z p).1 hz).2`. Establish `hF : DifferentiableOn ℂ (Fc p.1) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}`. Simplify using `only [hFc]`.

Use `differentiableOn_prod' Finset.univ fun I => ?_` and prove the remaining obligations. Establish `hc : DifferentiableOn ℂ (fun z => u.fr (p.1 I) (∑ k ∈ I.down, Y k z)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}` using `(u.fr_hol (p.1 I)).comp (hYd I).differentiableOn (fun z hz => (hMc z p.1).1 ((hdiv z p).1 hz).1 I)`. Break down `neg_one_pow_eq_or ℤ (n - I.down.card) with h | h` into its components or cases. Simplify using `only [h, zpow_one]`. Conclude with `hc`.

Simplify using `only [h, _root_.zpow_neg_one]`. Conclude with `hc.inv fun z hz => u.fr_ne _ _ ((hMc z p.1).1 ((hdiv z p).1 hz).1 I)`. Simplify using `only [hG, div_eq_mul_inv]`. Conclude with `(((u.hol _ (w.s p).val).2).mul ((u.fr_hol p.2).mono hsub2)).mul (hF.inv fun z hz => hFc_ne z _ ((hdiv z p).1 hz).1)`. Establish `hcompat : ∀ p q z, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} → z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U q} → G p z = G q z`.

Introduce `p q z hp hq`. Establish `hp'` using `(hdiv z p).1 hp`. Establish `hq'` using `(hdiv z q).1 hq`. Establish `hpq : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((LB.div (cubeLB A y L) L).U p ⊓ (LB.div (cubeLB A y L) L).U q)` using `(le_preimage_inf _ _ _).2 ⟨hp, hq⟩`. Establish `hL2 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2)` using `(le_preimage_inf _ _ _).2 ⟨hp'.2, hq'.2⟩`.

Establish `e1` using `val_gen (u.ex z).left hv w hw p q hp hq`. Establish `e2` using `val_div hv (u.ex z).left (cubeLB A y L) L p q hp hq`. Establish `e3` using `u.fr_compat p.2 q.2 z hL2`. Establish `e4` using `hFc_g z p.1 q.1 hp'.1 hq'.1`. Establish `n1` using `val_unit_ne_zero _ hv hpq ((LB.div (cubeLB A y L) L).g p q)`.

Establish `n2` using `val_unit_ne_zero _ hv hL2 (L.g p.2 q.2)`. Establish `n3` using `hFc_ne z q.1 hq'.1`. Simplify using `only [hG]`. Rewrite using `[e1, e3, e4, ← e2]`. Clear the denominators using the available nonvanishing facts.

Take `⟨F, hFd, hFG⟩` from `exists_glue (fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}) G hopen hcov hGd hcompat`. Use `⟨F, hFd, fun z => ?_, fun z l hl => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `hcov z`. Rewrite using `[hFG p z hp]`. Conclude with `hG_ne p z hp`.

Take `⟨p, hp⟩` from `hcov z`. Establish `hp'` using `(hdiv z p).1 hp`. Establish `hpl : z + l ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}`. Rewrite using `[Set.mem_ofPred_eq, hex z l hl]`. Conclude with `hp`.

Rewrite using `[hFG p z hp, hFG p (z + l) hpl]`. Simplify using `only [hG]`. Rewrite using `[hex z l hl]`. Establish `e1` using `ha l hl p.2 z hp'.2`. Establish `hSl : ∀ I : ULift.{0} (Finset (Fin n)), ∑ k ∈ I.down, Y k l ∈ u.Λ` using `fun I => Submodule.sum_mem _ fun k _ => hY k l hl`.

Establish `e2 : Fc p.1 z = (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * Fc p.1 (z + l)`. Simplify using `only [hFc]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, ha _ (hSl I) (p.1 I) _ ((hMc z p.1).1 hp'.1 I)]`.

Rewrite using `[show ∑ k ∈ I.down, Y k (z + l) = ∑ k ∈ I.down, Y k z + ∑ k ∈ I.down, Y k l by`. Simplify using `only [map_add, Finset.sum_add_distrib]]`. Establish `n0` using `hFc_ne z p.1 hp'.1`. Establish `n1 : Fc p.1 (z + l) ≠ 0` using `hFc_ne (z + l) p.1 (by rw [hex z l hl]; exact hp'.1)`. Establish `n2 : (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) ≠ 0` using `fun h => n0 (by`.

Rewrite using `[e2, h, zero_mul])`. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_unit_of_iso (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {n : ℕ} (y : Fin n → (A ⟶ A))
    (Y : Fin n → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hY : ∀ k, ∀ l ∈ u.Λ, Y k l ∈ u.Λ)
    (hy : ∀ k z, u.ex z ≫ y k = u.ex (Y k z))
    (a : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l z * u.fr i (z + l))
    (hiso : LBIso L (cubeLB A y L)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ (∀ z, ψ z ≠ 0) ∧ ∀ z, ∀ l ∈ u.Λ,
      ψ (z + l) * a l z = (∏ I : ULift.{0} (Finset (Fin n)),
        a (∑ k ∈ I.down, Y k l) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * ψ z := by
  classical
  obtain ⟨w, hw⟩ := hiso
  have hpt : ∀ z (I : ULift.{0} (Finset (Fin n))),
      (u.ex z).left ≫ (psum A y I.down).left = (u.ex (∑ k ∈ I.down, Y k z)).left := fun z I => by
    rw [← Over.comp_left, comp_psum u (u.ex z) y (fun k => Y k z) (fun k => hy k z)]
  have hMc : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j ↔
        ∀ I : ULift.{0} (Finset (Fin n)), ⊤ ≤ (u.ex (∑ k ∈ I.down, Y k z)).left ⁻¹ᵁ L.U (j I) :=
    fun z j => by
      have h1 := le_preimage_wchart (u.ex z).left L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left) j
      simp only [hpt] at h1
      exact h1
  have hMg : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j') ((cubeLB A y L).g j j').val =
        ∏ I : ULift.{0} (Finset (Fin n)), valAt' (u.ex (∑ k ∈ I.down, Y k z)).left
          (L.U (j I) ⊓ L.U (j' I)) (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (n - I.down.card)) :=
    fun z j j' hj hj' => by
      have h1 := val_linComb (u.ex z).left hv L
        (fun I : ULift.{0} (Finset (Fin n)) => (psum A y I.down).left)
        (fun I => (-1 : ℤ) ^ (n - I.down.card)) j j' hj hj'
      simp only [hpt] at h1
      exact h1
  obtain ⟨Fc, hFc⟩ : ∃ Fc : (ULift.{0} (Finset (Fin n)) → L.ι) → (Fin g → ℂ) → ℂ,
      Fc = fun j z => ∏ I : ULift.{0} (Finset (Fin n)),
        u.fr (j I) (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card)) := ⟨_, rfl⟩
  have hFc_ne : ∀ z (j : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → Fc j z ≠ 0 := fun z j hj => by
    simp only [hFc]
    exact Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (u.fr_ne _ _ ((hMc z j).1 hj I))
  have hFc_g : ∀ z (j j' : ULift.{0} (Finset (Fin n)) → L.ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U j' →
      Fc j z = valAt' (u.ex z).left ((cubeLB A y L).U j ⊓ (cubeLB A y L).U j')
        ((cubeLB A y L).g j j').val * Fc j' z := fun z j j' hj hj' => by
    rw [hMg z j j' hj hj']
    simp only [hFc]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [← mul_zpow, ← u.fr_compat _ _ _
      ((le_preimage_inf _ _ _).2 ⟨(hMc z j).1 hj I, (hMc z j').1 hj' I⟩)]
  have hdiv : ∀ z (p : (LB.div (cubeLB A y L) L).ι),
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p ↔
        ⊤ ≤ (u.ex z).left ⁻¹ᵁ (cubeLB A y L).U p.1 ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2 :=
    fun z p => le_preimage_inf _ _ _
  have hex : ∀ z l, l ∈ u.Λ → u.ex (z + l) = u.ex z := fun z l hl => by
    rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  obtain ⟨G, hG⟩ : ∃ G : (LB.div (cubeLB A y L) L).ι → (Fin g → ℂ) → ℂ,
      G = fun p z => valAt' (u.ex z).left ((LB.div (cubeLB A y L) L).U p) (w.s p).val *
        u.fr p.2 z / Fc p.1 z := ⟨_, rfl⟩
  have hG_ne : ∀ p z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p → G p z ≠ 0 := by
    intro p z hz
    have h2 := (hdiv z p).1 hz
    simp only [hG]
    exact div_ne_zero (mul_ne_zero (val_unit_ne_zero _ hv hz _) (u.fr_ne _ _ h2.2))
      (hFc_ne z _ h2.1)
  have hcov : ∀ z, ∃ p, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun z => by
    obtain ⟨i, hi⟩ := exists_chart hv hL u z
    choose j hj using fun I : ULift.{0} (Finset (Fin n)) => exists_chart hv hL u (∑ k ∈ I.down, Y k z)
    exact ⟨(j, i), (hdiv z (j, i)).2 ⟨(hMc z j).2 hj, hi⟩⟩
  have hopen : ∀ p, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
    fun p => (u.hol _ (w.s p).val).1
  have hYd : ∀ I : ULift.{0} (Finset (Fin n)), Differentiable ℂ (fun z => ∑ k ∈ I.down, Y k z) :=
    fun I => by
      have h : ∀ k, Differentiable ℂ (Y k) := fun k => by
        simpa using (LinearMap.toContinuousLinearMap (Y k)).differentiable
      have h2 : ∀ s : Finset (Fin n), Differentiable ℂ (fun z => ∑ k ∈ s, Y k z) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact differentiable_const 0
        | insert b s hb ih => simp only [Finset.sum_insert hb]; exact (h b).add ih
      exact h2 I.down
  have hGd : ∀ p, DifferentiableOn ℂ (G p)
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := fun p => by
    have hsub2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} ⊆
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.2} := fun z hz => ((hdiv z p).1 hz).2
    have hF : DifferentiableOn ℂ (Fc p.1)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      simp only [hFc]
      refine differentiableOn_prod' Finset.univ fun I => ?_
      have hc : DifferentiableOn ℂ (fun z => u.fr (p.1 I) (∑ k ∈ I.down, Y k z))
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} :=
        (u.fr_hol (p.1 I)).comp (hYd I).differentiableOn
          (fun z hz => (hMc z p.1).1 ((hdiv z p).1 hz).1 I)
      rcases neg_one_pow_eq_or ℤ (n - I.down.card) with h | h
      · simp only [h, zpow_one]; exact hc
      · simp only [h, _root_.zpow_neg_one]
        exact hc.inv fun z hz => u.fr_ne _ _ ((hMc z p.1).1 ((hdiv z p).1 hz).1 I)
    simp only [hG, div_eq_mul_inv]
    exact (((u.hol _ (w.s p).val).2).mul ((u.fr_hol p.2).mono hsub2)).mul
      (hF.inv fun z hz => hFc_ne z _ ((hdiv z p).1 hz).1)
  have hcompat : ∀ p q z, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} →
      z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U q} → G p z = G q z := by
    intro p q z hp hq
    have hp' := (hdiv z p).1 hp
    have hq' := (hdiv z q).1 hq
    have hpq : ⊤ ≤ (u.ex z).left ⁻¹ᵁ
        ((LB.div (cubeLB A y L) L).U p ⊓ (LB.div (cubeLB A y L) L).U q) :=
      (le_preimage_inf _ _ _).2 ⟨hp, hq⟩
    have hL2 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U p.2 ⊓ L.U q.2) :=
      (le_preimage_inf _ _ _).2 ⟨hp'.2, hq'.2⟩
    have e1 := val_gen (u.ex z).left hv w hw p q hp hq
    have e2 := val_div hv (u.ex z).left (cubeLB A y L) L p q hp hq
    have e3 := u.fr_compat p.2 q.2 z hL2
    have e4 := hFc_g z p.1 q.1 hp'.1 hq'.1
    have n1 := val_unit_ne_zero _ hv hpq ((LB.div (cubeLB A y L) L).g p q)
    have n2 := val_unit_ne_zero _ hv hL2 (L.g p.2 q.2)
    have n3 := hFc_ne z q.1 hq'.1
    simp only [hG]
    rw [e1, e3, e4, ← e2]
    field_simp
  obtain ⟨F, hFd, hFG⟩ := exists_glue
    (fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p}) G hopen hcov hGd hcompat
  refine ⟨F, hFd, fun z => ?_, fun z l hl => ?_⟩
  · obtain ⟨p, hp⟩ := hcov z
    rw [hFG p z hp]
    exact hG_ne p z hp
  · obtain ⟨p, hp⟩ := hcov z
    have hp' := (hdiv z p).1 hp
    have hpl : z + l ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (cubeLB A y L) L).U p} := by
      rw [Set.mem_ofPred_eq, hex z l hl]
      exact hp
    rw [hFG p z hp, hFG p (z + l) hpl]
    simp only [hG]
    rw [hex z l hl]
    have e1 := ha l hl p.2 z hp'.2
    have hSl : ∀ I : ULift.{0} (Finset (Fin n)), ∑ k ∈ I.down, Y k l ∈ u.Λ :=
      fun I => Submodule.sum_mem _ fun k _ => hY k l hl
    have e2 : Fc p.1 z = (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) * Fc p.1 (z + l) := by
      simp only [hFc]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← mul_zpow, ha _ (hSl I) (p.1 I) _ ((hMc z p.1).1 hp'.1 I)]
      rw [show ∑ k ∈ I.down, Y k (z + l) = ∑ k ∈ I.down, Y k z + ∑ k ∈ I.down, Y k l by
        simp only [map_add, Finset.sum_add_distrib]]
    have n0 := hFc_ne z p.1 hp'.1
    have n1 : Fc p.1 (z + l) ≠ 0 := hFc_ne (z + l) p.1 (by rw [hex z l hl]; exact hp'.1)
    have n2 : (∏ I : ULift.{0} (Finset (Fin n)), a (∑ k ∈ I.down, Y k l)
        (∑ k ∈ I.down, Y k z) ^ ((-1 : ℤ) ^ (n - I.down.card))) ≠ 0 := fun h => n0 (by
      rw [e2, h, zero_mul])
    rw [e1, e2]
    field_simp

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart hv hL u 0`. Establish `hper : ∀ (a : u.Λ) z, u.ex (z + a) = u.ex z` using `fun a z => by`. Rewrite using `[u.ex_add, (u.ker a).2 a.2, _root_.mul_one]`. Establish `hne : u.fr i (0 + (l : Fin g → ℂ) + m) ≠ 0` using `u.fr_ne i _ (by rw [hper m, hper l]; exact hi)`. Establish `h1` using `hfr (l + m) i 0 hi`.

Establish `h2` using `hfr l i 0 hi`. Establish `h3` using `hfr m i (0 + l) (by rw [hper l]; exact hi)`. Rewrite `h1` using `[Submodule.coe_add, ← add_assoc]`. Rewrite `h2` using `[h3]`. Establish `key` using `mul_right_cancel₀ hne (h1.symm.trans (h2.trans (_root_.mul_assoc _ _ _).symm))`.

Simplify using `only [herm_zero_left, mul_zero, zero_add] at key`. Establish `hsum : hermForm Hm (↑l + ↑m) (↑l + ↑m) = hermForm Hm l l + hermForm Hm l m + starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m`. Rewrite using `[herm_add_left, herm_add_right, herm_add_right, ← herm_conj Hm hH]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hsum]`.

Establish `hc : hermForm Hm l m - starRingEnd ℂ (hermForm Hm l m) = 2 * ((hermForm Hm l m).im : ℂ) * I`. Rewrite using `[Complex.sub_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn' : (n : ℂ) = ((hermForm Hm l m).im : ℂ)` using `by exact_mod_cast hn`.

Establish `hX` using `Complex.exp_ne_zero (π / 2 * (hermForm Hm l l + hermForm Hm l m + starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m))`. Rewrite using `[← exp_pi_I_int n]`. Use `mul_right_cancel₀ hX ?_` and prove the remaining obligations. Rewrite using `[key]`. Establish `hE : cexp (↑π / 2 * hermForm Hm ↑l ↑l) * cexp (↑π * hermForm Hm ↑l ↑m + ↑π / 2 * hermForm Hm ↑m ↑m) = cexp (↑π * I * ↑n) * cexp (↑π / 2 * (hermForm Hm ↑l ↑l + hermForm Hm ↑l ↑m + starRingEnd ℂ (hermForm Hm ↑l ↑m) + hermForm Hm ↑m ↑m))`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Take the linear combination `((π : ℂ) / 2) * hc - ((π : ℂ) * I) * hn'`. Take the linear combination `(χ l * χ m) * hE`.
-/
theorem semicharacter_rule (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (χ : u.Λ → ℂ)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l))
    (l m : u.Λ) (n : ℤ) (hn : (n : ℝ) = (hermForm Hm l m).im) :
    χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := exists_chart hv hL u 0
  have hper : ∀ (a : u.Λ) z, u.ex (z + a) = u.ex z := fun a z => by
    rw [u.ex_add, (u.ker a).2 a.2, _root_.mul_one]
  have hne : u.fr i (0 + (l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hper m, hper l]; exact hi)
  have h1 := hfr (l + m) i 0 hi
  have h2 := hfr l i 0 hi
  have h3 := hfr m i (0 + l) (by rw [hper l]; exact hi)
  rw [Submodule.coe_add, ← add_assoc] at h1
  rw [h3] at h2
  have key := mul_right_cancel₀ hne (h1.symm.trans (h2.trans (_root_.mul_assoc _ _ _).symm))
  simp only [herm_zero_left, mul_zero, zero_add] at key
  have hsum : hermForm Hm (↑l + ↑m) (↑l + ↑m) = hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m := by
    rw [herm_add_left, herm_add_right, herm_add_right, ← herm_conj Hm hH]; ring
  rw [hsum] at key
  have hc : hermForm Hm l m - starRingEnd ℂ (hermForm Hm l m) =
      2 * ((hermForm Hm l m).im : ℂ) * I := by
    rw [Complex.sub_conj]; push_cast; ring
  have hn' : (n : ℂ) = ((hermForm Hm l m).im : ℂ) := by exact_mod_cast hn
  have hX := Complex.exp_ne_zero (π / 2 * (hermForm Hm l l + hermForm Hm l m +
      starRingEnd ℂ (hermForm Hm l m) + hermForm Hm m m))
  rw [← exp_pi_I_int n]
  refine mul_right_cancel₀ hX ?_
  rw [key]
  have hE : cexp (↑π / 2 * hermForm Hm ↑l ↑l) * cexp (↑π * hermForm Hm ↑l ↑m + ↑π / 2 * hermForm Hm ↑m ↑m) =
      cexp (↑π * I * ↑n) * cexp (↑π / 2 * (hermForm Hm ↑l ↑l + hermForm Hm ↑l ↑m +
      starRingEnd ℂ (hermForm Hm ↑l ↑m) + hermForm Hm ↑m ↑m)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination ((π : ℂ) / 2) * hc - ((π : ℂ) * I) * hn'
  linear_combination (χ l * χ m) * hE

/- English proof (translation)
Introduce `hv hh P _ u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ f F hF hexF hiso`. Establish `hv' : ValueRules` using `hv`. Use `clear hv hh`. Establish `: DiscreteTopology u.Λ` using `u.discrete`. Establish `: IsZLattice ℝ u.Λ` using `⟨u.full⟩`.

Establish `hfr' : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l)` using `hfr`. Establish `hχne : ∀ l, χ l ≠ 0` using `fun l h => by`. Establish `h1` using `hχ l`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Establish `hχ0 : χ 0 = 1`. Establish `h` using `semicharacter_rule hv' P.isLB u hH χ hfr' 0 0 0 (by simp [herm_zero_left])`. Simplify using `only [add_zero, zpow_zero, _root_.mul_one] at h`. Conclude with `mul_right_cancel₀ (hχne 0) (h.symm.trans (_root_.one_mul _).symm)`. Take `⟨a, ha_def⟩ : ∃ a : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, a = fun l z => if h : l ∈ u.Λ then χ ⟨l, h⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) else 1` from `⟨_, rfl⟩`.

Establish `ha_mem : ∀ l (hl : l ∈ u.Λ) z, a l z = χ ⟨l, hl⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)` using `fun l hl z => by`. Simplify using `only [ha_def, dif_pos hl]`. Establish `ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = a l z * u.fr i (z + l)` using `fun l hl i z hz => by rw [ha_mem l hl]; exact hfr' ⟨l, hl⟩ i z hz`. Take `⟨ψ, hψd, hψ0, hψp⟩` from `exists_unit_of_iso hv' P.isLB u ![𝟙 P.A, f] ![LinearMap.id, F] (by intro k; fin_cases k`. Simplify using the standard rewrite rules.

Simplify using `using hF)`. Use the proof step `(by intro k z; fin_cases k`. Simplify using the standard rewrite rules. Simplify using `[hexF])`. Use `a ha hiso`.

Establish `hprod : ∀ z l, l ∈ u.Λ → ψ (z + l) * a l z = a 0 0 * (a l z)⁻¹ * (a (F l) (F z))⁻¹ * a (l + F l) (z + F z) * ψ z`. Introduce `z l hl`. Rewrite using `[hψp z l hl, prod_finset_fin_two (fun J => a (∑ k ∈ J, (![LinearMap.id, F] k) l) (∑ k ∈ J, (![LinearMap.id, F] k) z) ^ ((-1 : ℤ) ^ (2 - J.card)))]`. Simplify using the standard rewrite rules. Take `⟨D, hD⟩ : ∃ D : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, D = fun z w => hermForm Hm z (F w) + hermForm Hm (F z) w - hermForm Hm z w` from `⟨_, rfl⟩`.

Take `⟨ρ, hρdef⟩ : ∃ ρ : u.Λ → ℂ, ρ = fun l => χ (l + ⟨F l, hF l l.2⟩) * (χ l)⁻¹ * (χ l)⁻¹ * (χ ⟨F l, hF l l.2⟩)⁻¹` from `⟨_, rfl⟩`. Establish `hFc : Continuous F` using `F.continuous_of_finiteDimensional`. Establish `hc : Continuous fun z => D z z`. Simplify using `only [hD]`. Conclude with `((herm_continuous Hm continuous_id hFc).add (herm_continuous Hm hFc continuous_id)).sub (herm_continuous Hm continuous_id continuous_id)`.

Establish `hadd : ∀ z z' w, D (z + z') w = D z w + D z' w` using `fun z z' w => by`. Simplify using `only [hD, herm_add_left, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w` using `fun t z w => by`. Simplify using `only [hD, herm_smul_left, map_smul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hst : ∀ z w, D w z = starRingEnd ℂ (D z w)` using `fun z w => by`. Simplify using `only [hD, map_sub, map_add, ← herm_conj Hm hH]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρ : ∀ l, ‖ρ l‖ = 1` using `fun l => by`.

Simplify using `[hρdef, hχ]`. Establish `hper : ∀ z (l : u.Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z`. Introduce `z l`. Establish `hl` using `l.2`. Establish `hFl` using `hF l l.2`.

Establish `hlF : (l : Fin P.g → ℂ) + F l ∈ u.Λ` using `Submodule.add_mem _ hl hFl`. Establish `key` using `hprod z l hl`. Rewrite `key` using `[ha_mem 0 (Submodule.zero_mem _), ha_mem l hl, ha_mem (F l) hFl, ha_mem _ hlF]`. Establish `h0' : (⟨0, Submodule.zero_mem _⟩ : u.Λ) = 0` using `rfl`. Establish `hlF' : (⟨(l : Fin P.g → ℂ) + F l, hlF⟩ : u.Λ) = l + ⟨F l, hFl⟩` using `rfl`.

Rewrite `key` using `[h0', hχ0, hlF']`. Simplify using `only [herm_zero_left, mul_zero, zero_add, Complex.exp_zero, _root_.mul_one, _root_.one_mul] at key`. Establish `hX : cexp (π * D z l + π / 2 * D l l) = cexp (π * hermForm Hm (z + F z) (l + F l) + π / 2 * hermForm Hm (l + F l) (l + F l)) * (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ * (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ * (cexp (π * hermForm Hm (F z) (F l) …`. Simplify using `only [← Complex.exp_neg, ← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [hD, herm_add_left, herm_add_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hX, hρdef]`. Establish `e1` using `Complex.exp_ne_zero (π * hermForm Hm z l + π / 2 * hermForm Hm l l)`. Establish `e2` using `Complex.exp_ne_zero (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l))`.

Establish `c1` using `hχne l`. Establish `c2` using `hχne ⟨F l, hFl⟩`. Establish `hmul` using `mul_ne_zero c1 e1`. Rewrite using `[← mul_inv_cancel_right₀ hmul (ψ (z + l)), key]`. Clear the denominators using the available nonvanishing facts.

Take `⟨hD0, hρ1⟩` from `form_eq_zero_of_unit u.Λ ψ hψd hψ0 D hc hadd hsm hst ρ hρ hper`. Use `⟨fun z w => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `h1` using `hD0 z w`. Simplify using `only [hD] at h1`. Take the linear combination `-h1`.

Establish `h1` using `hρ1 l`. Simplify using `only [hρdef] at h1`. Establish `h2` using `semicharacter_rule hv' P.isLB u hH χ hfr' l ⟨F l, hF l l.2⟩ (Ef l ⟨F l, hF l l.2⟩) (hE _ _)`. Rewrite `h1` using `[h2]`. Establish `c1` using `hχne l`.

Establish `c2` using `hχne ⟨F l, hF l l.2⟩`. Clear denominators, using `at h1` for the nonvanishing conditions. Conclude with `h1.symm`.
-/
theorem appellHumbert_data_of_iso_cube :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (P : Out.PolAV (Sp ℂ)) [IsCommMonObj P.A] (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (f : P.A ⟶ P.A) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u.Λ), (∀ z, u.ex (F z) = u.ex z ≫ f) → LBIso P.L (cubeLB P.A ![𝟙 P.A, f] P.L) → (∀ z w, hermForm Hm z w = hermForm Hm z (F w) + hermForm Hm (F z) w) ∧ ∀ l : u.Λ, χ l = (-1) ^ Ef l ⟨F l, hF l l.2⟩) := by
  classical
  intro hv hh P _ u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ f F hF hexF hiso
  have hv' : ValueRules := hv
  clear hv hh
  have : DiscreteTopology u.Λ := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hfr' : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z =
      (χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l)) * u.fr i (z + l) := hfr
  have hχne : ∀ l, χ l ≠ 0 := fun l h => by
    have h1 := hχ l
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hχ0 : χ 0 = 1 := by
    have h := semicharacter_rule hv' P.isLB u hH χ hfr' 0 0 0 (by simp [herm_zero_left])
    simp only [add_zero, zpow_zero, _root_.mul_one] at h
    exact mul_right_cancel₀ (hχne 0) (h.symm.trans (_root_.one_mul _).symm)
  obtain ⟨a, ha_def⟩ : ∃ a : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, a = fun l z =>
      if h : l ∈ u.Λ then χ ⟨l, h⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) else 1 :=
    ⟨_, rfl⟩
  have ha_mem : ∀ l (hl : l ∈ u.Λ) z,
      a l z = χ ⟨l, hl⟩ * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) := fun l hl z => by
    simp only [ha_def, dif_pos hl]
  have ha : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = a l z * u.fr i (z + l) :=
    fun l hl i z hz => by rw [ha_mem l hl]; exact hfr' ⟨l, hl⟩ i z hz
  obtain ⟨ψ, hψd, hψ0, hψp⟩ := exists_unit_of_iso hv' P.isLB u ![𝟙 P.A, f] ![LinearMap.id, F]
    (by intro k; fin_cases k
        · simp
        · simpa using hF)
    (by intro k z; fin_cases k
        · simp
        · simp [hexF])
    a ha hiso
  have hprod : ∀ z l, l ∈ u.Λ → ψ (z + l) * a l z =
      a 0 0 * (a l z)⁻¹ * (a (F l) (F z))⁻¹ * a (l + F l) (z + F z) * ψ z := by
    intro z l hl
    rw [hψp z l hl, prod_finset_fin_two (fun J => a (∑ k ∈ J, (![LinearMap.id, F] k) l)
      (∑ k ∈ J, (![LinearMap.id, F] k) z) ^ ((-1 : ℤ) ^ (2 - J.card)))]
    simp
  obtain ⟨D, hD⟩ : ∃ D : (Fin P.g → ℂ) → (Fin P.g → ℂ) → ℂ, D = fun z w =>
      hermForm Hm z (F w) + hermForm Hm (F z) w - hermForm Hm z w := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : u.Λ → ℂ, ρ = fun l => χ (l + ⟨F l, hF l l.2⟩) * (χ l)⁻¹ * (χ l)⁻¹ *
      (χ ⟨F l, hF l l.2⟩)⁻¹ := ⟨_, rfl⟩
  have hFc : Continuous F := F.continuous_of_finiteDimensional
  have hc : Continuous fun z => D z z := by
    simp only [hD]
    exact ((herm_continuous Hm continuous_id hFc).add (herm_continuous Hm hFc continuous_id)).sub
      (herm_continuous Hm continuous_id continuous_id)
  have hadd : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [hD, herm_add_left, map_add]; ring
  have hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w := fun t z w => by
    simp only [hD, herm_smul_left, map_smul]; ring
  have hst : ∀ z w, D w z = starRingEnd ℂ (D z w) := fun z w => by
    simp only [hD, map_sub, map_add, ← herm_conj Hm hH]; ring
  have hρ : ∀ l, ‖ρ l‖ = 1 := fun l => by
    simp [hρdef, hχ]
  have hper : ∀ z (l : u.Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z := by
    intro z l
    have hl := l.2
    have hFl := hF l l.2
    have hlF : (l : Fin P.g → ℂ) + F l ∈ u.Λ := Submodule.add_mem _ hl hFl
    have key := hprod z l hl
    rw [ha_mem 0 (Submodule.zero_mem _), ha_mem l hl, ha_mem (F l) hFl, ha_mem _ hlF] at key
    have h0' : (⟨0, Submodule.zero_mem _⟩ : u.Λ) = 0 := rfl
    have hlF' : (⟨(l : Fin P.g → ℂ) + F l, hlF⟩ : u.Λ) = l + ⟨F l, hFl⟩ := rfl
    rw [h0', hχ0, hlF'] at key
    simp only [herm_zero_left, mul_zero, zero_add, Complex.exp_zero, _root_.mul_one,
      _root_.one_mul] at key
    have hX : cexp (π * D z l + π / 2 * D l l) =
        cexp (π * hermForm Hm (z + F z) (l + F l) + π / 2 * hermForm Hm (l + F l) (l + F l)) *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))⁻¹ *
        (cexp (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l)))⁻¹ := by
      simp only [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      simp only [hD, herm_add_left, herm_add_right]
      ring
    rw [hX, hρdef]
    have e1 := Complex.exp_ne_zero (π * hermForm Hm z l + π / 2 * hermForm Hm l l)
    have e2 := Complex.exp_ne_zero (π * hermForm Hm (F z) (F l) + π / 2 * hermForm Hm (F l) (F l))
    have c1 := hχne l
    have c2 := hχne ⟨F l, hFl⟩
    have hmul := mul_ne_zero c1 e1
    rw [← mul_inv_cancel_right₀ hmul (ψ (z + l)), key]
    field_simp
  obtain ⟨hD0, hρ1⟩ := form_eq_zero_of_unit u.Λ ψ hψd hψ0 D hc hadd hsm hst ρ hρ hper
  refine ⟨fun z w => ?_, fun l => ?_⟩
  · have h1 := hD0 z w
    simp only [hD] at h1
    linear_combination -h1
  · have h1 := hρ1 l
    simp only [hρdef] at h1
    have h2 := semicharacter_rule hv' P.isLB u hH χ hfr' l ⟨F l, hF l l.2⟩ (Ef l ⟨F l, hF l l.2⟩)
      (hE _ _)
    rw [h2] at h1
    have c1 := hχne l
    have c2 := hχne ⟨F l, hF l l.2⟩
    field_simp at h1
    exact h1.symm

end GlobalTheory.SelfCube
