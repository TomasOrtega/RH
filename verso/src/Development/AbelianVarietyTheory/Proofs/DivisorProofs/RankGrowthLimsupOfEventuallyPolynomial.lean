import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat

set_option autoImplicit false

namespace GlobalTheory.CompHt

open Filter Topology
open scoped ENNReal

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
/- English proof (translation)
Establish `hk' : (0 : ℝ) < (k : ℝ) ^ D`. Establish `: (0 : ℝ) < k` using `by exact_mod_cast hk`. Check the signs of the components of the expression. Rewrite using `[ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]`. Simplify using the standard rewrite rules.
-/
private lemma factorial_mul_div_pow_ennreal_eq_ofReal (D k m : ℕ) (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * ((m : ℕ∞) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      ENNReal.ofReal ((D.factorial : ℝ) * (m : ℝ) / (k : ℝ) ^ D) := by
  have hk' : (0 : ℝ) < (k : ℝ) ^ D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  simp

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
/- English proof (translation)
Establish `hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D` using `by simp`. Break down `hQ.lt_or_eq with hlt | heq` into its components or cases. Establish `hc : Q.coeff D = 0` using `Polynomial.coeff_eq_zero_of_degree_lt hlt`. Rewrite using `[hc]`. Simplify using `using Polynomial.div_tendsto_zero_of_degree_lt Q (Polynomial.X ^ D) (by rw [hX]; exact hlt)`.

Establish `hc : Q.leadingCoeff = Q.coeff D`. Rewrite using `[Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]`. Use `Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq Q (Polynomial.X ^ D) (by rw [hX, heq])` as an intermediate fact. Simplify `this` using `[hc]`.
-/
private lemma tendsto_eval_div_pow_atTop_coeff_of_degree_le (Q : Polynomial ℝ) (D : ℕ) (hQ : Q.degree ≤ D) :
    Tendsto (fun y : ℝ => Q.eval y / y ^ D) atTop (𝓝 (Q.coeff D)) := by
  have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
  rcases hQ.lt_or_eq with hlt | heq
  · have hc : Q.coeff D = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    rw [hc]
    simpa using Polynomial.div_tendsto_zero_of_degree_lt Q (Polynomial.X ^ D) (by rw [hX]; exact hlt)
  · have hc : Q.leadingCoeff = Q.coeff D := by
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]
    have := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq Q (Polynomial.X ^ D) (by rw [hX, heq])
    simpa [hc] using this

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in

/- English proof (translation)
Introduce `D a h H ha hev`. Use `set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef`. Establish `hQdeg : Q.degree = H.degree` using `Polynomial.degree_map _ _`. Establish `hak : Tendsto (fun k : ℕ => a * k) atTop atTop` using `tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id`. Establish `hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop` using `tendsto_natCast_atTop_atTop.comp hak`.

Establish `hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ)` using `by filter_upwards [hak.eventually hev] with k hk`. Establish `hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ)` using `by simp`. Rewrite using `[hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]`. Simplify using the standard rewrite rules. Use `set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg`.

Establish `hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D * (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D)` using `by filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1`. Establish `hk0 : (k : ℝ) ≠ 0` using `by exact_mod_cast (show k ≠ 0 by omega)`. Establish `ha0 : (a : ℝ) ≠ 0` using `by exact_mod_cast (show a ≠ 0 by omega)`. Simplify using `only [hg]`. Rewrite using `[hk]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop`. Unfold `_root_.GlobalTheory.CompHt.growth`.

Use `limsup_congr ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with k hk`. Conclude with `factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk`. Use `⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩` and prove the remaining obligations. Establish `hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D))`.

Use `Tendsto.congr' (EventuallyEq.symm hg_eq) ?_` and prove the remaining obligations. Conclude with `((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _`. Rewrite using `[hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]`. Establish `hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ)`. Rewrite using `[hQdef, Polynomial.coeff_map]`.

Establish `: ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ)` using `by rw [hδ]`. Move the coercions through the operations in `at this ⊢`. Rewrite using `[this]`. Simplify using `only [eq_ratCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hc, ENNReal.ofReal_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hQdeg' : (D : WithBot ℕ) < Q.degree` using `hQdeg ▸ hdeg`. Establish `hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D` using `by simp`.

Establish `hlc : 0 < Q.leadingCoeff`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hpos : 0 < Q.degree` using `lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'`. Establish `hbot` using `(Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hpos hneg).comp hakR`.

Establish `hneg'` using `hbot.eventually (eventually_lt_atBot (0 : ℝ))`. Take `⟨k, hk1, hk2⟩` from `(hneg'.and hval).exists`. Simplify using `only [Function.comp_apply] at hk1`. Rewrite `hk1` using `[← hk2]`. Conclude with `absurd hk1 (not_lt.2 (Nat.cast_nonneg _))`.

Establish `hT : Tendsto g atTop atTop`. Use `Tendsto.congr' (EventuallyEq.symm hg_eq) ?_` and prove the remaining obligations. Use `Tendsto.const_mul_atTop (by positivity) ?_` and prove the remaining obligations. Use `(Polynomial.div_tendsto_atTop_of_degree_gt Q (Polynomial.X ^ D) (by rw [hX]; exact hQdeg') (by simp) ?_).comp hakR |>.congr fun k => by simp` and prove the remaining obligations. Simplify using `using hlc.le`.

Rewrite using `[hlim]`. Conclude with `(ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq`.
-/
theorem _root_.GlobalTheory.CompHt.growth_of_eventually_eq_eval :
    ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) →
      (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D →
        _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧
      ((D : WithBot ℕ) < H.degree → _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  intro D a h H ha hev
  set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef
  have hQdeg : Q.degree = H.degree := Polynomial.degree_map _ _

  have hak : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id
  have hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hak

  have hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ) := by
    filter_upwards [hak.eventually hev] with k hk
    have hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ) := by simp
    rw [hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]
    simp

  set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg
  have hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D *
      (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D) := by
    filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    simp only [hg]
    rw [hk]
    push_cast
    field_simp
    ring
  have hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop := by
    unfold _root_.GlobalTheory.CompHt.growth
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk
  refine ⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩
  · have hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D)) := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      exact ((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _
    rw [hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]
    have hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ) := by
      rw [hQdef, Polynomial.coeff_map]
      have : ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ) := by rw [hδ]
      push_cast at this ⊢
      rw [this]
      simp only [eq_ratCast]
      ring
    rw [hc, ENNReal.ofReal_natCast]
    push_cast
    rfl
  · have hQdeg' : (D : WithBot ℕ) < Q.degree := hQdeg ▸ hdeg
    have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
    have hlc : 0 < Q.leadingCoeff := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < Q.degree := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'
      have hbot := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hpos hneg).comp hakR
      have hneg' := hbot.eventually (eventually_lt_atBot (0 : ℝ))
      obtain ⟨k, hk1, hk2⟩ := (hneg'.and hval).exists
      simp only [Function.comp_apply] at hk1
      rw [← hk2] at hk1
      exact absurd hk1 (not_lt.2 (Nat.cast_nonneg _))
    have hT : Tendsto g atTop atTop := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      refine (Polynomial.div_tendsto_atTop_of_degree_gt Q (Polynomial.X ^ D) (by rw [hX]; exact hQdeg')
        (by simp) ?_).comp hakR |>.congr fun k => by simp
      simpa using hlc.le
    rw [hlim]
    exact (ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq

end GlobalTheory.CompHt
