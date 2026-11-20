import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.UmatUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.EntryMulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ConeStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ContVal

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

/- English proof (translation)
Establish `e1 : ∑ b ∈ F, μ (A b) = ∫⁻ x, ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x ∂μ`. Rewrite using `[lintegral_finset_sum _ fun b _ => measurable_one.indicator (hA b)]`. Conclude with `Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hA b)).symm`. Establish `e2 : (R : ℝ≥0∞) * μ Y = ∫⁻ x, Y.indicator (fun _ => (R : ℝ≥0∞)) x ∂μ` using `(lintegral_indicator_const hY _).symm`. Rewrite using `[e1, e2]`.

Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ Y`. Rewrite using `[Set.indicator_of_mem hx]`. Establish `: ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x = ((F.filter fun b => x ∈ A b).card : ℝ≥0∞)`. Simplify using `[Set.indicator_apply]`.

Rewrite using `[this]`. Conclude with `Nat.cast_le.2 (by`. Use `hR x (F.filter fun b => x ∈ A b) (Finset.filter_subset _ _) fun b hb => (Finset.mem_filter.1 hb).2)` and compare the differences between its conclusion and the goal. Rewrite using `[Set.indicator_of_notMem hx]`. Use `(Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun h => hx (hsub b hb h)) _).le` and prove the remaining obligations.
-/
theorem sum_meas_le {α β : Type*} [MeasurableSpace α] (μ : Measure α) (F : Finset β) (A : β → Set α)
    (hA : ∀ b, MeasurableSet (A b)) {Y : Set α} (hY : MeasurableSet Y) (hsub : ∀ b ∈ F, A b ⊆ Y) (R : ℕ)
    (hR : ∀ x, ∀ S : Finset β, S ⊆ F → (∀ b ∈ S, x ∈ A b) → S.card ≤ R) : ∑ b ∈ F, μ (A b) ≤ R * μ Y := by
  classical
  have e1 : ∑ b ∈ F, μ (A b) = ∫⁻ x, ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x ∂μ := by
    rw [lintegral_finset_sum _ fun b _ => measurable_one.indicator (hA b)]
    exact Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hA b)).symm
  have e2 : (R : ℝ≥0∞) * μ Y = ∫⁻ x, Y.indicator (fun _ => (R : ℝ≥0∞)) x ∂μ := (lintegral_indicator_const hY _).symm
  rw [e1, e2]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Y
  · rw [Set.indicator_of_mem hx]
    have : ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x = ((F.filter fun b => x ∈ A b).card : ℝ≥0∞) := by
      simp [Set.indicator_apply]
    rw [this]
    exact Nat.cast_le.2 (by
      convert hR x (F.filter fun b => x ∈ A b) (Finset.filter_subset _ _) fun b hb => (Finset.mem_filter.1 hb).2)
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun h => hx (hsub b hb h)) _).le

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mul' (a b : G ι N) (w : ι) : mt (a * b) w = mt a w * mt b w := rfl

/- English proof (translation)
Simplify using `only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]`. Both sides reduce to the same expression.
-/
theorem mt_nu_same (w0 : ι) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w0 = (c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rfl

/- English proof (translation)
Simplify using `only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]`. Both sides reduce to the same expression.
-/
theorem mt_nu_ne {w0 w : ι} (h : w ≠ w0) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w = 1 := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
  rfl

/- English proof (translation)
Establish `h1 : mt a⁻¹ w * mt a w = 1` using `by rw [← mt_mul', inv_mul_cancel]; rfl`. Use `haveI : Invertible (mt a w) := invertibleOfLeftInverse _ _ h1`. Rewrite using `[← Matrix.inv_eq_left_inv h1]`. Conclude with `blockTriangular_inv_of_blockTriangular h`.
-/
theorem mt_inv_upper {a : G ι N} {w : ι} (h : (mt a w).BlockTriangular id) : (mt a⁻¹ w).BlockTriangular id := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  haveI : Invertible (mt a w) := invertibleOfLeftInverse _ _ h1
  rw [← Matrix.inv_eq_left_inv h1]
  exact blockTriangular_inv_of_blockTriangular h

/- English proof (translation)
Establish `h1 : mt a⁻¹ w * mt a w = 1` using `by rw [← mt_mul', inv_mul_cancel]; rfl`. Rewrite using `[← Matrix.inv_eq_left_inv h1, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 h)]`. Conclude with `Unitary.star_mem h`.
-/
theorem mt_inv_unit {a : G ι N} {w : ι} (h : mt a w ∈ unitaryGroup (Fin N) ℂ) : mt a⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  rw [← Matrix.inv_eq_left_inv h1, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 h)]
  exact Unitary.star_mem h

/- English proof (translation)
Take `⟨w0⟩` from `‹Nonempty ι›`. Take `⟨R0, hR0⟩` from `tri (N := N) M`. Take `⟨R, hR⟩` from `fin_bdd (N := N) R0`. Take `⟨R1, hR1⟩` from `env (N := N) M T`. Use `⟨R * μ (Zb R1), ENNReal.mul_ne_top (ENNReal.natCast_ne_top R) (cpt_Z R1).measure_lt_top.ne, ?_⟩` and prove the remaining obligations.

Introduce `m s0 hs0 hc0 hm0`. Take `⟨F, hF, hcard⟩` from `count s0`. Establish `hs0' : ∑ i, (-s0 i) = 0` using `by rw [Finset.sum_neg_distrib, hs0, neg_zero]`. Establish `hXm : MeasurableSet (Xb P T m)` using `(cpt_X hPc T m).measurableSet`. Establish `hZm : MeasurableSet (Zb (ι` using `ι) (N := N) R1) := (cpt_Z R1).measurableSet`.

Establish `hclose : ∀ s s' : Fin N → ℝ, (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) → (∀ i, (m i : ℝ) ≤ s' i ∧ s' i ≤ m i + 1) → ∀ i, |s i - s' i| ≤ 1`. Introduce `s s' h h' i`. Use `h i` as an intermediate fact. Use `h' i` as an intermediate fact. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`.

Establish `key` using `sum_meas_le μ F (fun c => (fun x => (nu w0 c)⁻¹ * x) ⁻¹' Xb P T m) (fun c => measurable_const_mul _ hXm) (Y := (fun x => (dg (fun i => -s0 i) hs0' : G ι N) * x) ⁻¹' Zb R1) (measurable_const_mul _ hZm) ?_ R ?_`. Simplify using `only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul] at key`. Establish `h1 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m) ≤ R * μ (Zb R1)` using `(mul_le_mul' hcard le_rfl).trans key`. Establish `h2 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * ENNReal.ofReal (Real.exp (-2 * Phi s0)) = 1`. Rewrite using `[← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `c hc x ⟨p, hp, s, hs, -, hm, k, hk, hx⟩ w i j`. Establish `hx' : x = nu w0 c * p * dg s hs * k`. Establish `: x = nu w0 c * ((nu w0 c)⁻¹ * x)` using `by group`.

Rewrite using `[this]`. Simplify using `only at hx`. Rewrite using `[hx]`. Simplify using `only [mul_assoc]`. Rewrite using `[hx']`.

Establish `hn : (mt (nu w0 c) w).BlockTriangular id ∧ ∀ i j, i ≤ j → ‖mt (nu w0 c) w i j‖ ≤ 2 * Real.exp (s0 i - s0 j)`. Distinguish the cases in `hw : w = w0`. Substitute `hw` using the available equality. Rewrite using `[mt_nu_same]`. Conclude with `hF c hc`.

Rewrite using `[mt_nu_ne hw]`. Use `⟨blockTriangular_one, fun i j _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[one_apply_ne hij, norm_zero]`. Check the signs of the components of the expression. Conclude with `hR1 _ _ _ s0 s hc0 (hclose _ _ hm hm0) hn.1 hn.2 (hP hp w).1 (hP hp w).2 (hk w) i j`. Introduce `x S hS hx`. Use `hR S fun c hc c' hc' i j => ?_` and prove the remaining obligations.

Take `⟨p, hp, s, hs, -, hm, k, hk, e⟩` from `hx c hc`. Take `⟨p', hp', s', hs', -, hm', k', hk', e'⟩` from `hx c' hc'`. Simplify using `only at e e'`. Establish `hE : nu w0 (c⁻¹ * c') * p' * dg s' hs' = p * dg s hs * (k * k'⁻¹)`. Establish `a1 : p' * dg s' hs' = (nu w0 c')⁻¹ * x * k'⁻¹` using `by rw [e']; group`.

Rewrite using `[mul_assoc, a1, ← mul_assoc (p * dg s hs), ← e, map_mul, map_inv]`. Use `group`. Establish `hup : (mt (nu w0 (c⁻¹ * c')) w0).BlockTriangular id`. Rewrite using `[map_mul, map_inv, mt_mul']`. Use `(mt_inv_upper ?_).mul ?_` and prove the remaining obligations.

Rewrite using `[mt_nu_same]`. Conclude with `(hF c (hS hc)).1`. Rewrite using `[mt_nu_same]`. Conclude with `(hF c' (hS hc')).1`. Use `hR0 (mt (nu w0 (c⁻¹ * c')) w0) (mt p' w0) (mt p w0) (mt (k * k'⁻¹) w0) s' s (hclose _ _ hm' hm) hup (hP hp' w0).1 (hP hp w0).1 (hP hp' w0).2 (hP hp w0).2 (p' w0).2 (p w0).2 (by rw [mt_mul']; exact mul_mem (hk w0) (mt_inv_unit (hk' w0))) (congrArg (fun y => mt y w0) hE) i j` as an intermediate fact.

Rewrite `this` using `[mt_nu_same]`. Conclude with `this`.
-/
theorem pack [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)] (μ : Measure (G ι N))
    [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P) (M T : ℝ) (hP : P ⊆ PB M) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by
  classical
  obtain ⟨w0⟩ := ‹Nonempty ι›
  obtain ⟨R0, hR0⟩ := tri (N := N) M
  obtain ⟨R, hR⟩ := fin_bdd (N := N) R0
  obtain ⟨R1, hR1⟩ := env (N := N) M T
  refine ⟨R * μ (Zb R1), ENNReal.mul_ne_top (ENNReal.natCast_ne_top R) (cpt_Z R1).measure_lt_top.ne, ?_⟩
  intro m s0 hs0 hc0 hm0
  obtain ⟨F, hF, hcard⟩ := count s0
  have hs0' : ∑ i, (-s0 i) = 0 := by rw [Finset.sum_neg_distrib, hs0, neg_zero]
  have hXm : MeasurableSet (Xb P T m) := (cpt_X hPc T m).measurableSet
  have hZm : MeasurableSet (Zb (ι := ι) (N := N) R1) := (cpt_Z R1).measurableSet
  have hclose : ∀ s s' : Fin N → ℝ, (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) →
      (∀ i, (m i : ℝ) ≤ s' i ∧ s' i ≤ m i + 1) → ∀ i, |s i - s' i| ≤ 1 := by
    intro s s' h h' i
    have := h i; have := h' i
    rw [abs_le]; constructor <;> linarith
  have key := sum_meas_le μ F (fun c => (fun x => (nu w0 c)⁻¹ * x) ⁻¹' Xb P T m)
    (fun c => measurable_const_mul _ hXm)
    (Y := (fun x => (dg (fun i => -s0 i) hs0' : G ι N) * x) ⁻¹' Zb R1) (measurable_const_mul _ hZm) ?_ R ?_
  · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul] at key
    have h1 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m) ≤ R * μ (Zb R1) :=
      (mul_le_mul' hcard le_rfl).trans key
    have h2 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * ENNReal.ofReal (Real.exp (-2 * Phi s0)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc μ (Xb P T m) = (ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m)) *
          ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by rw [mul_right_comm, h2, one_mul]
      _ ≤ _ := mul_le_mul' h1 le_rfl
  · rintro c hc x ⟨p, hp, s, hs, -, hm, k, hk, hx⟩ w i j
    have hx' : x = nu w0 c * p * dg s hs * k := by
      have : x = nu w0 c * ((nu w0 c)⁻¹ * x) := by group
      rw [this]; dsimp only at hx; rw [hx]; simp only [mul_assoc]
    rw [hx']
    have hn : (mt (nu w0 c) w).BlockTriangular id ∧
        ∀ i j, i ≤ j → ‖mt (nu w0 c) w i j‖ ≤ 2 * Real.exp (s0 i - s0 j) := by
      by_cases hw : w = w0
      · subst hw; rw [mt_nu_same]; exact hF c hc
      · rw [mt_nu_ne hw]
        refine ⟨blockTriangular_one, fun i j _ => ?_⟩
        by_cases hij : i = j
        · subst hij; simp
        · rw [one_apply_ne hij, norm_zero]; positivity
    exact hR1 _ _ _ s0 s hc0 (hclose _ _ hm hm0) hn.1 hn.2 (hP hp w).1 (hP hp w).2 (hk w) i j
  · intro x S hS hx
    refine hR S fun c hc c' hc' i j => ?_
    obtain ⟨p, hp, s, hs, -, hm, k, hk, e⟩ := hx c hc
    obtain ⟨p', hp', s', hs', -, hm', k', hk', e'⟩ := hx c' hc'
    dsimp only at e e'
    have hE : nu w0 (c⁻¹ * c') * p' * dg s' hs' = p * dg s hs * (k * k'⁻¹) := by
      have a1 : p' * dg s' hs' = (nu w0 c')⁻¹ * x * k'⁻¹ := by rw [e']; group
      rw [mul_assoc, a1, ← mul_assoc (p * dg s hs), ← e, map_mul, map_inv]; group
    have hup : (mt (nu w0 (c⁻¹ * c')) w0).BlockTriangular id := by
      rw [map_mul, map_inv, mt_mul']
      refine (mt_inv_upper ?_).mul ?_
      · rw [mt_nu_same]; exact (hF c (hS hc)).1
      · rw [mt_nu_same]; exact (hF c' (hS hc')).1
    have := hR0 (mt (nu w0 (c⁻¹ * c')) w0) (mt p' w0) (mt p w0) (mt (k * k'⁻¹) w0) s' s (hclose _ _ hm' hm) hup
      (hP hp' w0).1 (hP hp w0).1 (hP hp' w0).2 (hP hp w0).2 (p' w0).2 (p w0).2
      (by rw [mt_mul']; exact mul_mem (hk w0) (mt_inv_unit (hk' w0))) (congrArg (fun y => mt y w0) hE) i j
    rw [mt_nu_same] at this
    exact this

end PositivityTheory.KB.TwSMInt2

end
