import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCuspStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLowStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `k e L N ε h b s hk he hs hL hNL hh hb hsum`. Take `⟨-, hch⟩` from `GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1`. Take `⟨-, hcb⟩` from `GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb`. Take `⟨C, hC⟩` from `hh.2`. Take `⟨C', δ, hδ, hdec⟩` from `GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh`.

Take `⟨M, hM⟩` from `GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb`. Establish `fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ))`. Use `((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)` and prove the remaining obligations. Conclude with `UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')`. Establish `hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s)`.

Introduce `τ`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]`. Establish `hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im}`. Use extensionality with `τ`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `lt_or_ge τ.im 1 with h' | h'` into its components or cases. Conclude with `Or.inl ⟨h, h'⟩`. Conclude with `Or.inr ⟨h, h'⟩`.

Apply the tactic sequence `rintro (h | h) <;> exact h.1`. Establish `hmre : Measurable (fun τ : ℍ => τ.re)` using `UpperHalfPlane.continuous_re.measurable`. Establish `hmim : Measurable (fun τ : ℍ => τ.im)` using `UpperHalfPlane.continuous_im.measurable`. Establish `hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}` using `((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter (measurableSet_le measurable_const hmim)`. Rewrite using `[hsplit]`.

Use `IntegrableOn.union ?_ ?_` and prove the remaining obligations. Establish `hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1}` using `(((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2`. Use `hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations. Rewrite using `[hnorm]`. Establish `hy` using `τ.im_pos`.

Use `set A := ‖qs h τ‖`. Use `set B := ‖qs b τ‖`. Use `set y := τ.im`. Establish `e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1)`. Rewrite using `[← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s)`. Rewrite using `[← Real.rpow_add hy]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s)`. Rewrite using `[← Real.rpow_add hy]`. Use `congr 1`. Rewrite using `[hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `amgm` using `two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))`. Establish `hCb : A ^ 2 * y ^ k ≤ C` using `hC τ`. Establish `hp : 0 ≤ y ^ (s + 1)` using `(Real.rpow_pos_of_pos hy _).le`.

Establish `: A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1)`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hCb hp`. Establish `h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s))` using `by rw [← e3]; ring`. Establish `h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1))` using `by rw [← e1]; ring`.

Establish `h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s)` using `by rw [← e2]; ring`. Rewrite `amgm` using `[h1, h2, h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `(GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)`. Use `hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))` and prove the remaining obligations.

Rewrite using `[hnorm]`. Establish `hy` using `τ.im_pos`. Establish `hy1 : 1 ≤ τ.im` using `hτ.2`. Establish `hd` using `hdec τ (by linarith)`. Rewrite `hd` using `[one_smul]`.

Establish `hB` using `hM τ hy1`. Use `set A := ‖qs h τ‖`. Use `set B := ‖qs b τ‖`. Use `set y := τ.im`. Establish `hA0 : 0 ≤ A` using `norm_nonneg _`.

Establish `hB0 : 0 ≤ B` using `norm_nonneg _`. Establish `hyk : 0 ≤ y ^ ((k : ℝ) / 2)` using `(Real.rpow_pos_of_pos hy _).le`. Establish `hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k`. Rewrite using `[mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y)`. Use `Real.sqrt_le_sqrt hd` as an intermediate fact. Rewrite `this` using `[← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s)`.

Rewrite using `[← Real.rpow_add hy]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : 0 ≤ y ^ ((k : ℝ) / 2 + s)` using `(Real.rpow_pos_of_pos hy _).le`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr` and prove the remaining obligations. Use `_ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring`.
-/
theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
