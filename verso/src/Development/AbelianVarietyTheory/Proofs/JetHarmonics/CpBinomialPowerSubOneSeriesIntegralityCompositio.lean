import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulSeries

variable {q : ℕ} [Fact q.Prime]

def zcHom : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zc_eq (a : ℤ_[q]) : zc a = zcHom a := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.norm_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
  rw [DT, add_mul, one_mul, map_add, coeff_derivative]
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem coeff_one_add_mulS (a : ℤ_[q]) (n : ℕ) :
    coeff n (1 + mulS a : ℂ_[q]⟦X⟧) = zcHom (Ring.choose a n) := by
  cases n with
  | zero => simp [mulS]
  | succ n => simp [mulS, coeff_one, zc_eq]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem constantCoeff_mulS (a : ℤ_[q]) : constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 := by
  simp [mulS]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_mulS a)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem choose_step (c : ℤ_[q]) (n : ℕ) :
    Ring.choose c (n + 1) * (n + 1) + Ring.choose c n * n = c * Ring.choose c n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h0 : (n.factorial : ℤ_[q]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h1

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem DT_one_add_mulS (a : ℤ_[q]) :
    DT (1 + mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  ext n
  rw [coeff_DT, coeff_C_mul, coeff_one_add_mulS, coeff_one_add_mulS, zc_eq]
  have := congrArg zcHom (choose_step a n)
  simpa using this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem DT_mulS (a : ℤ_[q]) : DT (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  rw [← DT_one_add_mulS]; simp [DT]

/- English proof (translation)
By extensionality, compare the relevant components. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem ode_unique (c : ℂ_[q]) (h : ℂ_[q]⟦X⟧) {f g : ℂ_[q]⟦X⟧} (hf : DT f = C c * f + h)
    (hg : DT g = C c * g + h) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_DT, map_add, coeff_C_mul] at h1 h2
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [ih] at h1
    linear_combination h1 - h2

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem DT_logS : DT (logS : ℂ_[q]⟦X⟧) = 1 := by
  ext n
  rw [coeff_DT]
  cases n with
  | zero => simp [logS]
  | succ n =>
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h4 : ((n : ℂ_[q]) + 1 + 1) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    simp only [logS, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
    push_cast
    field_simp
    ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem DT_subst_mulS (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (f.subst (mulS a : ℂ_[q]⟦X⟧)) = C (zc a) * (DT f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  have hs := hasSubst_mulS a
  have h2 := DT_mulS a
  have h1 : (DT f).subst (mulS a : ℂ_[q]⟦X⟧) =
      (1 + mulS a) * (derivative ℂ_[q] f).subst (mulS a : ℂ_[q]⟦X⟧) := by
    rw [DT, ← coe_substAlgHom hs, map_mul, map_add, map_one, substAlgHom_X]
  rw [h1]
  unfold DT at h2 ⊢
  rw [derivative_subst hs]
  linear_combination ((derivative ℂ_[q] f).subst (mulS a : ℂ_[q]⟦X⟧)) * h2

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem constantCoeff_subst_mulS (a : ℤ_[q]) {f : ℂ_[q]⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (f.subst (mulS a : ℂ_[q]⟦X⟧)) = 0 := by
  have hs := hasSubst_mulS a
  obtain ⟨b, rfl⟩ : (X : ℂ_[q]⟦X⟧) ∣ f := X_dvd_iff.2 hf
  rw [← coe_substAlgHom hs, map_mul, substAlgHom_X, map_mul, constantCoeff_mulS, zero_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities.
-/
theorem logS_subst (a : ℤ_[q]) :
    (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS := by
  have hs := hasSubst_mulS a
  have h0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  refine ode_unique 0 (C (zc a)) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_logS, ← coe_substAlgHom hs]; simp
  · have := DT_logS (q := q)
    unfold DT at this ⊢
    rw [Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero, map_zero, zero_mul, zero_add]
    linear_combination (C (zc a)) * this
  · rw [constantCoeff_subst_mulS a h0, map_mul, h0, mul_zero]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.
-/
theorem mulS_subst (a b : ℤ_[q]) :
    (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b) := by
  have hs := hasSubst_mulS b
  have hz : zc (a * b) = zc a * zc b := by simp [zc_eq]
  refine ode_unique (zc (a * b)) (C (zc (a * b))) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_mulS, ← coe_substAlgHom hs, map_mul, map_add, map_one, hz, map_mul]
    have : (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧) (C (zc a)) = C (zc a) :=
      (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧).commutes (zc a)
    rw [this]
    ring
  · rw [DT_mulS]; ring
  · rw [constantCoeff_subst_mulS b (constantCoeff_mulS a), constantCoeff_mulS]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mulS_one : (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X := by
  refine ode_unique 1 1 ?_ ?_ ?_
  · rw [DT_mulS]; simp [zc_eq, add_comm]
  · simp [DT, add_comm]
  · simp [constantCoeff_mulS]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bd_mulS (a : ℤ_[q]) : Bd 1 (mulS a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [mulS, coeff_mk]
  split_ifs
  · simp
  · rw [norm_zc]; exact PadicInt.norm_le_one _

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bd_one_pow {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (d : ℕ) : Bd 1 (h ^ d) := by
  induction d with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ d ih =>
    intro n
    rw [pow_succ, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hh _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem bd_subst {f h : ℂ_[q]⟦X⟧} {A : ℝ} (hf : Bd A f) (hh : Bd 1 h) (h0 : constantCoeff h = 0) :
    Bd A (f.subst h) := by
  classical
  intro n
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' h0
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  rw [coeff_subst' hs, finsum_def]
  split_ifs
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hA fun d _ => ?_
    rw [smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (bd_one_pow hh d n)).trans (hf d)
  · simpa using hA

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem bd_subst_mulS_iff (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ) (ha : ‖a‖ = 1) :
    Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f := by
  refine ⟨fun h => ?_, fun h => bd_subst h (bd_mulS a) (constantCoeff_mulS a)⟩
  obtain ⟨b, hb⟩ := (PadicInt.isUnit_iff.2 ha).exists_right_inv
  have h1 := bd_subst h (bd_mulS b) (constantCoeff_mulS b)
  rwa [subst_comp_subst_apply (hasSubst_mulS a) (hasSubst_mulS b), mulS_subst, hb, mulS_one,
    X_subst] at h1

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem mulS_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) :=
  fun _ _ => ⟨fun a => ⟨bd_mulS a, constantCoeff_mulS a, by simp [mulS], logS_subst a⟩, mulS_subst,
    mulS_one, bd_subst_mulS_iff, DT_logS, norm_zc⟩

end GlobalTheory.MomOne.MulSeries
