import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

noncomputable section

namespace GlobalTheory.HostModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def trForm (H : Host E) : LinearMap.BilinForm ℤ (𝓞 E) :=
  ((LinearMap.mul ℤ (𝓞 E)).compr₂ (Algebra.trace ℤ (𝓞 E))) ∘ₗ H.bar.toAddEquiv.toIntLinearEquiv.toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trForm_apply (H : Host E) (x y : 𝓞 E) : trForm H x y = Algebra.trace ℤ (𝓞 E) (H.bar x * y) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trace_bar (H : Host E) (a : 𝓞 E) : Algebra.trace ℤ (𝓞 E) (H.bar a) = Algebra.trace ℤ (𝓞 E) a := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_trace_int, Algebra.coe_trace_int, H.bar_eq]
  exact Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (a : E)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trForm_apply' (H : Host E) (x y : 𝓞 E) : trForm H x y = Algebra.trace ℤ (𝓞 E) (x * H.bar y) := by
  rw [trForm_apply, ← trace_bar H, map_mul, bar_bar]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trForm_symm (H : Host E) (x y : 𝓞 E) : trForm H x y = trForm H y x := by
  rw [trForm_apply', trForm_apply, mul_comm]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem trForm_isSymm (H : Host E) : (trForm H).IsSymm := ⟨trForm_symm H⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trForm_adj (H : Host E) (a y z : 𝓞 E) : trForm H (a • y) z = trForm H y (H.bar a • z) := by
  rw [trForm_apply, trForm_apply, smul_eq_mul, smul_eq_mul, map_mul H.bar, mul_comm (H.bar a) (H.bar y), mul_assoc]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trForm_mul_left (H : Host E) (a y z : 𝓞 E) : trForm H (a * y) z = trForm H y (H.bar a * z) :=
  trForm_adj H a y z

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trForm_adj_star (H : Host E) (a y z : 𝓞 E) :
    letI := H.starRing; trForm H (a • y) z = trForm H y (star a • z) :=
  trForm_adj H a y z

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trForm_bar_bar (H : Host E) (x y : 𝓞 E) : trForm H (H.bar x) (H.bar y) = trForm H x y := by
  rw [trForm_apply, trForm_apply', bar_bar]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem embedding_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) : τ (H.bar a : 𝓞 E) = conj (τ a) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

omit [IsCMField E] in

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coe_trace_eq_sum (a : 𝓞 E) : (Algebra.trace ℤ (𝓞 E) a : ℂ) = ∑ τ : E →+* ℂ, τ a := by
  have h : (Algebra.trace ℤ (𝓞 E) a : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E (a : E)) := by
    rw [← Algebra.coe_trace_int]; simp
  rw [h, trace_eq_sum_embeddings ℂ]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem trForm_eq_sum (H : Host E) (x y : 𝓞 E) : (trForm H x y : ℂ) = ∑ τ : E →+* ℂ, conj (τ x) * τ y := by
  rw [trForm_apply, coe_trace_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← embedding_bar H, ← map_mul]; rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trForm_self_eq_sum (H : Host E) (y : 𝓞 E) : (trForm H y y : ℝ) = ∑ τ : E →+* ℂ, ‖τ y‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  rw [trForm_eq_sum]
  exact Finset.sum_congr rfl fun τ _ => Complex.conj_mul' _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem trForm_pos (H : Host E) {y : 𝓞 E} (hy : y ≠ 0) : 0 < trForm H y y := by
  have h : (0 : ℝ) < (trForm H y y : ℝ) := by
    rw [trForm_self_eq_sum]
    refine Finset.sum_pos (fun τ _ => pow_pos (norm_pos_iff.2 ?_) 2) Finset.univ_nonempty
    exact (map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hy)
  exact_mod_cast h

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem trForm_nonneg (H : Host E) (y : 𝓞 E) : 0 ≤ trForm H y y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact (trForm_pos H hy).le

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem trForm_nondegenerate (H : Host E) : (trForm H).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> by_contra h <;> exact (trForm_pos H h).ne' (hx x)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trForm_injective (H : Host E) : Function.Injective (trForm H) :=
  LinearMap.ker_eq_bot.1 (trForm_nondegenerate H).ker_eq_bot

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem trForm_one_one (H : Host E) : trForm H 1 1 = Module.finrank ℚ E := by
  apply Int.cast_injective (α := ℝ)
  rw [trForm_self_eq_sum]
  simp [Embeddings.card]

def realEmb (τ : E →+* ℂ) : ℝ ⊗[ℤ] 𝓞 E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) (τ.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    fun _ _ => Commute.all _ _

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem realEmb_tmul (τ : E →+* ℂ) (r : ℝ) (a : 𝓞 E) : realEmb τ (r ⊗ₜ a) = r * τ a := rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trForm_baseChange_eq_sum (H : Host E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    ((trForm H).baseChange ℝ v w : ℂ) = ∑ τ : E →+* ℂ, conj (realEmb τ v) * realEmb τ w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' h h' => simp [h, h', add_mul, Finset.sum_add_distrib]
  | tmul r x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' h h' => rw [map_add, Complex.ofReal_add, h, h']; simp [mul_add, Finset.sum_add_distrib]
    | tmul s y =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
      push_cast
      rw [trForm_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [realEmb_tmul, map_mul, Complex.conj_ofReal]
      ring

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trForm_baseChange_self_eq_sum (H : Host E) (v : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ v v = ∑ τ : E →+* ℂ, ‖realEmb τ v‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  rw [trForm_baseChange_eq_sum]
  exact Finset.sum_congr rfl fun τ _ => Complex.conj_mul' _

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trForm_baseChange_symm (H : Host E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ v w = (trForm H).baseChange ℝ w v := by
  apply Complex.ofReal_injective
  rw [← Complex.conj_ofReal ((trForm H).baseChange ℝ w v), trForm_baseChange_eq_sum, trForm_baseChange_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun τ _ => by rw [map_mul, Complex.conj_conj, mul_comm]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trForm_baseChange_adj (H : Host E) (a : 𝓞 E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ ((1 ⊗ₜ a) * v) w = (trForm H).baseChange ℝ v ((1 ⊗ₜ H.bar a) * w) := by
  apply Complex.ofReal_injective
  rw [trForm_baseChange_eq_sum, trForm_baseChange_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_mul, realEmb_tmul, embedding_bar, Complex.ofReal_one, one_mul]
  ring

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem trForm_baseChange_nondegenerate (H : Host E) : ((trForm H).baseChange ℝ).Nondegenerate := by
  classical
  let b := RingOfIntegers.basis E
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 (trForm_nondegenerate H)
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℝ)]
  have e : LinearMap.BilinForm.toMatrix (b.baseChange ℝ) ((trForm H).baseChange ℝ) =
      (Int.castRingHom ℝ).mapMatrix (LinearMap.BilinForm.toMatrix b (trForm H)) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [e, ← RingHom.map_det]
  simpa using h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem trForm_baseChange_pos (H : Host E) {v : ℝ ⊗[ℤ] 𝓞 E} (hv : v ≠ 0) :
    0 < (trForm H).baseChange ℝ v v := by
  rw [trForm_baseChange_self_eq_sum]
  refine (Finset.sum_nonneg fun τ _ => sq_nonneg _).lt_of_ne fun h => hv ?_
  have h0 : ∀ τ : E →+* ℂ, realEmb τ v = 0 := fun τ => by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => sq_nonneg _).1 h.symm τ (Finset.mem_univ τ)
  refine (trForm_baseChange_nondegenerate H).1 v fun w => Complex.ofReal_injective ?_
  rw [trForm_baseChange_eq_sum]
  simp [h0]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trForm_baseChange_nonneg (H : Host E) (v : ℝ ⊗[ℤ] 𝓞 E) : 0 ≤ (trForm H).baseChange ℝ v v := by
  rw [trForm_baseChange_self_eq_sum]
  exact Finset.sum_nonneg fun τ _ => sq_nonneg _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.
-/
theorem trForm_rt_rt (H : Host E) : trForm H H.rt H.rt = H.d * Module.finrank ℚ E := by
  have h : H.bar H.rt * H.rt = (H.d : ℤ) • (H.bar 1 * 1) := by
    rw [bar_rt, map_one]
    simp only [mul_one, zsmul_eq_mul, Int.cast_natCast]
    linear_combination -H.rt_sq
  rw [trForm_apply, h, map_smul, ← trForm_apply, trForm_one_one, smul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem trForm_one_rt (H : Host E) : trForm H 1 H.rt = 0 := by
  have h := trForm_bar_bar H 1 H.rt
  rw [map_one, bar_rt, map_neg] at h
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
example : trForm host 1 1 = 12 := by
  rw [trForm_one_one, finrank_rat_E21_eq_twelve]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
example : trForm host host.rt host.rt = 84 := by
  rw [trForm_rt_rt, finrank_rat_E21_eq_twelve, host_d]; rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
example : Algebra.trace ℤ (𝓞 E21) (host.rt * host.rt) = -84 := by
  have h := trForm_rt_rt host
  rw [trForm_apply, bar_rt, neg_mul, map_neg, finrank_rat_E21_eq_twelve, host_d] at h
  omega

end GlobalTheory.HostModel

end
