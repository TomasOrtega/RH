import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import ReciprocityTheory.Chebotarev.EulerSum
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.APart

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨d, hd, h⟩` from `I.isFractional`. Use `⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h b hb`. Conclude with `⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩`.
-/
theorem exists_den (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩
  obtain ⟨x, hx⟩ := h b hb
  exact ⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩

/- English proof (translation)
Take `⟨d, hd, hdI⟩` from `exists_den I`. Use `choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1`. Establish `hd' : (d : F) ≠ 0` using `by exact_mod_cast hd`. Establish `hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F)))`. Introduce `c c' h`.

Take `⟨u, hu⟩` from `Ideal.span_singleton_eq_span_singleton.1 h`. Establish `h2` using `congrArg (fun x : 𝓞 F => (x : F)) hu`. Move the coercions through the operations in `at h2`. Use `Quotient.out_equiv_out.1 ⟨u, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hd'` to reduce the goal to its premises.

Take the linear combination `((u : 𝓞 F) : F) * hg c - hg c' - h2`. Establish `hS` using `(ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj`. Establish `hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|`. Simplify using `[Algebra.norm_eq_zero_iff, hd']`. Use `(hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_` and prove the remaining obligations.

Establish `e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1`. Rewrite using `[Algebra.coe_norm_int, hg, map_mul]`. Establish `e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) = ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) e1` after adjusting the coercions. Establish `hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) = |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)|`.

Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel, Real.rpow_zero, one_mul]`.
-/
theorem summable_norm_rpow (I : FractionalIdeal (𝓞 F)⁰ F) {s : ℝ} (hs : 1 < s) :
    Summable (fun c : Quotient (unitRel I) => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| ^ (-s)) := by
  obtain ⟨d, hd, hdI⟩ := exists_den I
  choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F))) := by
    intro c c' h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := congrArg (fun x : 𝓞 F => (x : F)) hu
    push_cast at h2
    refine Quotient.out_equiv_out.1 ⟨u, ?_⟩
    apply mul_left_cancel₀ hd'
    linear_combination ((u : 𝓞 F) : F) * hg c - hg c' - h2
  have hS := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine (hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1 := by
    rw [Algebra.coe_norm_int, hg, map_mul]
  have e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) =
      |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply]
  rw [hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel,
    Real.rpow_zero, one_mul]

/- English proof (translation)
Rewrite using `[show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]`.
-/
theorem inv_natPow_rpow_neg_half_even_eq_pow {x : ℝ} (hx : 0 < x) (t : ℝ) : x ^ (-(2 + 2 * t)) = x⁻¹ ^ 2 * x ^ (-2 * t) := by
  rw [show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]

/- English proof (translation)
Break down `le_total x 1 with h | h` into its components or cases. Use `Real.rpow_le_rpow_of_exponent_ge hx h (show -2 * R ≤ -2 * t by linarith)` as an intermediate fact. Combine the linear relations using `[Real.rpow_nonneg hx.le (-2 * r)]`. Use `Real.rpow_le_rpow_of_exponent_le h (show -2 * t ≤ -2 * r by linarith)` as an intermediate fact. Combine the linear relations using `[Real.rpow_nonneg hx.le (-2 * R)]`.
-/
theorem rpow_le_add {x : ℝ} (hx : 0 < x) {r t R : ℝ} (hr : r ≤ t) (hR : t ≤ R) :
    x ^ (-2 * t) ≤ x ^ (-2 * r) + x ^ (-2 * R) := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -2 * R ≤ -2 * t by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * r)]
  · have := Real.rpow_le_rpow_of_exponent_le h (show -2 * t ≤ -2 * r by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * R)]

variable [IsTotallyReal F]

/- English proof (translation)
Simplify using `only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]`.
-/
theorem prod_latPt_zero (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
  simp only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]

end GlobalTheory.HeckeTwo.APart

open GlobalTheory.HeckeTwo.APart in

/- English proof (translation)
Introduce `F _ _ _ 𝔞`. Use `set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP`. Establish `hP0 : ∀ c, P c ≠ 0` using `fun c => by`. Simplify using `only [hP, prod_latPt_zero]`. Use `mul_ne_zero (pow_ne_zero _ ?_) ?_` and prove the remaining obligations.

Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Conclude with `mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero`. Conclude with `(Algebra.norm_ne_zero_iff).2 c.out.2.2` after adjusting the coercions. Use `set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK`. Establish `hK0 : 0 < K`.

Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Conclude with `norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))`. Establish `hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)|` using `fun c => by`. Simplify using `only [hP, prod_latPt_zero, norm_mul, hK]`. Use `congr 1`.

Rewrite using `[← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`. Establish `hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t)` using `fun t ht => ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by`. Rewrite using `[hnP, Real.mul_rpow hK0.le (abs_nonneg _)]`. Establish `hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re)` using `fun c σ => by show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _`. Rewrite using `[norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]`.

Simplify using the standard rewrite rules. Introduce `σ₀ hσ₀`. Establish `hσ₀' : -1 / 2 < σ₀.re` using `hσ₀`. Use `set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr`. Use `set R : ℝ := σ₀.re + 1 with hR`.

Use `set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef`. Establish `hU : IsOpen U` using `(isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)`. Establish `hmem : σ₀ ∈ U` using `⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩`. Establish `hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U`. Use `differentiableOn_tsum_of_summable_norm (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_` and prove the remaining obligations.

Use `((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr fun c => ?_` and prove the remaining obligations. Establish `hx` using `norm_pos_iff.2 (hP0 c)`. Rewrite using `[inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c σ _ show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ`.

Use `DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)` and prove the remaining obligations. Use `DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)` and prove the remaining obligations. Conclude with `(norm_pos_iff.2 (hP0 c)).ne'` after adjusting the coercions. Introduce `c σ hσ`. Rewrite using `[hnorm]`.

Establish `hx` using `norm_pos_iff.2 (hP0 c)`. Use `gcongr`. Conclude with `rpow_le_add hx hσ.1.le hσ.2.le`. Conclude with `(hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt`.
-/
theorem GlobalTheory.HeckeTwo.aPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ _ 𝔞
  set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP
  have hP0 : ∀ c, P c ≠ 0 := fun c => by
    simp only [hP, prod_latPt_zero]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
    · exact_mod_cast (Algebra.norm_ne_zero_iff).2 c.out.2.2
  set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK
  have hK0 : 0 < K := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))
  have hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := fun c => by
    simp only [hP, prod_latPt_zero, norm_mul, hK]
    congr 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t) := fun t ht =>
    ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by
      rw [hnP, Real.mul_rpow hK0.le (abs_nonneg _)]
  have hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re) := fun c σ => by
    show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _
    rw [norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]
    simp
  intro σ₀ hσ₀
  have hσ₀' : -1 / 2 < σ₀.re := hσ₀
  set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr
  set R : ℝ := σ₀.re + 1 with hR
  set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hmem : σ₀ ∈ U := ⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩
  have hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_
    · refine ((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr
        fun c => ?_
      have hx := norm_pos_iff.2 (hP0 c)
      rw [inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]
      ring
    · intro c σ _
      show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
      exact_mod_cast (norm_pos_iff.2 (hP0 c)).ne'
    · intro c σ hσ
      rw [hnorm]
      have hx := norm_pos_iff.2 (hP0 c)
      gcongr
      exact rpow_le_add hx hσ.1.le hσ.2.le
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
