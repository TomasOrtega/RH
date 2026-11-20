import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoConst

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * (N : FractionalIdeal (𝓞 F)⁰ F) ≤ 1`. Rewrite using `[← hM]`. Conclude with `mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 a.2.1) _`. Take `⟨I, hI⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle`. Establish `hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.2 a.2.2`.

Establish `hI0 : I ≠ 0`. Introduce and unpack `rfl`. Conclude with `mul_ne_zero hs N.ne_zero (by rw [← hI]; simp)`. Use `⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, hI⟩` and prove the remaining obligations. Establish `e : FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ = Units.mk0 _ hs * N` using `by ext1`.

Rewrite using `[FractionalIdeal.coe_mk0]`. Conclude with `hI`. Rewrite using `[← ClassGroup.mk_mk0 F, e, map_mul, ClassGroup.mk_eq_one_iff.2, one_mul]`. Rewrite using `[FractionalIdeal.isPrincipal_iff]`. Conclude with `⟨a.1, rfl⟩`.
-/
theorem exists_ideal (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1)
    (a : NZ M) : ∃ J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N},
      ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * N := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * (N : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
    rw [← hM]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 a.2.1) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 a.2.2
  have hI0 : I ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hs N.ne_zero (by rw [← hI]; simp)
  refine ⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, hI⟩
  have e : FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ = Units.mk0 _ hs * N := by
    ext1
    rw [FractionalIdeal.coe_mk0]
    exact hI
  rw [← ClassGroup.mk_mk0 F, e, map_mul, ClassGroup.mk_eq_one_iff.2, one_mul]
  rw [FractionalIdeal.isPrincipal_iff]
  exact ⟨a.1, rfl⟩

/- English proof (translation)
Use `choose f hf using exists_ideal M N hM`. Establish `key : ∀ a b : NZ M, (unitRel M).r a b ↔ FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1`. Introduce `a b`. Rewrite using `[FractionalIdeal.spanSingleton_eq_spanSingleton]`. Use `exists_congr fun ε => ?_` and prove the remaining obligations.

Rewrite using `[Units.smul_def, Algebra.smul_def]`. Conclude with `eq_comm`. Use `⟨Equiv.ofBijective (fun c => f c.out) ⟨?_, ?_⟩, fun c => hf _⟩` and prove the remaining obligations. Introduce `c c' h`. Establish `h1` using `hf c.out`.

Simplify using `only at h`. Rewrite `h1` using `[h, hf]`. Establish `h2` using `(key _ _).2 (mul_right_cancel₀ N.ne_zero h1).symm`. Rewrite using `[← c.out_eq, ← c'.out_eq]`. Conclude with `Quotient.sound h2`.

Introduce and unpack `⟨J, hJ⟩`. Establish `h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * N⁻¹) = 1`. Rewrite using `[map_mul, map_inv, ClassGroup.mk_mk0, hJ, mul_inv_cancel]`. Rewrite `h1` using `[ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]`. Take `⟨a, ha⟩` from `h1`.

Establish `ha0 : a ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.1 (ha ▸ Units.ne_zero _)`. Establish `hMN : M = ((N⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)`. Rewrite using `[Units.val_inv_eq_inv_val]`. Conclude with `eq_inv_of_mul_eq_one_left hM`. Rewrite `ha` using `[Units.val_mul, FractionalIdeal.coe_mk0, ← hMN]`.

Establish `haM : a ∈ M`. Rewrite using `[← FractionalIdeal.spanSingleton_le_iff_mem, ← ha]`. Use `conv_rhs => rw [← one_mul M]`. Conclude with `mul_le_mul_left FractionalIdeal.coeIdeal_le_one _`. Use `⟨Quotient.mk _ ⟨a, haM, ha0⟩, ?_⟩` and prove the remaining obligations.

Establish `h2 : (unitRel M).r (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out ⟨a, haM, ha0⟩` using `Quotient.exact (Quotient.out_eq _)`. Establish `h3` using `hf (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out`. Rewrite `h3` using `[(key _ _).1 h2]`. Simplify using `only at h3`. Rewrite `h3` using `[← ha, mul_assoc, hM, mul_one]`.

Conclude with `Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_injective h3))`.
-/
theorem exists_equiv (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1) :
    ∃ e : Quotient (unitRel M) ≃ {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N}, ∀ c,
      (((e c).1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c.out.1 * N := by
  choose f hf using exists_ideal M N hM
  have key : ∀ a b : NZ M, (unitRel M).r a b ↔
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 := by
    intro a b
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine exists_congr fun ε => ?_
    rw [Units.smul_def, Algebra.smul_def]
    exact eq_comm
  refine ⟨Equiv.ofBijective (fun c => f c.out) ⟨?_, ?_⟩, fun c => hf _⟩
  · intro c c' h
    have h1 := hf c.out
    simp only at h
    rw [h, hf] at h1
    have h2 := (key _ _).2 (mul_right_cancel₀ N.ne_zero h1).symm
    rw [← c.out_eq, ← c'.out_eq]
    exact Quotient.sound h2
  · rintro ⟨J, hJ⟩
    have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * N⁻¹) = 1 := by
      rw [map_mul, map_inv, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
    obtain ⟨a, ha⟩ := h1
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.1 (ha ▸ Units.ne_zero _)
    have hMN : M = ((N⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hM
    rw [Units.val_mul, FractionalIdeal.coe_mk0, ← hMN] at ha
    have haM : a ∈ M := by
      rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ha]
      conv_rhs => rw [← one_mul M]
      exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
    refine ⟨Quotient.mk _ ⟨a, haM, ha0⟩, ?_⟩
    have h2 : (unitRel M).r (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out ⟨a, haM, ha0⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have h3 := hf (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out
    rw [(key _ _).1 h2] at h3
    simp only at h3
    rw [← ha, mul_assoc, hM, mul_one] at h3
    exact Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_injective h3))

/- English proof (translation)
Establish `h` using `prod_emb (F := F) (algebraMap ℚ F 2)`. Rewrite `h` using `[Algebra.norm_algebraMap]`. Simplify using `only [map_ofNat, Finset.prod_const, Finset.card_univ] at h`. Establish `h' : (2 : ℕ) ^ Fintype.card (Emb F) = 2 ^ Module.finrank ℚ F` using `by exact_mod_cast h`. Conclude with `Nat.pow_right_injective le_rfl h'`.
-/
theorem card_emb [IsTotallyReal F] : Fintype.card (Emb F) = Module.finrank ℚ F := by
  have h := prod_emb (F := F) (algebraMap ℚ F 2)
  rw [Algebra.norm_algebraMap] at h
  simp only [map_ofNat, Finset.prod_const, Finset.card_univ] at h
  have h' : (2 : ℕ) ^ Fintype.card (Emb F) = 2 ^ Module.finrank ℚ F := by exact_mod_cast h
  exact Nat.pow_right_injective le_rfl h'

/- English proof (translation)
Establish `h1 : ∏ τ, latPt (0 : Emb F → ℂ) (a, 0) τ = (2 * (Real.pi : ℂ) * I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ)`. Rewrite using `[← prod_emb, ← card_emb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[latPt]`. Establish `h2 : (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 = ((Algebra.norm ℚ a : ℚ) : ℂ)⁻¹ ^ 2`.

Rewrite using `[inv_pow, inv_pow, ← Rat.cast_pow, sq_abs, Rat.cast_pow]`. Unfold `eisTerm`. Rewrite using `[h1, h2, mul_zero, cpow_zero, mul_one, mul_inv, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Module.finrank ℚ F)]`.
-/
theorem eisTerm_zero [IsTotallyReal F] (a : F) :
    eisTerm 2 0 0 (a, 0) = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F *
      (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 := by
  have h1 : ∏ τ, latPt (0 : Emb F → ℂ) (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← card_emb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  have h2 : (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 = ((Algebra.norm ℚ a : ℚ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← Rat.cast_pow, sq_abs, Rat.cast_pow]
  unfold eisTerm
  rw [h1, h2, mul_zero, cpow_zero, mul_one, mul_inv, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Module.finrank ℚ F)]

/- English proof (translation)
Use `set N : Frac F := FractionalIdeal.mk0 F D * 𝔞 with hN`. Establish `hCN : C = ClassGroup.mk F N`. Rewrite using `[hN, map_mul, ClassGroup.mk_mk0, ← hC, inv_mul_cancel_right]`. Establish `hM : latM 𝔞 * (N : FractionalIdeal (𝓞 F)⁰ F) = 1`. Use `(FractionalIdeal.mk0 F D).ne_zero` as an intermediate fact.

Rewrite `this` using `[FractionalIdeal.coe_mk0]`. Rewrite using `[latM, hN, ← hD, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val, ← mul_inv, inv_mul_cancel₀ (mul_ne_zero this 𝔞.ne_zero)]`. Establish `hnN : ((FractionalIdeal.absNorm (N : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℂ) = (dF F : ℂ) * (nrm 𝔞 : ℂ)`. Rewrite using `[hN, Units.val_mul, FractionalIdeal.coe_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm, hD, absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, dF, nrm, ← Int.cast_abs, Rat.cast_mul, Rat.cast_intCast, ofReal_intCast, ofReal_ratCast]`. Establish `hn0 : (dF F : ℂ) * (nrm 𝔞 : ℂ) ≠ 0`.

Rewrite using `[← hnN]`. Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.2 N.ne_zero)` after adjusting the coercions. Substitute `hCN` using the available equality. Take `⟨e, he⟩` from `exists_equiv _ N hM`. Establish `hs` using `(e.hasSum_iff.2 (hZ.2 2 (by norm_num))).mul_left (((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2)`.

Rewrite using `[← hs.tsum_eq, aPart]`. Use `tsum_congr fun c => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun I => ((FractionalIdeal.absNorm I : ℚ) : ℂ)) (he c)`. Simplify using `only [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, hnN, Rat.cast_natCast] at h1`. Rewrite using `[eisTerm_zero, Function.comp_apply, h1, cpow_neg, cpow_two]`.

Generalize the expression as in `(dF F : ℂ) * (nrm 𝔞 : ℂ) = x at hn0 ⊢`. Generalize the expression as in `((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F = y`. Rewrite using `[mul_pow, mul_inv, inv_pow, mul_assoc, mul_left_comm (x ^ 2), mul_inv_cancel₀ (pow_ne_zero 2 hn0), mul_one]`.
-/
theorem aPart_zero [IsTotallyReal F] (𝔞 : Frac F) (C : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰) (Za : ℂ → ℂ)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D)
    (hZ : IsPartialZeta C Za) :
    aPart 𝔞 0 = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2 * Za 2 := by
  set N : Frac F := FractionalIdeal.mk0 F D * 𝔞 with hN
  have hCN : C = ClassGroup.mk F N := by
    rw [hN, map_mul, ClassGroup.mk_mk0, ← hC, inv_mul_cancel_right]
  have hM : latM 𝔞 * (N : FractionalIdeal (𝓞 F)⁰ F) = 1 := by
    have := (FractionalIdeal.mk0 F D).ne_zero
    rw [FractionalIdeal.coe_mk0] at this
    rw [latM, hN, ← hD, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val, ← mul_inv,
      inv_mul_cancel₀ (mul_ne_zero this 𝔞.ne_zero)]
  have hnN : ((FractionalIdeal.absNorm (N : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℂ) = (dF F : ℂ) * (nrm 𝔞 : ℂ) := by
    rw [hN, Units.val_mul, FractionalIdeal.coe_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm, hD,
      absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, dF, nrm, ← Int.cast_abs,
      Rat.cast_mul, Rat.cast_intCast, ofReal_intCast, ofReal_ratCast]
  have hn0 : (dF F : ℂ) * (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [← hnN]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 N.ne_zero)
  subst hCN
  obtain ⟨e, he⟩ := exists_equiv _ N hM
  have hs := (e.hasSum_iff.2 (hZ.2 2 (by norm_num))).mul_left
    (((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2)
  rw [← hs.tsum_eq, aPart]
  refine tsum_congr fun c => ?_
  have h1 := congrArg (fun I => ((FractionalIdeal.absNorm I : ℚ) : ℂ)) (he c)
  simp only [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, hnN,
    Rat.cast_natCast] at h1
  rw [eisTerm_zero, Function.comp_apply, h1, cpow_neg, cpow_two]
  generalize (dF F : ℂ) * (nrm 𝔞 : ℂ) = x at hn0 ⊢
  generalize ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F = y
  rw [mul_pow, mul_inv, inv_pow, mul_assoc, mul_left_comm (x ^ 2), mul_inv_cancel₀ (pow_ne_zero 2 hn0), mul_one]

/- English proof (translation)
Rewrite using `[Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.Gamma_one, cpow_neg_one, mul_one]`.
-/
theorem gammaR_two : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.Gamma_one, cpow_neg_one,
    mul_one]

/- English proof (translation)
Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h` using `Gammaℝ_add_two (s := -1) (by norm_num)`. Rewrite `h` using `[show (-1 : ℂ) + 2 = 1 by norm_num, Gammaℝ_one]`. Clear denominators, using `at h` for the nonvanishing conditions. Take the linear combination `h`.
-/
theorem gammaR_neg_one : Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Gammaℝ_add_two (s := -1) (by norm_num)
  rw [show (-1 : ℂ) + 2 = 1 by norm_num, Gammaℝ_one] at h
  field_simp at h
  linear_combination h

/- English proof (translation)
Introduce `F _ _ _ 𝔞 C D Za Za' hD hC hZ _ hfe`. Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hfe2` using `hfe 2 (fun n h => by`. Establish `h' : (2 : ℤ) = -2 * n` using `by exact_mod_cast h`. Use the proof step `omega) (fun n h => by`.

Establish `h' : (1 - 2 : ℤ) = -2 * n` using `by exact_mod_cast h`. Use the proof step `omega)`. Establish `hd : 0 < dF F` using `abs_pos.2 (by exact_mod_cast discr_ne_zero F)`. Establish `hn : (nrm 𝔞 : ℂ) ≠ 0`. Rewrite using `[nrm]`.

Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.2 𝔞.ne_zero)` after adjusting the coercions. Use `set r : ℝ := dF F ^ ((1 : ℝ) / 2) with hr`. Establish `hr0 : (r : ℂ) ≠ 0` using `by exact_mod_cast (Real.rpow_pos_of_pos hd _).ne'`. Establish `hrr : (dF F : ℂ) = (r : ℂ) ^ 2`. Establish `: dF F = r ^ 2`.

Rewrite using `[hr, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]`. Evaluate the numerical expressions. Conclude with `this` after adjusting the coercions. Establish `hc : cK F 2 = r`. Rewrite using `[cK, hr]`.

Evaluate the numerical expressions. Establish `hneg : (dF F : ℂ) ^ ((-1 : ℂ) / 2) = (r : ℂ)⁻¹`. Rewrite using `[hr, ofReal_cpow hd.le, ← cpow_neg]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hfe2` using `[show (1 : ℂ) - 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, cpow_one, hneg, gammaR_two, gammaR_neg_one]`. Rewrite using `[show (1 : ℂ) - ((2 : ℕ) : ℂ) = -1 by norm_num, aPart_zero 𝔞 C D Za hD hC hZ, hc, omegaFactor, ← hr]`. Establish `hI : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 = 2⁻¹ * (Real.pi : ℂ)⁻¹ * (-2 * (Real.pi : ℂ))⁻¹`. Rewrite using `[inv_pow, mul_pow, I_sq]`.

Clear the denominators using the available nonvanishing facts. Establish `hg : (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F ≠ 0` using `pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)`. Rewrite using `[hI, mul_pow, mul_pow, inv_pow (-2 * (Real.pi : ℂ)), hrr]`. Rewrite `hfe2` using `[hrr]`. Generalize the expression as in `(-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F = g at hg hfe2`.

Generalize the expression as in `((Real.pi : ℂ)⁻¹) ^ Module.finrank ℚ F = p at hfe2`. Generalize the expression as in `((2 : ℂ)⁻¹) ^ Module.finrank ℚ F = t`. Use `push_cast`. Clear denominators, using `at hfe2 ⊢` for the nonvanishing conditions. Take the linear combination `t * hfe2`.
-/
theorem constant_term : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 C D Za Za' hD hC hZ _ hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfe2 := hfe 2 (fun n h => by
      have h' : (2 : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - 2 : ℤ) = -2 * n := by exact_mod_cast h
      omega)
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [nrm]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 𝔞.ne_zero)
  set r : ℝ := dF F ^ ((1 : ℝ) / 2) with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hd _).ne'
  have hrr : (dF F : ℂ) = (r : ℂ) ^ 2 := by
    have : dF F = r ^ 2 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
    exact_mod_cast this
  have hc : cK F 2 = r := by
    rw [cK, hr]; norm_num
  have hneg : (dF F : ℂ) ^ ((-1 : ℂ) / 2) = (r : ℂ)⁻¹ := by
    rw [hr, ofReal_cpow hd.le, ← cpow_neg]
    congr 1
    push_cast; ring
  rw [show (1 : ℂ) - 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, cpow_one, hneg, gammaR_two,
    gammaR_neg_one] at hfe2
  rw [show (1 : ℂ) - ((2 : ℕ) : ℂ) = -1 by norm_num, aPart_zero 𝔞 C D Za hD hC hZ, hc, omegaFactor, ← hr]
  have hI : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 = 2⁻¹ * (Real.pi : ℂ)⁻¹ * (-2 * (Real.pi : ℂ))⁻¹ := by
    rw [inv_pow, mul_pow, I_sq]; field_simp
  have hg : (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)
  rw [hI, mul_pow, mul_pow, inv_pow (-2 * (Real.pi : ℂ)), hrr]
  rw [hrr] at hfe2
  generalize (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F = g at hg hfe2
  generalize ((Real.pi : ℂ)⁻¹) ^ Module.finrank ℚ F = p at hfe2
  generalize ((2 : ℂ)⁻¹) ^ Module.finrank ℚ F = t
  push_cast
  field_simp at hfe2 ⊢
  linear_combination t * hfe2

end GlobalTheory.HeckeTwoConst
