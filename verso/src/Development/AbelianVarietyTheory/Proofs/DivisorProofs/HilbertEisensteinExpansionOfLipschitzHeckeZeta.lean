import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinNonconstantTermsHasSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaRealFunctionalEquationConstantEvenIntegerStatement

noncomputable section

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.LatVal GlobalTheory.LatJet
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertEis

/- English proof (translation)
Take `⟨G, hG, -, -⟩` from `hH F hf 𝔞 𝔟`. Establish `hre : 0 < ((s : ℂ) - 1).re`. Simplify using `only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]`. Conclude with `(by omega : 1 < s)` after adjusting the coercions. Establish `h1` using `(hG.1 ((s : ℂ) - 1) hre z hz).1`.

Establish `h2 : Summable fun c => ‖eisClass 𝔞 𝔟 2 ((s : ℂ) - 1) z c‖` using `summable_norm_iff.mpr h1`. Use `Summable.of_norm (h2.congr fun c => ?_)` and prove the remaining obligations. Establish `hP : ∏ τ, latPt z c.out.1 τ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero hz c.out.2.2.2 τ`. Establish `hn : 0 < ‖∏ τ, latPt z c.out.1 τ‖` using `norm_pos_iff.2 hP`. Establish `hr : (-2 * ((s : ℂ) - 1)).re = -((2 * (s - 1) : ℕ) : ℝ)`.

Rewrite using `[Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]`. Simplify using the standard rewrite rules. Simplify using `only [eisClass, eisTerm, norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hn, hr, mul_zero, Complex.zero_re, Real.rpow_zero, mul_one, Real.rpow_neg hn.le, Real.rpow_natCast, ← inv_pow, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem eisClass_summable_of_hecke (hH : HeckeWeightTwo) {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (hf : 2 ≤ Module.finrank ℚ F) (𝔞 𝔟 : Frac F) {s : ℕ} (hs : 2 ≤ s) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) :
    Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := by
  obtain ⟨G, hG, -, -⟩ := hH F hf 𝔞 𝔟
  have hre : 0 < ((s : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]
    exact_mod_cast (by omega : 1 < s)
  have h1 := (hG.1 ((s : ℂ) - 1) hre z hz).1
  have h2 : Summable fun c => ‖eisClass 𝔞 𝔟 2 ((s : ℂ) - 1) z c‖ := summable_norm_iff.mpr h1
  refine Summable.of_norm (h2.congr fun c => ?_)
  have hP : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero hz c.out.2.2.2 τ
  have hn : 0 < ‖∏ τ, latPt z c.out.1 τ‖ := norm_pos_iff.2 hP
  have hr : (-2 * ((s : ℂ) - 1)).re = -((2 * (s - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]
    simp
  simp only [eisClass, eisTerm, norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hn, hr,
    mul_zero, Complex.zero_re, Real.rpow_zero, mul_one, Real.rpow_neg hn.le, Real.rpow_natCast, ← inv_pow, ← pow_add]
  congr 1
  omega

/- English proof (translation)
The claim follows from `abs_pos.2 (by exact_mod_cast discr_ne_zero F)`.
-/
theorem dF_pos (F : Type) [Field F] [NumberField F] : 0 < dF F :=
  abs_pos.2 (by exact_mod_cast discr_ne_zero F)

/- English proof (translation)
Establish `h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Conclude with `𝔞.ne_zero`. Unfold `nrm`. Conclude with `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm` after adjusting the coercions.
-/
theorem nrm_pos {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  unfold nrm
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

/- English proof (translation)
Establish `hd` using `dF_pos F`. Establish `hn` using `nrm_pos 𝔞`. Unfold `cK omegaFactor`. Rewrite using `[mul_pow, mul_pow, ← Real.rpow_natCast (dF F ^ _), ← Real.rpow_mul hd.le, ← Real.rpow_natCast (dF F) k]`. Establish `h1 : dF F ^ ((1 : ℝ) / 2 * k) ≠ 0` using `(Real.rpow_pos_of_pos hd _).ne'`.

Establish `h2 : nrm 𝔞 ^ k ≠ 0` using `pow_ne_zero _ hn.ne'`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← Real.rpow_add hd, ← Real.rpow_add hd]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) :
    cK F k * (dF F * nrm 𝔞) ^ k / omegaFactor 𝔞 ^ k =
      ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ ((k : ℝ) - 1 / 2) := by
  have hd := dF_pos F
  have hn := nrm_pos 𝔞
  unfold cK omegaFactor
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (dF F ^ _), ← Real.rpow_mul hd.le, ← Real.rpow_natCast (dF F) k]
  have h1 : dF F ^ ((1 : ℝ) / 2 * k) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have h2 : nrm 𝔞 ^ k ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [← Real.rpow_add hd, ← Real.rpow_add hd]
  congr 1
  ring

/- English proof (translation)
Introduce `hL hH hP F _ _ _ hf 𝔞 𝔟 s hs`. Break down `Nat.lt_or_ge s 2 with h1 | h2` into its components or cases. Take `rfl : s = 1` from `by omega`. Take `⟨G, hG, hd, he⟩` from `hH F hf 𝔞 𝔟`. Conclude with `⟨G 0, ⟨fun h => absurd rfl h, fun _ => ⟨G, hG, rfl⟩⟩, hd, he⟩`.

Establish `hsum : ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 (2 * s) 0 z)` using `fun z hz => eisClass_summable_of_hecke hH hf 𝔞 𝔟 h2 hz`. Use `⟨eisSum 𝔞 𝔟 (2 * s) 0, ⟨fun _ z hz => (hsum z hz).hasSum, fun h => by omega⟩, GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn F 𝔞 𝔟 _ hsum, ?_⟩` and prove the remaining obligations. Set `D : (Ideal (𝓞 F))⁰` to `⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩`. Take `⟨Z, Z', hZ, hZ', hfe⟩` from `hP F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl (by rw [mul_assoc, mul_inv_cancel, mul_one])`. Use `⟨Z', hZ', fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨hq, h3⟩` from `GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum F hL 𝔞 𝔟 (2 * s) (by omega) (even_two_mul s) hsum z hz`. Establish `h0` using `GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta F 𝔞 𝔟 s (by omega) D rfl Z hZ z hz`. Establish `hfe'` using `hfe ((2 * s : ℕ) : ℂ) (fun n h => by`. Establish `h' : ((2 * s : ℕ) : ℤ) = -2 * n` using `by exact_mod_cast h`. Use the proof step `omega) (fun n h => by`.

Establish `h' : (1 - ((2 * s : ℕ) : ℤ)) = -2 * n` using `by exact_mod_cast h`. Use the proof step `omega)`. Establish `hc` using `GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer (dF F) (dF_pos F) (Module.finrank ℚ F) s (by omega) _ _ hfe'`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Establish `hG` using `(HasSum.add_compl (f := eisClass 𝔞 𝔟 (2 * s) 0 z) (s := {c : Quotient (latRel 𝔞 𝔟) | c.out.1.2 = 0}) h0 h3).tsum_eq`.

Rewrite using `[show eisSum 𝔞 𝔟 (2 * s) 0 z = ∑' c, eisClass 𝔞 𝔟 (2 * s) 0 z c from rfl, hG]`. Establish `hk` using `const_eq F 𝔞 (2 * s)`. Establish `hω : (omegaFactor 𝔞 : ℂ) ≠ 0`. Unfold `omegaFactor`. Conclude with `(mul_pos (Real.rpow_pos_of_pos (dF_pos F) _) (nrm_pos 𝔞)).ne'` after adjusting the coercions.

Establish `hcK : (cK F (2 * s) : ℂ) ≠ 0`. Establish `: 0 < cK F (2 * s)`. Unfold `cK`. Conclude with `mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hk' : (cK F (2 * s) : ℂ) * ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) / (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((2 * s - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * ((dF F ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ)`. Conclude with `hk` after adjusting the coercions. Rewrite using `[← hc, ← hk']`. Clear the denominators using the available nonvanishing facts.
-/
theorem eisExp : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  intro hL hH hP F _ _ _ hf 𝔞 𝔟 s hs
  rcases Nat.lt_or_ge s 2 with h1 | h2
  · obtain rfl : s = 1 := by omega
    obtain ⟨G, hG, hd, he⟩ := hH F hf 𝔞 𝔟
    exact ⟨G 0, ⟨fun h => absurd rfl h, fun _ => ⟨G, hG, rfl⟩⟩, hd, he⟩
  have hsum : ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := fun z hz =>
    eisClass_summable_of_hecke hH hf 𝔞 𝔟 h2 hz
  refine ⟨eisSum 𝔞 𝔟 (2 * s) 0, ⟨fun _ z hz => (hsum z hz).hasSum, fun h => by omega⟩,
    GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn F 𝔞 𝔟 _ hsum, ?_⟩
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩
  obtain ⟨Z, Z', hZ, hZ', hfe⟩ := hP F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (by rw [mul_assoc, mul_inv_cancel, mul_one])
  refine ⟨Z', hZ', fun z hz => ?_⟩
  obtain ⟨hq, h3⟩ := GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum F hL 𝔞 𝔟 (2 * s) (by omega) (even_two_mul s) hsum z hz
  have h0 := GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta F 𝔞 𝔟 s (by omega) D rfl Z hZ z hz
  have hfe' := hfe ((2 * s : ℕ) : ℂ) (fun n h => by
      have h' : ((2 * s : ℕ) : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - ((2 * s : ℕ) : ℤ)) = -2 * n := by exact_mod_cast h
      omega)
  have hc := GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer (dF F) (dF_pos F) (Module.finrank ℚ F) s (by omega) _ _ hfe'
  refine ⟨hq, ?_⟩
  have hG := (HasSum.add_compl (f := eisClass 𝔞 𝔟 (2 * s) 0 z) (s := {c : Quotient (latRel 𝔞 𝔟) | c.out.1.2 = 0}) h0 h3).tsum_eq
  rw [show eisSum 𝔞 𝔟 (2 * s) 0 z = ∑' c, eisClass 𝔞 𝔟 (2 * s) 0 z c from rfl, hG]
  have hk := const_eq F 𝔞 (2 * s)
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    unfold omegaFactor
    exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (dF_pos F) _) (nrm_pos 𝔞)).ne'
  have hcK : (cK F (2 * s) : ℂ) ≠ 0 := by
    have : 0 < cK F (2 * s) := by
      unfold cK
      exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
    exact_mod_cast this.ne'
  have hk' : (cK F (2 * s) : ℂ) * ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) / (omegaFactor 𝔞 : ℂ) ^ (2 * s) =
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * ((dF F ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) := by
    exact_mod_cast hk
  rw [← hc, ← hk']
  field_simp

end GlobalTheory.HilbertEis
