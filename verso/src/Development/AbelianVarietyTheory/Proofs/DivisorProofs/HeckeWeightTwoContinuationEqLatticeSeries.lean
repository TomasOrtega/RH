import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinLatticeClassWeightTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumLatticePairUnitQuotientRegroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoPoissonSummationFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformZeroEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumAbsNormCpowUnitClassesPartialZetaStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoEq

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul, mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)), ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]`.
-/
theorem ofReal_prod_cpow {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (c : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ c = ∏ i ∈ s, ((r i : ℂ) ^ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Unfold `eisTerm kFac phi`. Rewrite using `[← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖`. Simplify using `only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`.

Rewrite using `[hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]`. Simplify using `only [latPt, mul_inv, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisTerm_eq_kFac (σ : ℂ) (z : Emb F → ℂ) (a b : F) :
    eisTerm 2 σ z (a, b) = kFac F σ * ∏ τ : Emb F, phi σ ((τ a : ℂ) + (τ b : ℂ) * z τ) := by
  unfold eisTerm kFac phi
  rw [← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖ := by
    simp only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  simp only [latPt, mul_inv, mul_pow]
  ring

/- English proof (translation)
Establish `h0 : (0 : F) ∈ I` using `(I : Submodule (𝓞 F) F).zero_mem`. Rewrite using `[h.tsum_eq_add_tsum_ite ⟨0, h0⟩]`. Use `congr 1`. Set `e : NZ I → {ν : F // ν ∈ I}` to `fun ν => ⟨ν.1, ν.2.1⟩`. Establish `he : Function.Injective e` using `fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)`.

Rewrite using `[← he.tsum_eq]`. Use `tsum_congr fun ν => ?_` and prove the remaining obligations. Establish `: e ν ≠ ⟨0, h0⟩` using `fun h' => ν.2.2 (congrArg Subtype.val h' : _)`. Simplify using `only [this, if_false, e]`. Introduce `x hx`.

Establish `hx0 : x ≠ ⟨0, h0⟩`. Introduce `h'`. Apply `hx` to reduce the goal to its premises. Simplify using `[h']`. Conclude with `⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩`.
-/
theorem split_zero (I : FractionalIdeal (𝓞 F)⁰ F) (g : F → ℂ) (h : Summable (fun ν : {ν : F // ν ∈ I} => g ν.1)) :
    ∑' ν : {ν : F // ν ∈ I}, g ν.1 = g 0 + ∑' ν : NZ I, g ν.1 := by
  classical
  have h0 : (0 : F) ∈ I := (I : Submodule (𝓞 F) F).zero_mem
  rw [h.tsum_eq_add_tsum_ite ⟨0, h0⟩]
  congr 1
  let e : NZ I → {ν : F // ν ∈ I} := fun ν => ⟨ν.1, ν.2.1⟩
  have he : Function.Injective e := fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)
  rw [← he.tsum_eq]
  · refine tsum_congr fun ν => ?_
    have : e ν ≠ ⟨0, h0⟩ := fun h' => ν.2.2 (congrArg Subtype.val h' : _)
    simp only [this, if_false, e]
  · intro x hx
    have hx0 : x ≠ ⟨0, h0⟩ := by
      intro h'; apply hx; simp [h']
    exact ⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩

/- English proof (translation)
Rewrite using `[← Finset.abs_prod]`. Use `congr 1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `prod_emb b`.
-/
theorem prod_abs_emb [IsTotallyReal F] (b : F) : ∏ τ : Emb F, |τ b| = |((Algebra.norm ℚ b : ℚ) : ℝ)| := by
  rw [← Finset.abs_prod]
  congr 1
  apply Complex.ofReal_injective
  push_cast
  exact prod_emb b

/- English proof (translation)
Unfold `fTerm`. Rewrite using `[← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hy : 0 < (z τ).im` using `hz τ`. Establish `hτb : τ b ≠ 0` using `(map_ne_zero τ).2 hb`.

Rewrite using `[map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul, mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring

/- English proof (translation)
Introduce `F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz`. Establish `hS` using `GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two F 𝔞 𝔟 σ hσ z hz`. Use `⟨hS, ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F), eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b)` using `fun ε a b => eisTerm_unit even_two σ z ε a b`. Take `⟨-, -, hBs, hsum⟩` from `GlobalTheory.T.tsum_latticePair_unitQuotient_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS`.

Establish `hσ0 : σ ≠ 0` using `by rintro rfl; simp at hσ`. Use `set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef`. Use `set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef`. Establish `hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) = K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) + K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1`. Introduce `c`.

Establish `hb : c.out.1 ≠ 0` using `c.out.2.2`. Take `⟨hfs, hP⟩` from `GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal F 𝔞 σ hσ z hz c.out.1 hb`. Repeatedly rewrite using `[eisTerm_eq_kFac]`. Rewrite using `[tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hz2` using `GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)`. Rewrite `hz2` using `[show -(1 + 2 * σ) = -1 - 2 * σ by ring]`. Establish `hX` using `hz2.mul_left (K * P)`. Establish `hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) + K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1)`. Simplify `hBs` using `only [hper]`.

Establish `hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1)` using `(hT.sub hX.summable).congr fun c => by ring`. Unfold `eisSum eisClass`. Rewrite using `[hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]`. Establish `hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ` using `tsum_congr fun c => by simp [eisTerm, latPt]`. Rewrite using `[hA]`.

Unfold `gFun bZero bOne`. Rewrite using `[if_neg hσ0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gFun_eq_eisSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  intro F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz
  have hS := GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two F 𝔞 𝔟 σ hσ z hz
  refine ⟨hS, ?_⟩
  have hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F),
      eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b) :=
    fun ε a b => eisTerm_unit even_two σ z ε a b
  obtain ⟨-, -, hBs, hsum⟩ := GlobalTheory.T.tsum_latticePair_unitQuotient_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef
  set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef
  have hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) =
        K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1 := by
    intro c
    have hb : c.out.1 ≠ 0 := c.out.2.2
    obtain ⟨hfs, hP⟩ := GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal F 𝔞 σ hσ z hz c.out.1 hb
    simp_rw [eisTerm_eq_kFac]
    rw [tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]
    ring
  have hz2 := GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)
  rw [show -(1 + 2 * σ) = -1 - 2 * σ by ring] at hz2
  have hX := hz2.mul_left (K * P)
  have hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) := by
    simpa only [hper] using hBs
  have hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) :=
    (hT.sub hX.summable).congr fun c => by ring
  unfold eisSum eisClass
  rw [hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]
  have hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ :=
    tsum_congr fun c => by simp [eisTerm, latPt]
  rw [hA]
  unfold gFun bZero bOne
  rw [if_neg hσ0]
  ring

end GlobalTheory.HeckeTwoEq
