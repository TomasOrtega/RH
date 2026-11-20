import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.FactorBound

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `x`.

Establish `h1 : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * z)) (Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) * (2 * (Real.pi : ℂ) * I)) (x : ℂ)`. Use `((hasDerivAt_id (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).cexp` as an intermediate fact. Simplify using `using this`. Establish `h2` using `(h1.comp_ofReal).const_mul ((2 * (Real.pi : ℂ) * I) ^ i)`. Rewrite using `[h2.deriv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedDeriv_eChar (i : ℕ) :
    iteratedDeriv i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * I) ^ i * Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * z))
        (Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) * (2 * (Real.pi : ℂ) * I)) (x : ℂ) := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).cexp
      simpa using this
    have h2 := (h1.comp_ofReal).const_mul ((2 * (Real.pi : ℂ) * I) ^ i)
    rw [h2.deriv]
    ring

/- English proof (translation)
The claim follows from `(contDiff_const.mul Complex.ofRealCLM.contDiff).cexp`.
-/
theorem contDiff_eChar :
    ContDiff ℝ ω (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/- English proof (translation)
Rewrite using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eChar]`. Simplify using `only [norm_mul, norm_pow]`. Establish `: ‖Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))‖ = 1`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.

Rewrite using `[this, mul_one]`. Use `congr 1`. Simplify using `[Complex.norm_real, abs_of_pos Real.pi_pos]`.
-/
theorem norm_iteratedFDeriv_eChar (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) x‖ = (2 * Real.pi) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eChar]
  simp only [norm_mul, norm_pow]
  have : ‖Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]
  congr 1
  simp [Complex.norm_real, abs_of_pos Real.pi_pos]

/- English proof (translation)
Use `set L : ℂ →L[ℝ] ℝ := a • Complex.reCLM`. Establish `hf : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) = (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) ∘ L`. Use function extensionality and compare the values at `w`. Simplify using `[L]`. Rewrite using `[hf, L.iteratedFDeriv_comp_right contDiff_eChar w le_top]`.

Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_iteratedFDeriv_eChar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hL : ‖L‖ ≤ |a|`. Simplify using `only [L]`. Use `(norm_smul_le _ _).trans ?_` and prove the remaining obligations.

Simplify using `[Complex.reCLM_norm]`. Rewrite using `[mul_pow (2 * Real.pi) |a| i]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (pow_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) _)`.
-/
theorem norm_iteratedFDeriv_eRe (a : ℝ) (i : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ i (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) w‖ ≤
      (2 * Real.pi * |a|) ^ i := by
  set L : ℂ →L[ℝ] ℝ := a • Complex.reCLM
  have hf : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) =
      (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) ∘ L := by
    funext w; simp [L]
  rw [hf, L.iteratedFDeriv_comp_right contDiff_eChar w le_top]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eChar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖L‖ ≤ |a| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.reCLM_norm]
  rw [mul_pow (2 * Real.pi) |a| i]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (pow_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) _)

/- English proof (translation)
Use `set L : ℂ →L[ℝ] ℝ := β • Complex.imCLM`. Establish `hS : IsOpen {y : ℝ | y ≠ 0}` using `isOpen_ne`. Establish `hpre : {w : ℂ | β * w.im ≠ 0} = L ⁻¹' {y : ℝ | y ≠ 0}` using `by ext w; simp [L]`. Establish `hf : (fun w : ℂ => hTrans σ ν (β * w.im)) = hTrans σ ν ∘ L` using `by funext w; simp [L]`. Establish `hLw : L w = β * w.im` using `by simp [L]`.

Establish `hLw' : L w ∈ {y : ℝ | y ≠ 0}` using `by rw [hLw]; exact hw`. Rewrite using `[hf, hpre, L.iteratedFDerivWithin_comp_right (TermSmooth.contDiffOn_hTrans σ hσ ν) hS.uniqueDiffOn (hS.preimage L.continuous).uniqueDiffOn hLw' (by exact_mod_cast le_top)]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDerivWithin_of_isOpen j hS hLw', norm_iteratedFDeriv_eq_norm_iteratedDeriv, hLw]`. Establish `hL : ‖L‖ ≤ |β|`.

Simplify using `only [L]`. Use `(norm_smul_le _ _).trans ?_` and prove the remaining obligations. Simplify using `[Complex.imCLM_norm]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)`.
-/
theorem norm_iteratedFDerivWithin_hIm (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (j : ℕ) (w : ℂ)
    (hw : β * w.im ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | β * w.im ≠ 0} w‖ ≤
      ‖iteratedDeriv j (hTrans σ ν) (β * w.im)‖ * |β| ^ j := by
  set L : ℂ →L[ℝ] ℝ := β • Complex.imCLM
  have hS : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  have hpre : {w : ℂ | β * w.im ≠ 0} = L ⁻¹' {y : ℝ | y ≠ 0} := by ext w; simp [L]
  have hf : (fun w : ℂ => hTrans σ ν (β * w.im)) = hTrans σ ν ∘ L := by funext w; simp [L]
  have hLw : L w = β * w.im := by simp [L]
  have hLw' : L w ∈ {y : ℝ | y ≠ 0} := by rw [hLw]; exact hw
  rw [hf, hpre, L.iteratedFDerivWithin_comp_right (TermSmooth.contDiffOn_hTrans σ hσ ν) hS.uniqueDiffOn
    (hS.preimage L.continuous).uniqueDiffOn hLw' (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDerivWithin_of_isOpen j hS hLw',
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, hLw]
  have hL : ‖L‖ ≤ |β| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.imCLM_norm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)

/- English proof (translation)
Use `set V : Set ℂ := {w : ℂ | β * w.im ≠ 0}`. Establish `hV : IsOpen V` using `isOpen_ne_fun (continuous_const.mul Complex.continuous_im) continuous_const`. Establish `hwV : w ∈ V` using `mul_ne_zero hβ hw.ne'`. Establish `hu : ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) V` using `((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff))).cexp).contDiffOn`. Establish `hv : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) V` using `(TermSmooth.contDiffOn_hTrans σ hσ ν).comp (contDiff_const.mul Complex.imCLM.contDiff).contDiffOn fun z hz => hz`.

Rewrite using `[← iteratedFDerivWithin_of_isOpen k hV hwV]`. Use `(norm_iteratedFDerivWithin_mul_le hu hv hV.uniqueDiffOn hwV (by exact_mod_cast le_top)).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[iteratedFDerivWithin_of_isOpen i hV hwV]`. Use `mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_eRe (ν * β) i w) (Nat.cast_nonneg _)) (norm_iteratedFDerivWithin_hIm σ hσ ν β (k - i) w hwV) (norm_nonneg _) ?_` and prove the remaining obligations.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)`.
-/
theorem norm_iteratedFDeriv_le_sum (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) (k : ℕ) (w : ℂ)
    (hw : 0 < w.im) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i *
        (‖iteratedDeriv (k - i) (hTrans σ ν) (β * w.im)‖ * |β| ^ (k - i)) := by
  set V : Set ℂ := {w : ℂ | β * w.im ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (continuous_const.mul Complex.continuous_im) continuous_const
  have hwV : w ∈ V := mul_ne_zero hβ hw.ne'
  have hu : ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) V :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul Complex.reCLM.contDiff))).cexp).contDiffOn
  have hv : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) V :=
    (TermSmooth.contDiffOn_hTrans σ hσ ν).comp (contDiff_const.mul Complex.imCLM.contDiff).contDiffOn
      fun z hz => hz
  rw [← iteratedFDerivWithin_of_isOpen k hV hwV]
  refine (norm_iteratedFDerivWithin_mul_le hu hv hV.uniqueDiffOn hwV (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iteratedFDerivWithin_of_isOpen i hV hwV]
  refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_eRe (ν * β) i w) (Nat.cast_nonneg _))
    (norm_iteratedFDerivWithin_hIm σ hσ ν β (k - i) w hwV) (norm_nonneg _) ?_
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)

/- English proof (translation)
Introduce `H K hK hKH c c' hc k`. Use `choose s hs using H K hK hKH`. Use `⟨k + ∑ j ∈ Finset.range (k + 1), s j, fun N => ?_⟩` and prove the remaining obligations. Use `choose C hC using fun j => hs j (N + k)`. Use `set M : ℝ := max c' c⁻¹ with hMdef`.

Use `set μ : ℝ := min 1 c with hμdef`. Establish `hM : 0 < M` using `lt_of_lt_of_le (inv_pos.2 hc) (le_max_right _ _)`. Establish `hμ : 0 < μ` using `lt_min one_pos hc`. Use `⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C (k - i)| * M ^ s (k - i) / μ ^ (N + k)), ?_⟩` and prove the remaining obligations. Introduce `σ hσ ν β hν hβ w hw1 hw2`.

Establish `hσH : σ ∈ halfPlane` using `hKH hσ`. Establish `ht : 0 < w.im` using `lt_of_lt_of_le hc hw1`. Use `set t := w.im with htdef`. Use `set B : ℝ := |β| + |β|⁻¹ with hBdef`. Use `set A : ℝ := 1 + |ν * β| with hAdef`.

Establish `hβp : 0 < |β|` using `abs_pos.2 hβ`. Establish `hB1 : 1 ≤ B`. Break down `le_total 1 |β| with h | h` into its components or cases. Use `inv_nonneg.2 hβp.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(one_le_inv₀ hβp).2 h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA1 : 1 ≤ A` using `by have := abs_nonneg (ν * β); linarith`. Establish `hApos : 0 < A` using `by linarith`. Establish `hy : β * t ≠ 0` using `mul_ne_zero hβ ht.ne'`.

Establish `hyB : |β * t| + |β * t|⁻¹ ≤ M * B`. Rewrite using `[abs_mul, abs_of_pos ht, mul_inv, hBdef, mul_add]`. Establish `h1 : |β| * t ≤ M * |β|`. Rewrite using `[mul_comm M]`. Conclude with `mul_le_mul_of_nonneg_left (hw2.trans (le_max_left _ _)) hβp.le`.

Establish `h2 : |β|⁻¹ * t⁻¹ ≤ M * |β|⁻¹`. Rewrite using `[mul_comm M]`. Use `mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβp.le)` and prove the remaining obligations. Conclude with `(inv_anti₀ hc hw1).trans (le_max_right _ _)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hyA : μ * A ≤ 1 + |ν * (β * t)|`. Rewrite using `[← mul_assoc, abs_mul (ν * β), abs_of_pos ht, hAdef, mul_add, mul_one]`. Establish `h1 : μ ≤ 1` using `min_le_left _ _`. Establish `h2 : μ ≤ t` using `(min_le_right _ _).trans hw1`. Establish `h3 : μ * |ν * β| ≤ |ν * β| * t`.

Rewrite using `[mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left h2 (abs_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : ∀ j, ‖iteratedDeriv j (hTrans σ ν) (β * t)‖ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k)`. Introduce `j`.

Use `(hC j σ hσ ν (β * t) hν hy).trans ?_` and prove the remaining obligations. Establish `hX : 0 ≤ (|β * t| + |β * t|⁻¹) ^ s j` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_abs_self _`. Use `_ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by gcongr`.

Use `(norm_iteratedFDeriv_le_sum σ hσH ν β hβ k w ht).trans ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc, Finset.sum_mul]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hik : i ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Use `set j := k - i with hjdef`.

Establish `hjk : j ≤ k` using `Nat.sub_le _ _`. Establish `hsj : s j ≤ ∑ j ∈ Finset.range (k + 1), s j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))`. Establish `hd : (2 * Real.pi * |ν * β|) ^ i ≤ (2 * Real.pi) ^ i * A ^ k`. Rewrite using `[mul_pow]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `he : |β| ^ j ≤ B ^ k` using `(pow_le_pow_left₀ hβp.le (by have := inv_nonneg.2 hβp.le; linarith) j).trans (pow_le_pow_right₀ hB1 hjk)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hh j`. Use `_ = (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + s j) / A ^ N) := by`.

Establish `hA0 : A ≠ 0` using `hApos.ne'`. Establish `hμ0 : μ ≠ 0` using `hμ.ne'`. Rewrite using `[mul_pow, mul_pow, pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_pow, mul_pow, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `_ ≤ (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + ∑ j ∈ Finset.range (k + 1), s j) / A ^ N) := by gcongr all_goals first | exact hB1 | omega`.
-/
theorem norm_iteratedFDeriv_fourierFactor_le :
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  intro H K hK hKH c c' hc k
  choose s hs using H K hK hKH
  refine ⟨k + ∑ j ∈ Finset.range (k + 1), s j, fun N => ?_⟩
  choose C hC using fun j => hs j (N + k)
  set M : ℝ := max c' c⁻¹ with hMdef
  set μ : ℝ := min 1 c with hμdef
  have hM : 0 < M := lt_of_lt_of_le (inv_pos.2 hc) (le_max_right _ _)
  have hμ : 0 < μ := lt_min one_pos hc
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi) ^ i *
      (|C (k - i)| * M ^ s (k - i) / μ ^ (N + k)), ?_⟩
  intro σ hσ ν β hν hβ w hw1 hw2
  have hσH : σ ∈ halfPlane := hKH hσ
  have ht : 0 < w.im := lt_of_lt_of_le hc hw1
  set t := w.im with htdef
  set B : ℝ := |β| + |β|⁻¹ with hBdef
  set A : ℝ := 1 + |ν * β| with hAdef
  have hβp : 0 < |β| := abs_pos.2 hβ
  have hB1 : 1 ≤ B := by
    rcases le_total 1 |β| with h | h
    · have := inv_nonneg.2 hβp.le; linarith
    · have := (one_le_inv₀ hβp).2 h; linarith
  have hA1 : 1 ≤ A := by have := abs_nonneg (ν * β); linarith
  have hApos : 0 < A := by linarith
  have hy : β * t ≠ 0 := mul_ne_zero hβ ht.ne'
  have hyB : |β * t| + |β * t|⁻¹ ≤ M * B := by
    rw [abs_mul, abs_of_pos ht, mul_inv, hBdef, mul_add]
    have h1 : |β| * t ≤ M * |β| := by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hw2.trans (le_max_left _ _)) hβp.le
    have h2 : |β|⁻¹ * t⁻¹ ≤ M * |β|⁻¹ := by
      rw [mul_comm M]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβp.le)
      exact (inv_anti₀ hc hw1).trans (le_max_right _ _)
    linarith
  have hyA : μ * A ≤ 1 + |ν * (β * t)| := by
    rw [← mul_assoc, abs_mul (ν * β), abs_of_pos ht, hAdef, mul_add, mul_one]
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ t := (min_le_right _ _).trans hw1
    have h3 : μ * |ν * β| ≤ |ν * β| * t := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  have hh : ∀ j, ‖iteratedDeriv j (hTrans σ ν) (β * t)‖ ≤
      |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
    intro j
    refine (hC j σ hσ ν (β * t) hν hy).trans ?_
    have hX : 0 ≤ (|β * t| + |β * t|⁻¹) ^ s j := by positivity
    calc C j * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k)
        ≤ |C j| * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k) := by
          gcongr
          exact le_abs_self _
      _ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
          gcongr
  refine (norm_iteratedFDeriv_le_sum σ hσH ν β hβ k w ht).trans ?_
  rw [mul_div_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  set j := k - i with hjdef
  have hjk : j ≤ k := Nat.sub_le _ _
  have hsj : s j ≤ ∑ j ∈ Finset.range (k + 1), s j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))
  have hd : (2 * Real.pi * |ν * β|) ^ i ≤ (2 * Real.pi) ^ i * A ^ k := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |ν * β| ^ i ≤ A ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hik
  have he : |β| ^ j ≤ B ^ k :=
    (pow_le_pow_left₀ hβp.le (by have := inv_nonneg.2 hβp.le; linarith) j).trans (pow_le_pow_right₀ hB1 hjk)
  calc (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i * (‖iteratedDeriv j (hTrans σ ν) (β * t)‖ * |β| ^ j)
      ≤ (k.choose i : ℝ) * ((2 * Real.pi) ^ i * A ^ k) *
          ((|C j| * (M * B) ^ s j / (μ * A) ^ (N + k)) * B ^ k) := by
        gcongr
        exact hh j
    _ = (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + s j) / A ^ N) := by
        have hA0 : A ≠ 0 := hApos.ne'
        have hμ0 : μ ≠ 0 := hμ.ne'
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp
        rw [mul_pow, mul_pow, pow_add]
        ring
    _ ≤ (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) *
          (B ^ (k + ∑ j ∈ Finset.range (k + 1), s j) / A ^ N) := by
        gcongr
        all_goals first | exact hB1 | omega

end GlobalTheory.HeckeTwo.FactorBound

end
