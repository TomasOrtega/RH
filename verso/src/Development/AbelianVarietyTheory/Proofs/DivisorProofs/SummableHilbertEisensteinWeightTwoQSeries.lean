import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoSum

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h` using `Real.pow_div_factorial_le_exp (c * t) (by positivity) n`. Establish `hf : (0 : ℝ) < n.factorial` using `by exact_mod_cast n.factorial_pos`. Establish `he` using `Real.exp_pos (c * t)`. Rewrite `h` using `[div_le_iff₀ hf, mul_pow]`. Rewrite using `[le_div_iff₀ (pow_pos hc n), Real.exp_neg]`.

Rewrite using `[show t ^ n * (Real.exp (c * t))⁻¹ * c ^ n = (c ^ n * t ^ n) / Real.exp (c * t) by field_simp]`. Rewrite using `[div_le_iff₀ he]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pow_mul_exp_neg_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-(c * t)) ≤ n.factorial / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * t) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have he := Real.exp_pos (c * t)
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ (pow_pos hc n), Real.exp_neg]
  rw [show t ^ n * (Real.exp (c * t))⁻¹ * c ^ n = (c ^ n * t ^ n) / Real.exp (c * t) by field_simp]
  rw [div_le_iff₀ he]
  linarith

/- English proof (translation)
Take `⟨d, hd, hdI⟩` from `GlobalTheory.HeckeTwo.APart.exists_den I`. Establish `hd' : (d : F) ≠ 0` using `by exact_mod_cast hd`. Establish `hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|`. Simplify using `[Algebra.norm_eq_zero_iff, hd']`. Use `⟨|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|⁻¹, inv_pos.2 hNd, fun ν hν hν0 => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `hdI ν hν`. Establish `e1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ ν`. Rewrite using `[Algebra.coe_norm_int, hx, map_mul]`. Establish `hxz : (Algebra.norm ℤ x : ℤ) ≠ 0`. Introduce `h`.

Rewrite `e1` using `[h, Int.cast_zero]`. Establish `h1 : Algebra.norm ℚ (d : F) ≠ 0` using `(Algebra.norm_ne_zero_iff).2 hd'`. Establish `h2 : Algebra.norm ℚ ν ≠ 0` using `(Algebra.norm_ne_zero_iff).2 hν0`. Conclude with `mul_ne_zero h1 h2 e1.symm`. Establish `h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)|`.

Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hxz` after adjusting the coercions. Establish `e2 : ((Algebra.norm ℤ x : ℤ) : ℝ) = ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ ν : ℚ) : ℝ)`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) e1` after adjusting the coercions. Rewrite `h1` using `[e2, abs_mul]`.

Use `mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNd).le` as an intermediate fact. Rewrite `this` using `[mul_one, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_norm_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν ∈ I, ν ≠ 0 → κ ≤ |((Algebra.norm ℚ ν : ℚ) : ℝ)| := by
  obtain ⟨d, hd, hdI⟩ := GlobalTheory.HeckeTwo.APart.exists_den I
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine ⟨|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|⁻¹, inv_pos.2 hNd, fun ν hν hν0 => ?_⟩
  obtain ⟨x, hx⟩ := hdI ν hν
  have e1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ ν := by
    rw [Algebra.coe_norm_int, hx, map_mul]
  have hxz : (Algebra.norm ℤ x : ℤ) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at e1
    have h1 : Algebra.norm ℚ (d : F) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hd'
    have h2 : Algebra.norm ℚ ν ≠ 0 := (Algebra.norm_ne_zero_iff).2 hν0
    exact mul_ne_zero h1 h2 e1.symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hxz
  have e2 : ((Algebra.norm ℤ x : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNd).le
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul] at this

/- English proof (translation)
Rewrite using `[qPow, Complex.norm_exp]`. Use `congr 1`. Simplify using `[Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]`.
-/
theorem norm_qPow (ξ : F) (z : Emb F → ℂ) :
    ‖qPow ξ z‖ = Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) := by
  rw [qPow, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

end GlobalTheory.HeckeTwoSum

namespace GlobalTheory.HeckeTwoSum

open GlobalTheory.LipschitzTR

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨τ₀⟩` from `GlobalTheory.HeckeTwoExp.emb_nonempty (F := F)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hmy⟩ : ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ (z τ).im := by`. Take `⟨τ₁, -, hτ₁⟩` from `Finset.exists_min_image Finset.univ (fun τ => (z τ).im) ⟨τ₀, Finset.mem_univ _⟩`. Conclude with `⟨_, hz τ₁, fun τ => hτ₁ τ (Finset.mem_univ _)⟩`. Take `⟨κ, hκ, hκν⟩` from `exists_norm_lower (𝔞 : FractionalIdeal (𝓞 F)⁰ F)`.

Establish `hnrm : 0 < nrm 𝔞` using `lt_of_le_of_ne (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _) (GlobalTheory.HeckeTwoExp.nrm_ne_zero 𝔞).symm`. Use `set N : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) with hN`. Use `haveI : DiscreteTopology (latOf N) := discrete_latOf F N`. Use `set n : ℕ := Module.finrank ℤ (latOf N) + 1 with hn`. Establish `hL : Summable fun v : latOf N => ‖v‖⁻¹ ^ n` using `ZLattice.summable_norm_pow_inv (latOf N) n (Nat.lt_succ_self _)`.

Use `set f : ℕ := Fintype.card (Emb F) with hf`. Use `set K : ℝ := ((2 * f + n).factorial : ℝ) / (2 * Real.pi * m) ^ (2 * f + n) with hK`. Use `set C : ℝ := K / (nrm 𝔞 * κ) with hC`. Establish `hK0 : 0 < K` using `by positivity`. Establish `hC0 : 0 < C` using `by positivity`.

Establish `key : ∀ ν b : F, ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ν ≠ 0 → b ≠ 0 → (∀ τ : Emb F, 0 < τ (ν * b)) → ‖qTerm 𝔞 2 z (ν, b)‖ ≤ C * ((|((Algebra.norm ℚ b : ℚ) : ℝ)| ^ 2)⁻¹ * ‖remb F (ν * b)‖⁻¹ ^ n)`. Introduce `ν b hν hν0 hb0 hpos`. Use `set ξ := ν * b with hξ`. Use `set s := ∑ τ : Emb F, τ ξ with hs_def`. Use `set A := |((Algebra.norm ℚ ν : ℚ) : ℝ)| with hA_def`.

Use `set B := |((Algebra.norm ℚ b : ℚ) : ℝ)| with hB_def`. Use `set w := ‖remb F ξ‖ with hw_def`. Establish `hs : 0 < s` using `Finset.sum_pos (fun τ _ => hpos τ) ⟨τ₀, Finset.mem_univ _⟩`. Establish `hA : κ ≤ A` using `hκν ν hν hν0`. Establish `hA0 : 0 < A` using `hκ.trans_le hA`.

Establish `hB0 : 0 < B`. Rewrite using `[hB_def, abs_pos, Rat.cast_ne_zero]`. Conclude with `(Algebra.norm_ne_zero_iff).2 hb0`. Establish `hw0 : 0 < w`. Rewrite using `[hw_def, norm_pos_iff]`.

Introduce `h`. Use `congrArg (fun v : RSp F => v τ₀) h` as an intermediate fact. Establish `h3 : τ₀ ξ = 0` using `by simpa using this`. Establish `h2` using `hpos τ₀`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hws : w ≤ s`. Rewrite using `[hw_def, EuclideanSpace.norm_eq]`. Use `Real.sqrt_le_iff.2 ⟨hs.le, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[remb_apply, Real.norm_eq_abs, sq_abs]`. Use `_ ≤ (∑ τ : Emb F, τ ξ) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun τ _ => (hpos τ).le`. Establish `hAB : A * B ≤ s ^ f`. Establish `h2` using `GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ξ`. Rewrite `h2` using `[← Complex.ofReal_prod]`.

Establish `h3` using `Complex.ofReal_injective h2`. Establish `h1 : A * B = ∏ τ : Emb F, τ ξ`. Rewrite using `[hA_def, hB_def, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hξ, h3]`. Conclude with `Finset.prod_congr rfl fun τ _ => abs_of_pos (hpos τ)`. Rewrite using `[h1, hf, ← Finset.card_univ, ← Finset.prod_const]`.

Conclude with `Finset.prod_le_prod (fun τ _ => (hpos τ).le) (fun τ _ => Finset.single_le_sum (fun τ _ => (hpos τ).le) (Finset.mem_univ τ))`. Use `set E := Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) with hE`. Use `set E' := Real.exp (-((2 * Real.pi * m) * s)) with hE'`. Establish `hEE : E ≤ E'`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Establish `: m * s ≤ ∑ τ, τ ξ * (z τ).im`. Rewrite using `[hs_def, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hmy τ]`. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `hKs` using `pow_mul_exp_neg_le (c := 2 * Real.pi * m) (t := s) (by positivity) hs.le (2 * f + n)`.

Establish `hP : (A * B) ^ 2 * w ^ n ≤ s ^ (2 * f + n)`. Rewrite using `[show s ^ (2 * f + n) = (s ^ f) ^ 2 * s ^ n by ring]`. Use `gcongr`. Establish `hE'K : E' * ((A * B) ^ 2 * w ^ n) ≤ K`. Establish `hE'0 : 0 ≤ E'` using `(Real.exp_pos _).le`.

Combine the equalities or inequalities in the displayed calculation. Establish `hnorm : ‖qTerm 𝔞 2 z (ν, b)‖ = A / nrm 𝔞 * E`. Rewrite using `[qTerm, norm_mul, norm_qPow, Complex.norm_real, Real.norm_eq_abs, show (2 : ℕ) - 1 = 1 from rfl, pow_one, abs_of_nonneg (div_nonneg (abs_nonneg _) hnrm.le)]`. Establish `hR : C * ((B ^ 2)⁻¹ * w⁻¹ ^ n) = K / (nrm 𝔞 * κ * B ^ 2 * w ^ n)`. Rewrite using `[hC, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hnorm, hR, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ E' * (A * A * B ^ 2 * w ^ n) := by gcongr`.

Use `_ = E' * ((A * B) ^ 2 * w ^ n) := by ring`. Use `_ ≤ K := hE'K`. Use `set e := Equiv.ofBijective (GlobalTheory.HeckeTwoExp.toQ 𝔞 𝔟) ⟨GlobalTheory.HeckeTwoExp.toQ_injective 𝔞 𝔟, GlobalTheory.HeckeTwoExp.toQ_surjective 𝔞 𝔟⟩ with he`. Set `ι : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)} → latOf N` to `fun c ν => ⟨remb F (ν.1.1 * c.out.1), (mem_latOf N _).2 ⟨_, FractionalIdeal.mul_mem_mul ν.1.2.1 c.out.2.1, rfl⟩⟩`. Establish `hι : ∀ c, Function.Injective (ι c)`.

Introduce `c ν ν' h`. Establish `h1` using `congrArg (fun v : latOf N => (v : RSp F) τ₀) h`. Simplify using `only [ι, remb_apply] at h1`. Establish `h2 : ν.1.1 * c.out.1 = ν'.1.1 * c.out.1` using `τ₀.injective h1`. Conclude with `Subtype.ext (Subtype.ext (mul_right_cancel₀ c.out.2.2 h2))`.

Use `set Bf : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ := fun c => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| with hBf`. Use `set G : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → ℝ := fun p => C * ((Bf p.1 ^ 2)⁻¹ * ‖ι p.1 p.2‖⁻¹ ^ n) with hG`. Establish `hG0 : ∀ p, 0 ≤ G p` using `fun p => by`. Simplify using `only [hG]`. Check the signs of the components of the expression.

Establish `hbound : ∀ p, ‖qClass 𝔞 𝔟 2 z (e p)‖ ≤ G p`. Introduce and unpack `⟨c, ν⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hGs : Summable G`. Use `(summable_sigma_of_nonneg hG0).2 ⟨fun c => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `((hL.comp_injective (hι c)).mul_left ((Bf c ^ 2)⁻¹)).mul_left C`. Establish `hZ` using `GlobalTheory.HeckeTwo.APart.summable_norm_rpow (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (s := 2) one_lt_two`. Use `Summable.of_nonneg_of_le (fun c => tsum_nonneg fun ν => hG0 ⟨c, ν⟩) (fun c => ?_) (hZ.mul_left (C * ∑' v : latOf N, ‖v‖⁻¹ ^ n))` and prove the remaining obligations. Use `show ∑' ν, C * ((Bf c ^ 2)⁻¹ * ‖ι c ν‖⁻¹ ^ n) ≤ _`. Rewrite using `[tsum_mul_left, tsum_mul_left, Real.rpow_neg (abs_nonneg _), Real.rpow_two]`.

Establish `hH : ∑' ν, ‖ι c ν‖⁻¹ ^ n ≤ ∑' v : latOf N, ‖v‖⁻¹ ^ n` using `tsum_comp_le_tsum_of_inj hL (fun _ => by positivity) (hι c)`. Establish `hB : 0 ≤ (Bf c ^ 2)⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `Summable.of_norm ?_` and prove the remaining obligations. Rewrite using `[← e.summable_iff]`.

Conclude with `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hGs`.
-/
theorem summable_qClass_two [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) := by
  classical
  obtain ⟨τ₀⟩ := GlobalTheory.HeckeTwoExp.emb_nonempty (F := F)
  obtain ⟨m, hm, hmy⟩ : ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ (z τ).im := by
    obtain ⟨τ₁, -, hτ₁⟩ := Finset.exists_min_image Finset.univ (fun τ => (z τ).im) ⟨τ₀, Finset.mem_univ _⟩
    exact ⟨_, hz τ₁, fun τ => hτ₁ τ (Finset.mem_univ _)⟩
  obtain ⟨κ, hκ, hκν⟩ := exists_norm_lower (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hnrm : 0 < nrm 𝔞 := lt_of_le_of_ne (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
    (GlobalTheory.HeckeTwoExp.nrm_ne_zero 𝔞).symm
  set N : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) with hN
  haveI : DiscreteTopology (latOf N) := discrete_latOf F N
  set n : ℕ := Module.finrank ℤ (latOf N) + 1 with hn
  have hL : Summable fun v : latOf N => ‖v‖⁻¹ ^ n := ZLattice.summable_norm_pow_inv (latOf N) n (Nat.lt_succ_self _)
  set f : ℕ := Fintype.card (Emb F) with hf
  set K : ℝ := ((2 * f + n).factorial : ℝ) / (2 * Real.pi * m) ^ (2 * f + n) with hK
  set C : ℝ := K / (nrm 𝔞 * κ) with hC
  have hK0 : 0 < K := by positivity
  have hC0 : 0 < C := by positivity
  have key : ∀ ν b : F, ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ν ≠ 0 → b ≠ 0 → (∀ τ : Emb F, 0 < τ (ν * b)) →
      ‖qTerm 𝔞 2 z (ν, b)‖ ≤
        C * ((|((Algebra.norm ℚ b : ℚ) : ℝ)| ^ 2)⁻¹ * ‖remb F (ν * b)‖⁻¹ ^ n) := by
    intro ν b hν hν0 hb0 hpos
    set ξ := ν * b with hξ
    set s := ∑ τ : Emb F, τ ξ with hs_def
    set A := |((Algebra.norm ℚ ν : ℚ) : ℝ)| with hA_def
    set B := |((Algebra.norm ℚ b : ℚ) : ℝ)| with hB_def
    set w := ‖remb F ξ‖ with hw_def
    have hs : 0 < s := Finset.sum_pos (fun τ _ => hpos τ) ⟨τ₀, Finset.mem_univ _⟩
    have hA : κ ≤ A := hκν ν hν hν0
    have hA0 : 0 < A := hκ.trans_le hA
    have hB0 : 0 < B := by
      rw [hB_def, abs_pos, Rat.cast_ne_zero]; exact (Algebra.norm_ne_zero_iff).2 hb0
    have hw0 : 0 < w := by
      rw [hw_def, norm_pos_iff]
      intro h
      have := congrArg (fun v : RSp F => v τ₀) h
      have h3 : τ₀ ξ = 0 := by simpa using this
      have h2 := hpos τ₀
      linarith
    have hws : w ≤ s := by
      rw [hw_def, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.2 ⟨hs.le, ?_⟩
      calc ∑ τ, ‖(remb F ξ) τ‖ ^ 2 = ∑ τ : Emb F, (τ ξ) ^ 2 := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [remb_apply, Real.norm_eq_abs, sq_abs]
        _ ≤ (∑ τ : Emb F, τ ξ) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun τ _ => (hpos τ).le
    have hAB : A * B ≤ s ^ f := by
      have h2 := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ξ
      rw [← Complex.ofReal_prod] at h2
      have h3 := Complex.ofReal_injective h2
      have h1 : A * B = ∏ τ : Emb F, τ ξ := by
        rw [hA_def, hB_def, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hξ, h3]
        exact Finset.prod_congr rfl fun τ _ => abs_of_pos (hpos τ)
      rw [h1, hf, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun τ _ => (hpos τ).le)
        (fun τ _ => Finset.single_le_sum (fun τ _ => (hpos τ).le) (Finset.mem_univ τ))
    set E := Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) with hE
    set E' := Real.exp (-((2 * Real.pi * m) * s)) with hE'
    have hEE : E ≤ E' := by
      apply Real.exp_le_exp.2
      have : m * s ≤ ∑ τ, τ ξ * (z τ).im := by
        rw [hs_def, Finset.mul_sum]
        exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hmy τ]
      nlinarith [Real.pi_pos]
    have hKs := pow_mul_exp_neg_le (c := 2 * Real.pi * m) (t := s) (by positivity) hs.le (2 * f + n)
    have hP : (A * B) ^ 2 * w ^ n ≤ s ^ (2 * f + n) := by
      rw [show s ^ (2 * f + n) = (s ^ f) ^ 2 * s ^ n by ring]
      gcongr
    have hE'K : E' * ((A * B) ^ 2 * w ^ n) ≤ K := by
      have hE'0 : 0 ≤ E' := (Real.exp_pos _).le
      calc E' * ((A * B) ^ 2 * w ^ n) ≤ E' * s ^ (2 * f + n) := mul_le_mul_of_nonneg_left hP hE'0
        _ = s ^ (2 * f + n) * E' := mul_comm _ _
        _ ≤ K := hKs
    have hnorm : ‖qTerm 𝔞 2 z (ν, b)‖ = A / nrm 𝔞 * E := by
      rw [qTerm, norm_mul, norm_qPow, Complex.norm_real, Real.norm_eq_abs, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
        abs_of_nonneg (div_nonneg (abs_nonneg _) hnrm.le)]
    have hR : C * ((B ^ 2)⁻¹ * w⁻¹ ^ n) = K / (nrm 𝔞 * κ * B ^ 2 * w ^ n) := by
      rw [hC, inv_pow]
      field_simp
    rw [hnorm, hR, le_div_iff₀ (by positivity)]
    calc A / nrm 𝔞 * E * (nrm 𝔞 * κ * B ^ 2 * w ^ n) = E * (A * κ * B ^ 2 * w ^ n) := by
          field_simp
      _ ≤ E' * (A * A * B ^ 2 * w ^ n) := by
          gcongr
      _ = E' * ((A * B) ^ 2 * w ^ n) := by ring
      _ ≤ K := hE'K
  set e := Equiv.ofBijective (GlobalTheory.HeckeTwoExp.toQ 𝔞 𝔟)
    ⟨GlobalTheory.HeckeTwoExp.toQ_injective 𝔞 𝔟, GlobalTheory.HeckeTwoExp.toQ_surjective 𝔞 𝔟⟩ with he
  let ι : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)} → latOf N :=
    fun c ν => ⟨remb F (ν.1.1 * c.out.1),
      (mem_latOf N _).2 ⟨_, FractionalIdeal.mul_mem_mul ν.1.2.1 c.out.2.1, rfl⟩⟩
  have hι : ∀ c, Function.Injective (ι c) := by
    intro c ν ν' h
    have h1 := congrArg (fun v : latOf N => (v : RSp F) τ₀) h
    simp only [ι, remb_apply] at h1
    have h2 : ν.1.1 * c.out.1 = ν'.1.1 * c.out.1 := τ₀.injective h1
    exact Subtype.ext (Subtype.ext (mul_right_cancel₀ c.out.2.2 h2))
  set Bf : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ :=
    fun c => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| with hBf
  set G : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → ℝ :=
    fun p => C * ((Bf p.1 ^ 2)⁻¹ * ‖ι p.1 p.2‖⁻¹ ^ n) with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [hG]; positivity
  have hbound : ∀ p, ‖qClass 𝔞 𝔟 2 z (e p)‖ ≤ G p := by
    rintro ⟨c, ν⟩
    calc ‖qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩)‖ = ‖qTerm 𝔞 2 z (ν.1.1, c.out.1)‖ :=
          congrArg norm (qClass_mk 𝔞 𝔟 2 z ⟨(ν.1.1, c.out.1), ν.1.2.1, c.out.2.1, ν.2⟩)
      _ ≤ G ⟨c, ν⟩ := key ν.1.1 c.out.1 ν.1.2.1 ν.1.2.2 c.out.2.2 ν.2
  have hGs : Summable G := by
    refine (summable_sigma_of_nonneg hG0).2 ⟨fun c => ?_, ?_⟩
    · exact ((hL.comp_injective (hι c)).mul_left ((Bf c ^ 2)⁻¹)).mul_left C
    · have hZ := GlobalTheory.HeckeTwo.APart.summable_norm_rpow (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (s := 2) one_lt_two
      refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun ν => hG0 ⟨c, ν⟩) (fun c => ?_)
        (hZ.mul_left (C * ∑' v : latOf N, ‖v‖⁻¹ ^ n))
      show ∑' ν, C * ((Bf c ^ 2)⁻¹ * ‖ι c ν‖⁻¹ ^ n) ≤ _
      rw [tsum_mul_left, tsum_mul_left, Real.rpow_neg (abs_nonneg _), Real.rpow_two]
      have hH : ∑' ν, ‖ι c ν‖⁻¹ ^ n ≤ ∑' v : latOf N, ‖v‖⁻¹ ^ n :=
        tsum_comp_le_tsum_of_inj hL (fun _ => by positivity) (hι c)
      have hB : 0 ≤ (Bf c ^ 2)⁻¹ := by positivity
      calc C * ((Bf c ^ 2)⁻¹ * ∑' ν, ‖ι c ν‖⁻¹ ^ n) ≤ C * ((Bf c ^ 2)⁻¹ * ∑' v : latOf N, ‖v‖⁻¹ ^ n) := by
            gcongr
        _ = _ := by simp only [hBf]; ring
  refine Summable.of_norm ?_
  rw [← e.summable_iff]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hGs

end GlobalTheory.HeckeTwoSum

/- English proof (translation)
Introduce `_ _ _ _ 𝔞 𝔟 z hz` and use `GlobalTheory.HeckeTwoSum.summable_qClass_two 𝔞 𝔟 z hz`.
-/
theorem GlobalTheory.HeckeTwoSum.summable_qClass : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) :=
  fun _ _ _ _ 𝔞 𝔟 z hz => GlobalTheory.HeckeTwoSum.summable_qClass_two 𝔞 𝔟 z hz
