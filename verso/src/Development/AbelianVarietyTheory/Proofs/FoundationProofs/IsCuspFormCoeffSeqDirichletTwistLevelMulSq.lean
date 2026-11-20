import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.CharTwist

/- English proof (translation)
Use `⟨fun u => (M : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩` and prove the remaining obligations. Establish `h` using `ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n`. Rewrite `h` using `[LinearEquiv.symm_apply_apply]`. Rewrite using `[h, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨d, rfl⟩` from `hd`. Establish `h` using `ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)`. Simplify using `only [map_mul] at h`.

Rewrite `h` using `[ZMod.dft_const_mul, Units.inv_mul_cancel_left]`. Simplify using `only [← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_coeffs {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) :
    ∃ c : ZMod M → ℂ, (∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod M, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (M : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

/- English proof (translation)
Take `⟨C, A, hC⟩` from `h`. Use `set q : ℂ := cexp (2 * π * Complex.I * τ) with hq`. Establish `hq1 : ‖q‖ < 1` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one τ`. Establish `hq0 : ‖q‖ ≠ 0` using `norm_ne_zero_iff.2 (Complex.exp_ne_zero _)`. Establish `h1 : Summable fun n : ℕ => (n : ℝ) ^ A * ‖q‖ ^ n` using `summable_pow_mul_geometric_of_norm_lt_one A (by rwa [norm_norm])`.

Establish `h2` using `((summable_nat_add_iff 1).2 h1).mul_left (C * ‖q‖⁻¹)`. Use `Summable.of_norm_bounded h2 fun n => ?_` and prove the remaining obligations. Establish `e : cexp (2 * π * Complex.I * n * τ) = q ^ n`. Rewrite using `[hq, ← Complex.exp_nat_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma summable_of_polyB {a : ℕ → ℂ} (h : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) := by
  obtain ⟨C, A, hC⟩ := h
  set q : ℂ := cexp (2 * π * Complex.I * τ) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 (Complex.exp_ne_zero _)
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ A * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rwa [norm_norm])
  have h2 := ((summable_nat_add_iff 1).2 h1).mul_left (C * ‖q‖⁻¹)
  refine Summable.of_norm_bounded h2 fun n => ?_
  have e : cexp (2 * π * Complex.I * n * τ) = q ^ n := by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; ring
  rw [e, norm_mul, norm_pow]
  calc ‖a n‖ * ‖q‖ ^ n ≤ C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = _ := by push_cast; field_simp; ring

/- English proof (translation)
Establish `a` using `hasSum_sum (s := Finset.univ) fun (u : ZMod M) _ => (summable_of_polyB hg ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)).hasSum.mul_left (c u)`. Unfold `qs`. Rewrite using `[← a.tsum_eq]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[← hc, Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Establish `: u * (m : ZMod M) = ((u.val * m : ℤ) : ZMod M)` using `by simp`. Establish `e2 : ZMod.stdAddChar (u * (m : ZMod M)) * cexp (2 * π * Complex.I * m * τ) = cexp (2 * π * Complex.I * m * (((((u.val : ℤ) : ℝ) / M) +ᵥ τ : ℍ) : ℂ))`. Rewrite using `[this, ZMod.stdAddChar_coe, ← Complex.exp_add, coe_vadd]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qs_twist {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) {c : ZMod M → ℂ}
    (hc : ∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) {g : ℕ → ℂ} (hg : PolyB g) (τ : ℍ) :
    qs (fun n => ψ n * g n) τ = ∑ u : ZMod M, c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) := by
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod M) _ =>
    (summable_of_polyB hg ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)).hasSum.mul_left (c u)
  unfold qs
  rw [← a.tsum_eq]
  refine tsum_congr fun m => ?_
  beta_reduce
  rw [← hc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : u * (m : ZMod M) = ((u.val * m : ℤ) : ZMod M) := by simp
  have e2 : ZMod.stdAddChar (u * (m : ZMod M)) * cexp (2 * π * Complex.I * m * τ) =
      cexp (2 * π * Complex.I * m * (((((u.val : ℤ) : ℝ) / M) +ᵥ τ : ℍ) : ℂ)) := by
    rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  ring

/- English proof (translation)
Take `⟨c, hc⟩` from `hγ`. Move the coercions through the operations in `at hc`. Establish `hd` using `γ.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two, hc]`. Establish `hd'` using `congrArg (Int.cast : ℤ → ZMod M) hd`.

Move the coercions through the operations in `at hd'`. Rewrite `hd'` using `[ZMod.natCast_self]`. Establish `h1 : (M : ℤ) ∣ u * γ 1 1 - v * γ 0 0`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`.

Rewrite using `[h]`. Take the linear combination `(-(u : ZMod M) * ((γ 1 1 : ℤ) : ZMod M)) * hd'`. Take `⟨e, he⟩` from `h1`. Establish `hM : (M : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne M`. Choose the witnesses or unpack the hypotheses as in `⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * N * c * M ∧ δ 0 1 = γ 0 1 + e - u * v * N * c ∧ δ 1 0 = N * M ^ 2 * c ∧ δ 1 1 = γ 1 1 - N * c * v * M := by`.

Use `⟨⟨!![γ 0 0 + u * N * c * M, γ 0 1 + e - u * v * N * c; N * M ^ 2 * c, γ 1 1 - N * c * v * M], ?_⟩, rfl, rfl, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `hd + N * M * c * he`. Establish `hden : ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)`. Rewrite using `[d10, d11, hc, coe_vadd]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨δ, ⟨M ^ 2 * c, by rw [d10]; ring⟩, by rw [d11]; simp, ?_, hden⟩` and prove the remaining obligations. Apply `UpperHalfPlane.ext` to reduce the goal to its premises.

Establish `e1` using `UpperHalfPlane.coe_specialLinearGroup_apply γ τ`. Establish `e2` using `UpperHalfPlane.coe_specialLinearGroup_apply δ (((v : ℝ) / M) +ᵥ τ)`. Simplify using `only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e1 e2`. Establish `hz` using `UpperHalfPlane.denom_ne_zero γ τ`. Rewrite `hz` using `[UpperHalfPlane.denom]`.

Simplify using `at hz`. Establish `he' : (u : ℂ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = M * e` using `by exact_mod_cast he`. Establish `hc' : ((γ 1 0 : ℤ) : ℂ) = N * M ^ 2 * c` using `by exact_mod_cast hc`. Rewrite using `[coe_vadd, e1, e2, hden, eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz, d00, d01, coe_vadd, hc']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `he'`.
-/
lemma vadd_smul {N M : ℕ} [NeZero M] (γ : SL(2, ℤ)) (hγ : ((N * M ^ 2 : ℕ) : ℤ) ∣ γ 1 0) (u v : ℤ)
    (h : (v : ZMod M) = ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u) (τ : ℍ) :
    ∃ δ : SL(2, ℤ), (N : ℤ) ∣ δ 1 0 ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ((u : ℝ) / M) +ᵥ (γ • τ) = δ • (((v : ℝ) / M) +ᵥ τ) ∧
      ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod M) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (M : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod M) * ((γ 1 1 : ℤ) : ZMod M)) * hd'
  obtain ⟨e, he⟩ := h1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * N * c * M ∧
      δ 0 1 = γ 0 1 + e - u * v * N * c ∧ δ 1 0 = N * M ^ 2 * c ∧ δ 1 1 = γ 1 1 - N * c * v * M := by
    refine ⟨⟨!![γ 0 0 + u * N * c * M, γ 0 1 + e - u * v * N * c; N * M ^ 2 * c, γ 1 1 - N * c * v * M], ?_⟩,
      rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * M * c * he
  have hden : ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    rw [d10, d11, hc, coe_vadd]
    push_cast
    field_simp
    ring
  refine ⟨δ, ⟨M ^ 2 * c, by rw [d10]; ring⟩, by rw [d11]; simp, ?_, hden⟩
  apply UpperHalfPlane.ext
  have e1 := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply δ (((v : ℝ) / M) +ᵥ τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e1 e2
  have hz := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hz
  simp at hz
  have he' : (u : ℂ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = M * e := by exact_mod_cast he
  have hc' : ((γ 1 0 : ℤ) : ℂ) = N * M ^ 2 * c := by exact_mod_cast hc
  rw [coe_vadd, e1, e2, hden, eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz, d00, d01, coe_vadd, hc']
  push_cast
  field_simp
  linear_combination he'

/- English proof (translation)
Introduce `k N M χ φ g hM ⟨⟨hp, hi⟩, B, hB⟩`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Take `⟨c, hc1, hc2⟩` from `exists_coeffs φ`. Use `⟨⟨?_, ?_⟩, (∑ u, ‖c u‖ ^ 2) * ∑ _u : ZMod M, B, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨C, A, hC⟩` from `hp`.

Use `⟨C, A, fun n => le_trans ?_ (hC n)⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one φ _)`. Introduce `γ hγ τ`. Establish `hu : IsUnit ((γ 1 1 : ℤ) : ZMod M)`.

Take `⟨e, he⟩` from `hγ`. Establish `dγ` using `congrArg (Int.cast : ℤ → ZMod M) (γ.det_coe)`. Rewrite `dγ` using `[Matrix.det_fin_two, he]`. Move the coercions through the operations in `at dγ`. Rewrite `dγ` using `[ZMod.natCast_self]`.

Conclude with `IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) (by linear_combination dγ)`. Establish `hb : Function.Bijective fun u : ZMod M => ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u` using `((hu.pow 2).unit.mulLeft).bijective`. Rewrite using `[qs_twist φ hc1 hp, qs_twist φ hc1 hp, ← hb.sum_comp fun u : ZMod M => c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Take `⟨δ, h0, h1, h2, h3⟩` from `vadd_smul γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod M) ^ 2 * u).val : ℤ) (by simp) τ`.

Rewrite using `[h2, hi δ h0, h3, hc2 _ u (hu.pow 2)]`. Simplify using `only [ch, h1, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[qs_twist φ hc1 hp]`. Establish `hy : 0 ≤ τ.im ^ k` using `pow_nonneg τ.im_pos.le k`.

Use `set x : ZMod M → ℂ := fun u => qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) with hx`. Establish `h1 : ‖∑ u, c u * x u‖ ≤ ∑ u, ‖c u‖ * ‖x u‖` using `(norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)`. Establish `h2 : ‖∑ u, c u * x u‖ ^ 2 ≤ (∑ u, ‖c u‖ ^ 2) * ∑ u, ‖x u‖ ^ 2` using `(pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)`. Use `(mul_le_mul_of_nonneg_right h2 hy).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Use `mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun u _ => sq_nonneg _)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun u _ => ?_` and prove the remaining obligations. Use `hB ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)` as an intermediate fact. Rewrite `this` using `[vadd_im]`. Then use the resulting hypothesis.
-/
theorem cf_twist : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M →
    CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  intro k N M χ φ g hM ⟨⟨hp, hi⟩, B, hB⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, hc1, hc2⟩ := exists_coeffs φ
  refine ⟨⟨?_, ?_⟩, (∑ u, ‖c u‖ ^ 2) * ∑ _u : ZMod M, B, fun τ => ?_⟩
  · obtain ⟨C, A, hC⟩ := hp
    refine ⟨C, A, fun n => le_trans ?_ (hC n)⟩
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one φ _)
  · intro γ hγ τ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
      obtain ⟨e, he⟩ := hγ
      have dγ := congrArg (Int.cast : ℤ → ZMod M) (γ.det_coe)
      rw [Matrix.det_fin_two, he] at dγ
      push_cast at dγ
      rw [ZMod.natCast_self] at dγ
      exact IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) (by linear_combination dγ)
    have hb : Function.Bijective fun u : ZMod M => ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u :=
      ((hu.pow 2).unit.mulLeft).bijective
    rw [qs_twist φ hc1 hp, qs_twist φ hc1 hp,
      ← hb.sum_comp fun u : ZMod M => c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    obtain ⟨δ, h0, h1, h2, h3⟩ := vadd_smul γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod M) ^ 2 * u).val : ℤ)
      (by simp) τ
    rw [h2, hi δ h0, h3, hc2 _ u (hu.pow 2)]
    simp only [ch, h1, map_pow]
    ring
  · rw [qs_twist φ hc1 hp]
    have hy : 0 ≤ τ.im ^ k := pow_nonneg τ.im_pos.le k
    set x : ZMod M → ℂ := fun u => qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) with hx
    have h1 : ‖∑ u, c u * x u‖ ≤ ∑ u, ‖c u‖ * ‖x u‖ :=
      (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)
    have h2 : ‖∑ u, c u * x u‖ ^ 2 ≤ (∑ u, ‖c u‖ ^ 2) * ∑ u, ‖x u‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    refine (mul_le_mul_of_nonneg_right h2 hy).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun u _ => sq_nonneg _)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    have := hB ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)
    rwa [vadd_im] at this

end GlobalTheory.EisM.CharTwist

end
