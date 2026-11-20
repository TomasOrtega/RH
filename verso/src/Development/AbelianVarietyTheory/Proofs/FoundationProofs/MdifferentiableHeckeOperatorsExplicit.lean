import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Establish `: (0 : ℝ) < q` using `by exact_mod_cast hq`. Simplify using `using mul_pos this hz`.
-/
private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

/- English proof (translation)
Establish `: (0 : ℝ) < q` using `by exact_mod_cast hq`. Rewrite using `[Complex.div_natCast_im]`. Simplify using `using div_pos hz this`.
-/
private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

/- English proof (translation)
Rewrite `hf`, the goal using `[UpperHalfPlane.mdifferentiable_iff]`. Establish `h : DifferentiableOn ℂ (fun z : ℂ => (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im}`. Use `DifferentiableOn.const_mul ?_ _` and prove the remaining obligations. Use `DifferentiableOn.fun_sum fun j _ => ?_` and prove the remaining obligations. Conclude with `hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j`.

Use `h.congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]`.
-/
theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

/- English proof (translation)
Rewrite `hf`, the goal using `[UpperHalfPlane.mdifferentiable_iff]`. Establish `h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im}` using `hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz`. Use `h.congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]`.
-/
theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

/- English proof (translation)
Introduce `q k σ f hq hf`. Use `⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩` and prove the remaining obligations. Establish `hs : MDiff (f ∣[k] σ)`. Rewrite using `[ModularForm.SL_slash]`. Conclude with `MDifferentiable.slash hf k _`.

Conclude with `(uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)`.
-/
theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
