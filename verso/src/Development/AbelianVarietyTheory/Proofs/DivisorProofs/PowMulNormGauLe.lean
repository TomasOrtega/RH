import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform

namespace GlobalTheory.RealWeil

/- English proof (translation)
Rewrite using `[norm_gau]`. Establish `hx0 : 0 ≤ ‖v‖` using `norm_nonneg v`. Establish `h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖`. Use `Real.pow_div_factorial_le_exp _ hx0 m` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)]`.

Combine the linear relations using `[mul_comm (Real.exp ‖v‖) (m.factorial : ℝ)]`. Establish `h2 : ‖v‖ + (-(π / 2) * ‖v‖ ^ 2) ≤ 1`. Use polynomial arithmetic with `[Real.pi_gt_three, sq_nonneg ‖v‖, sq_nonneg (‖v‖ - 1 / 3)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_mul_norm_gau_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) (v : V) :
    ‖v‖ ^ m * ‖gau v‖ ≤ m.factorial * Real.exp 1 := by
  rw [norm_gau]
  have hx0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hx0 m
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)] at this
    linarith [mul_comm (Real.exp ‖v‖) (m.factorial : ℝ)]
  have h2 : ‖v‖ + (-(π / 2) * ‖v‖ ^ 2) ≤ 1 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ‖v‖, sq_nonneg (‖v‖ - 1 / 3)]
  calc ‖v‖ ^ m * Real.exp (-(π / 2) * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-(π / 2) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = m.factorial * Real.exp (‖v‖ + (-(π / 2) * ‖v‖ ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ m.factorial * Real.exp 1 := by gcongr

/- English proof (translation)
Unfold `gau`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Establish `h' : ((‖v + t‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ ^ 2 + 2 * ⟪v, t⟫ + ‖t‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[← norm_add_sq_real v t]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gau_add {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v t : V) :
    gau (v + t) = gau v * gau t * cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) := by
  unfold gau
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h' : ((‖v + t‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ ^ 2 + 2 * ⟪v, t⟫ + ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← norm_add_sq_real v t]; push_cast; ring
  rw [h']
  push_cast
  ring

/- English proof (translation)
Establish `e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ))`. Use function extensionality and compare the values at `u`. Simplify using `only [gau]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e]`. Establish `hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2)` using `contDiff_norm_sq ℝ`. Conclude with `Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))`.
-/
theorem contDiff_gau {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContDiff ℝ ∞ (gau : V → ℂ) := by
  have e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp only [gau]
    push_cast
    rfl
  rw [e]
  have hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))

/- English proof (translation)
Set `l : V →L[ℝ] ℂ` to `(-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) - ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))`. Establish `hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)` using `fun t => by`. Simplify using `[l]`. Use `⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by` and prove the remaining obligations. Rewrite using `[hl t]`.

Use the proof step `rfl⟩`. Rewrite using `[hl t]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Complex.norm_real, abs_of_pos Real.pi_pos]`. Use `_ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by gcongr`.

Conclude with `abs_real_inner_le_norm _ _`. Conclude with `(abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])`. Use `_ = 2 * π * ‖v‖ * ‖t‖ := by ring`.
-/
theorem exists_shift_form {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V ≃ₗᵢ[ℝ] V) (v : V) :
    ∃ l : V →L[ℝ] ℂ, ‖l‖ ≤ 2 * π * ‖v‖ ∧
      ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (omJ J v t : ℂ) := by
  let l : V →L[ℝ] ℂ := (-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) -
      ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))
  have hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ) := fun t => by
    simp [l]
  refine ⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by
    rw [hl t]; rfl⟩
  rw [hl t]
  calc ‖-(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)‖
      ≤ ‖-(π : ℂ) * (⟪v, t⟫ : ℝ)‖ + ‖(π : ℂ) * I * (⟪v, J t⟫ : ℝ)‖ := norm_sub_le _ _
    _ = π * |⟪v, t⟫| + π * |⟪v, J t⟫| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    _ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact (abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])
    _ = 2 * π * ‖v‖ * ‖t‖ := by ring

/- English proof (translation)
Use `set F : V → B := fun u => gau u • ρ u f with hF`. Establish `hFs : ContDiff ℝ ∞ F` using `contDiff_gau.smul hf`. Establish `hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z)` using `Complex.contDiff_exp`. Establish `hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Use `⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) * ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩` and prove the remaining obligations.

Take `⟨l, hl, hlt⟩` from `exists_shift_form J v`. Establish `hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t)`. Use function extensionality and compare the values at `t`. Simplify using `only [hF, _root_.smul_apply, map_smul, smul_smul]`. Rewrite using `[add_comm t v, h.2.1 v t f, smul_smul]`.

Use `congr 1`. Establish `key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ))`. Rewrite using `[hlt t, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[gau_add, key]`. Expand and normalize the polynomial expressions, which then agree. Establish `hG : ContDiff ℝ ∞ (fun t => cexp (l t))` using `hE.comp l.contDiff`. Establish `hρ1 : ‖ρ v‖ ≤ 1` using `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]`. Establish `hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖`.

Rewrite using `[ContinuousLinearMap.norm_restrictScalars]`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤ ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i`. Introduce `i`. Establish `e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ)` using `rfl`.

Rewrite using `[e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `gcongr`. Establish `hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) * ‖iteratedFDeriv ℝ (n - i) F 0‖`.

Establish `e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0`. Rewrite using `[iteratedFDeriv_comp_add_right, zero_add]`. Establish `e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) = ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t)` using `rfl`. Rewrite using `[e0, hshift, e2]`. Use `(ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_` and prove the remaining obligations.

Use `mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)` and prove the remaining obligations. Use `(norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity)) (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)`.
-/
theorem decay_gau_smul {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun u => gau u • ρ u f) v‖ ≤ C := by
  set F : V → B := fun u => gau u • ρ u f with hF
  have hFs : ContDiff ℝ ∞ F := contDiff_gau.smul hf
  have hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z) := Complex.contDiff_exp
  have hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩
  obtain ⟨l, hl, hlt⟩ := exists_shift_form J v
  have hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t) := by
    funext t
    simp only [hF, _root_.smul_apply, map_smul, smul_smul]
    rw [add_comm t v, h.2.1 v t f, smul_smul]
    congr 1
    have key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ)) := by
      rw [hlt t, ← Complex.exp_add]; congr 1; ring
    rw [gau_add, key]
    ring
  have hG : ContDiff ℝ ∞ (fun t => cexp (l t)) := hE.comp l.contDiff
  have hρ1 : ‖ρ v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]
  have hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖ := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    calc ‖gau v • ρ v‖ ≤ ‖gau v‖ * ‖ρ v‖ := norm_smul_le _ _
      _ ≤ ‖gau v‖ * 1 := by gcongr
      _ = ‖gau v‖ := mul_one _
  have hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤
      ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i := by
    intro i
    have e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ) := rfl
    rw [e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ := by
    have e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0 := by
      rw [iteratedFDeriv_comp_add_right, zero_add]
    have e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) =
        ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t) := rfl
    rw [e0, hshift, e2]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_
    refine mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity))
      (norm_nonneg _)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖
      ≤ ‖v‖ ^ k * (‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖ * (‖v‖ ^ (k + i) * ‖gau v‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)

/- English proof (translation)
Introduce `V _ _ _ _ _ B _ _ _ J ρ hJ h f hf`. Set `ψ : SchwartzMap V B` to `⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩`. Establish `hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f)` using `SchwartzMap.fourier_coe ψ`. Introduce `n`. Establish `hint` using `(𝓕 ψ).integrable_pow_mul volume n`.

Use `(J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]`.
-/
theorem Sm.good : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ f : B,
    Sm ρ f → Good h f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h f hf
  let ψ : SchwartzMap V B := ⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩
  have hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f) := SchwartzMap.fourier_coe ψ
  intro n
  have hint := (𝓕 ψ).integrable_pow_mul volume n
  refine (J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]

end GlobalTheory.RealWeil
