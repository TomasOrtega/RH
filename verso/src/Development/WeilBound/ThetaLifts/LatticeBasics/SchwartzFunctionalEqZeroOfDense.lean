import Mathlib
import Development.WeilBound.ThetaLifts.SchwartzMoments.EqZeroOfMoments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open PositivityTheory.ThKOwn (polE eq_zero_PG)

/- English proof (translation)
Establish `hlin : (fun y => (s / (2 * Real.pi)) * r y).HasTemperateGrowth` using `(Function.HasTemperateGrowth.const _).mul hr`. Establish `hc` using `GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hlin`. Establish `h : (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))) = fun y => c * ((GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘ fun y => (s / (2 * Real.pi)) * r y) y`. Use function extensionality and compare the values at `y`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Simplify using `only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]`. Use `congr 2`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`.

Conclude with `(Function.HasTemperateGrowth.const c).mul hc`.
-/
theorem exp_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : E → ℝ}
    (hr : r.HasTemperateGrowth) (c : ℂ) (s : ℝ) :
    (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))).HasTemperateGrowth := by
  have hlin : (fun y => (s / (2 * Real.pi)) * r y).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hr
  have hc := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hlin
  have h : (fun y => c * Complex.exp ((s : ℂ) * Complex.I * (r y : ℂ))) =
      fun y => c * ((GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘ fun y => (s / (2 * Real.pi)) * r y) y := by
    funext y
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 2
    push_cast
    field_simp
  rw [h]
  exact (Function.HasTemperateGrowth.const c).mul hc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Establish `hL : (fun x => L x).HasTemperateGrowth` using `(L : E →L[ℝ] V).hasTemperateGrowth`. Conclude with `(Q.toContinuousBilinearMap).bilinear_hasTemperateGrowth hL hL`.
-/
theorem quad_tg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E ≃L[ℝ] V)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : (fun x => Q (L x) (L x)).HasTemperateGrowth := by
  have hL : (fun x => L x).HasTemperateGrowth := (L : E →L[ℝ] V).hasTemperateGrowth
  exact (Q.toContinuousBilinearMap).bilinear_hasTemperateGrowth hL hL

/- English proof (translation)
Use `set q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Q (L x) (L x) with hqdef`. Establish `hq : Continuous q` using `(quad_tg L Q).1.continuous`. Establish `hscale : ∀ (t : ℝ) x, q (t • x) = t ^ 2 * q x`. Introduce `t x`. Simplify using `only [hqdef, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hq0 : q 0 = 0` using `by simp [hqdef]`. Distinguish the cases in `hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty`. Take `⟨u, hu, hmin⟩` from `(isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne hq.continuousOn`. Establish `hu0 : u ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hu`. Establish `hw : 0 < q u` using `hpos _ (by simpa using hu0)`. Use `⟨q u, hw, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Substitute `hx show _ ≤ q 0` using the available equality. Simplify using `[hq0]`. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.2 hx`. Establish `hm : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`. Simplify using `[norm_smul, hn]`.

Establish `h1 : q u ≤ q (‖x‖⁻¹ • x)` using `hmin hm`. Establish `h2 : q x = ‖x‖ ^ 2 * q (‖x‖⁻¹ • x)`. Rewrite using `[hscale]`. Clear the denominators using the available nonvanishing facts. Use `show _ ≤ q x`.

Rewrite using `[h2, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left h1 (by positivity)`. Use `⟨1, one_pos, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x = 0`. Assume the negation of the conclusion as `hx`.

Conclude with `hne ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.2 hx]⟩`. Substitute `hx` using the available equality. Use `show _ ≤ q 0`. Simplify using `[hq0]`.
-/
theorem lower_bound {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V) (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x x) :
    ∃ w : ℝ, 0 < w ∧ ∀ x, w * ‖x‖ ^ 2 ≤ Q (L x) (L x) := by
  set q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Q (L x) (L x) with hqdef
  have hq : Continuous q := (quad_tg L Q).1.continuous
  have hscale : ∀ (t : ℝ) x, q (t • x) = t ^ 2 * q x := by
    intro t x
    simp only [hqdef, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hq0 : q 0 = 0 := by simp [hqdef]
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne
      hq.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have hw : 0 < q u := hpos _ (by simpa using hu0)
    refine ⟨q u, hw, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      show _ ≤ q 0
      simp [hq0]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hm : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp [norm_smul, hn]
    have h1 : q u ≤ q (‖x‖⁻¹ • x) := hmin hm
    have h2 : q x = ‖x‖ ^ 2 * q (‖x‖⁻¹ • x) := by
      rw [hscale]
      field_simp
    show _ ≤ q x
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.2 hx]⟩
    subst hx
    show _ ≤ q 0
    simp [hq0]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C z => exact ⟨z • f₀, N.smul_mem z hf₀, fun y => by simp [polE]⟩`. Consider the case `add P R hP hR`. Take `⟨F, hF, hFy⟩` from `hP`. Take `⟨G, hG, hGy⟩` from `hR`.

Use `⟨F + G, N.add_mem hF hG, fun y => ?_⟩` and prove the remaining obligations. Establish `h : polE (P + R) (L.symm y) = polE P (L.symm y) + polE R (L.symm y)` using `by simp [polE]`. Rewrite using `[h, add_mul, SchwartzMap.add_apply, hFy, hGy]`. Consider the case `mul_X P p hP`. Take `⟨F, hF, hFy⟩` from `hP`.

Set `l : V →L[ℝ] ℝ` to `(EuclideanSpace.proj (𝕜 := ℝ) p).comp (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin n))`. Establish `hg : (fun y => ((l y : ℝ) : ℂ)).HasTemperateGrowth` using `(Complex.ofRealCLM.comp l).hasTemperateGrowth`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun y => ((l y : ℝ) : ℂ)) F, hmul (l : V →ₗ[ℝ] ℝ) F _ hF (fun y => ?_), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]`. Both sides reduce to the same expression.

Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hFy]`. Establish `h : polE (P * MvPolynomial.X p) (L.symm y) = polE P (L.symm y) * ((l y : ℝ) : ℂ)`. Simplify using `[polE, l]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem poly_mem {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V)
    (N : Submodule ℂ (SchwartzMap V ℂ))
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (f₀ : SchwartzMap V ℂ) (hf₀ : f₀ ∈ N) (P : MvPolynomial (Fin n) ℂ) :
    ∃ F ∈ N, ∀ y, F y = polE P (L.symm y) * f₀ y := by
  induction P using MvPolynomial.induction_on with
  | C z => exact ⟨z • f₀, N.smul_mem z hf₀, fun y => by simp [polE]⟩
  | add P R hP hR =>
    obtain ⟨F, hF, hFy⟩ := hP
    obtain ⟨G, hG, hGy⟩ := hR
    refine ⟨F + G, N.add_mem hF hG, fun y => ?_⟩
    have h : polE (P + R) (L.symm y) = polE P (L.symm y) + polE R (L.symm y) := by simp [polE]
    rw [h, add_mul, SchwartzMap.add_apply, hFy, hGy]
  | mul_X P p hP =>
    obtain ⟨F, hF, hFy⟩ := hP
    let l : V →L[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) p).comp (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin n))
    have hg : (fun y => ((l y : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp l).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y => ((l y : ℝ) : ℂ)) F,
      hmul (l : V →ₗ[ℝ] ℝ) F _ hF (fun y => ?_), fun y => ?_⟩
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
      rfl
    · rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hFy]
      have h : polE (P * MvPolynomial.X p) (L.symm y) = polE P (L.symm y) * ((l y : ℝ) : ℂ) := by
        simp [polE, l]
      rw [h]
      ring

/- English proof (translation)
Set `L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V` to `(toEuclidean (E := V)).symm`. Set `q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ` to `fun x => Q (L x) (L x)`. Set `r : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ` to `fun x => Q' (L x) (L x)`. Establish `hq : q.HasTemperateGrowth` using `quad_tg L Q`. Establish `hr : r.HasTemperateGrowth` using `quad_tg L Q'`.

Take `⟨w, hw, hlow⟩` from `lower_bound L Q hpos`. Set `g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ` to `fun y => c₀ * Complex.exp (((-1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))`. Set `g' : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ` to `fun y => c₀⁻¹ * Complex.exp (((1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))`. Establish `hg : g.HasTemperateGrowth` using `exp_tg hr c₀ (-1)`. Establish `hg' : g'.HasTemperateGrowth` using `exp_tg hr c₀⁻¹ 1`.

Set `A : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ →L[ℂ] SchwartzMap V ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm`. Set `B : SchwartzMap V ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L`. Set `M` to `SchwartzMap.smulLeftCLM ℂ g`. Set `M'` to `SchwartzMap.smulLeftCLM ℂ g'`. Establish `hS : ∀ f, T (A (M f)) = 0`.

Establish `hext` using `eq_zero_PG q hq w hw hlow (T ∘L A ∘L M) (fun f hf' => by`. Take `⟨P, hP⟩` from `hf'`. Take `⟨F, hFN, hF⟩` from `poly_mem L N hmul f₀ hN P`. Establish `hAM : A (M f) = F`. Use extensionality with `y`.

Establish `hy : (L (L.symm y)) = y` using `L.apply_symm_apply y`. Simplify using `only [A, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, M, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hP, hF, hf]`. Simplify using `only [g, q, r, hy]`. Use `push_cast`. Rewrite using `[show -(Q y y : ℂ) - Complex.I * (Q' y y : ℂ) = -1 * Complex.I * (Q' y y : ℂ) + -(Q y y : ℂ) by ring, Complex.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Use `show T (A (M f)) = 0`. Rewrite using `[hAM]`. Conclude with `hT F hFN)`. Conclude with `fun f => DFunLike.congr_fun hext f`.

Use extensionality with `h`. Establish `hinv : A (M (M' (B h))) = h`. Use extensionality with `y`. Simplify using `only [A, B, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, M, M', SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg', smul_eq_mul, L.apply_symm_apply]`. Simplify using `only [g, g']`.

Rewrite using `[← mul_assoc, mul_mul_mul_comm, ← Complex.exp_add]`. Use `push_cast`. Simplify using `[hc]`. Rewrite using `[← hinv]`. Simplify using `using hS _`.
-/
theorem schwartz_functional_eq_zero_of_dense (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (c₀ : ℂ)
    (f₀ : SchwartzMap V ℂ) (hc : c₀ ≠ 0) (hpos : ∀ x, x ≠ 0 → 0 < Q x x)
    (hf : ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)))
    (N : Submodule ℂ (SchwartzMap V ℂ)) (hN : f₀ ∈ N)
    (hmul : ∀ (l : V →ₗ[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ N)
    (T : SchwartzMap V ℂ →L[ℂ] ℂ) (hT : ∀ f ∈ N, T f = 0) : T = 0 := by
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q (L x) (L x)
  let r : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℝ := fun x => Q' (L x) (L x)
  have hq : q.HasTemperateGrowth := quad_tg L Q
  have hr : r.HasTemperateGrowth := quad_tg L Q'
  obtain ⟨w, hw, hlow⟩ := lower_bound L Q hpos
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀ * Complex.exp (((-1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  let g' : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ :=
    fun y => c₀⁻¹ * Complex.exp (((1 : ℝ) : ℂ) * Complex.I * (r y : ℂ))
  have hg : g.HasTemperateGrowth := exp_tg hr c₀ (-1)
  have hg' : g'.HasTemperateGrowth := exp_tg hr c₀⁻¹ 1
  let A : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ →L[ℂ] SchwartzMap V ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
  let B : SchwartzMap V ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
  let M := SchwartzMap.smulLeftCLM ℂ g
  let M' := SchwartzMap.smulLeftCLM ℂ g'
  have hS : ∀ f, T (A (M f)) = 0 := by
    have hext := eq_zero_PG q hq w hw hlow (T ∘L A ∘L M)
      (fun f hf' => by
        obtain ⟨P, hP⟩ := hf'
        obtain ⟨F, hFN, hF⟩ := poly_mem L N hmul f₀ hN P
        have hAM : A (M f) = F := by
          ext y
          have hy : (L (L.symm y)) = y := L.apply_symm_apply y
          simp only [A, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
            M, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hP, hF, hf]
          simp only [g, q, r, hy]
          push_cast
          rw [show -(Q y y : ℂ) - Complex.I * (Q' y y : ℂ) =
            -1 * Complex.I * (Q' y y : ℂ) + -(Q y y : ℂ) by ring, Complex.exp_add]
          ring
        show T (A (M f)) = 0
        rw [hAM]
        exact hT F hFN)
    exact fun f => DFunLike.congr_fun hext f
  ext h
  have hinv : A (M (M' (B h))) = h := by
    ext y
    simp only [A, B, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
      M, M', SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg',
      smul_eq_mul, L.apply_symm_apply]
    simp only [g, g']
    rw [← mul_assoc, mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    simp [hc]
  rw [← hinv]
  simpa using hS _

end GlobalTheory.ThK.Dbl.Dense

end
