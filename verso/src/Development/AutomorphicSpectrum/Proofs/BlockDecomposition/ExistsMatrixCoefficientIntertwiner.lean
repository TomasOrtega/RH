import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquareStatement

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

/- English proof (translation)
The claim follows from `(LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y`.
-/
theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

/- English proof (translation)
Establish `h` using `hU.mul g g⁻¹`. Rewrite `h` using `[mul_inv_cancel, hU.one]`. Establish `h2` using `congrArg (fun T : A →L[ℂ] A => T x) h`. Simplify using `using h2.symm`.
-/
theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

/- English proof (translation)
Use `conv_lhs => rw [← isU_apply_inv hU k y]`. Conclude with `isU_inner hU k x _`.
-/
theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

/- English proof (translation)
Establish `h1` using `integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2) Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)`. Establish `h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν`. Simplify using `using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)`. Simplify using `only [Real.rpow_two] at h1`. Establish `hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν` using `integral_nonneg fun _ => by positivity`.

Establish `hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν` using `integral_nonneg fun _ => by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]`.
-/
theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}

omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in

/- English proof (translation)
Establish `key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]`. Take `⟨h1, h2⟩` from `hF.2 w a w a`. Simplify using `only [key] at h1 h2`.

Establish `h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν`. Conclude with `h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)`. Establish `hc : Continuous fun g => ⟪σ g w, a⟫_ℂ` using `(hσ.cont w).inner continuous_const`. Use `⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ)` using `fun x => by`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h2` using `[integral_complex_ofReal, e, e]`. Establish `h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ)`.

Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h4` after adjusting the coercions.
-/
theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
/- English proof (translation)
Take `⟨hb1, hb2⟩` from `GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b`. Establish `hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ` using `continuous_const.inner (hρ.cont v)`. Establish `hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν` using `(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1`. Take `⟨hψ, hψ2⟩` from `coeff_sq ν hσ hF w a`. Use `⟨hφ.integrable_mul hψ, ?_⟩` and prove the remaining obligations.

Use `(norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_` and prove the remaining obligations. Rewrite using `[hψ2]`. Conclude with `mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)`.
-/
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

/- English proof (translation)
Establish `hint` using `fun b a => (form_facts ν hρ hσ hF hv w b a).1`. Establish `hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν` using `integral_nonneg fun _ => norm_nonneg _`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by`. Use `⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩` and prove the remaining obligations. Establish `hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d` using `div_nonneg (by positivity) hF.1.le`.

Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Use `(form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow, Real.sq_sqrt hq]`. Expand and normalize the polynomial expressions, which then agree. Set `L : B → (A →L[ℂ] ℂ)` to `fun b => LinearMap.mkContinuous { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν map_add' := fun a a' => by`.

Rewrite using `[← integral_add (hint b a) (hint b a')]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[inner_add_right, mul_add]`. Use the proof step `map_smul' := fun t a => by`.

Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[inner_smul_right]`.

Use `ring } (K * ‖b‖) (fun a => hbd b a)`. Set `Tf : B → A` to `fun b => (InnerProductSpace.toDual ℂ A).symm (L b)`. Establish `hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν` using `fun b a => by`. Simplify using `only [Tf, InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression.

Establish `hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖` using `fun b => by`. Establish `h1` using `hbd b (Tf b)`. Rewrite `h1` using `[← hT, inner_self_eq_norm_sq_to_K]`. Distinguish the cases in `h0 : ‖Tf b‖ = 0`. Rewrite using `[h0]`.

Check the signs of the components of the expression. Establish `h2 : 0 < ‖Tf b‖` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)`. Establish `h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖`. Simplify `h1` using `[sq]`. Conclude with `le_of_mul_le_mul_right h3 h2`.

Use `⟨LinearMap.mkContinuous { toFun := Tf map_add' := fun b b' => ext_inner_right ℂ fun a => by` and prove the remaining obligations. Rewrite using `[inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[inner_add_left, add_mul]`.

Use the proof step `map_smul' := fun t b => ext_inner_right ℂ fun a => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[inner_smul_left, hT, hT, ← integral_const_mul]`. Use `congr 1`. Use extensionality with `g`.

Rewrite using `[inner_smul_left]`. Use `ring } K hTb, fun b a => ?_⟩`. Conclude with `hT b a`.
-/
theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

/- English proof (translation)
Introduce `Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h`. Take `⟨T, hT⟩` from `exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w`. Establish `hk : ∀ k b, T (ρ k b) = σ k (T b)` using `fun k b => ext_inner_right ℂ fun a => by`. Rewrite using `[hT, isU_inner_left hσ k, hT]`. Use `(integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans (integral_congr_ae (ae_of_all _ fun g => ?_))` and prove the remaining obligations.

Simplify using `only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]`. Rewrite using `[isU_inner hρ, isU_inner_left hσ]`. Establish `hv' : T v = (c : ℂ) • w` using `ext_inner_right ℂ fun a => by`. Rewrite using `[hT, inner_smul_left, Complex.conj_ofReal]`. Establish `h1` using `congrArg (starRingEnd ℂ) (h a)`.

Rewrite `h1` using `[← integral_conj]`. Simplify using `only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1`. Conclude with `h1`. Use `⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hk]`.

Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`. Rewrite using `[ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]`.
-/
theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
