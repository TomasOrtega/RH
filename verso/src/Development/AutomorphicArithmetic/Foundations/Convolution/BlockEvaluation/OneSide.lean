import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Unfold `cheb`. Conclude with `(Polynomial.continuous _).comp (by fun_prop)`.
-/
private theorem cheb_cont (η : ℝ) (m : ℕ) : Continuous (cheb η m) := by
  unfold cheb
  exact (Polynomial.continuous _).comp (by fun_prop)

/- English proof (translation)
Establish `e1 : fcalc (fun x : ℝ => 2 * x / η - 1) A = ((2 / η : ℝ) : ℂ) • A - 1`. Unfold `fcalc`. Establish `: (fun x : ℝ => 2 * x / η - 1) = fun x : ℝ => (2 / η) • x - 1`. Use function extensionality and compare the values at `x`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, cfc_sub _ _ A, cfc_smul (2 / η) (fun x : ℝ => x) A, cfc_id' ℝ A, cfc_const_one ℝ A]`. Both sides reduce to the same expression. Establish `e2 : fcalc (cheb η m) A = Polynomial.aeval (((2 / η : ℝ) : ℂ) • A - 1) (Polynomial.Chebyshev.T ℝ m)`. Rewrite using `[← e1]`.

Unfold `fcalc`. Rewrite using `[← cfc_polynomial (R := ℝ) (Polynomial.Chebyshev.T ℝ m) (cfc (fun x : ℝ => 2 * x / η - 1) A), ← cfc_comp' (fun y => (Polynomial.Chebyshev.T ℝ m).eval y) (fun x : ℝ => 2 * x / η - 1) A]`. Both sides reduce to the same expression. Set `φ : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℤ] (H →L[ℂ] H)` to `(ψ.comp C).toIntAlgHom`. Establish `e3 : ψ (chebP η m) = φ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ) (Polynomial.Chebyshev.T ℤ m))`.

Unfold `chebP`. Rewrite using `[← Polynomial.Chebyshev.map_T (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap]`. Both sides reduce to the same expression. Establish `e4 : φ (C ((2 / η : ℝ) : ℂ) * X none - 1) = ((2 / η : ℝ) : ℂ) • A - 1`. Rewrite using `[map_sub, map_mul, map_one]`.

Use `show ψ (C (C _)) * ψ (C (X none)) - 1 = _`. Rewrite using `[hc, hA, smul_mul_assoc, one_mul]`. Rewrite using `[e3, ← Polynomial.aeval_algHom_apply, e4, e2, ← Polynomial.Chebyshev.map_T (algebraMap ℤ ℝ), Polynomial.aeval_map_algebraMap]`.
-/
private theorem ev_cheb {K : Type} [Field K] [NumberField K] {n : ℕ} (ψ : PR K n →+* (H →L[ℂ] H))
    (hc : ∀ c : ℂ, ψ (C (C c)) = c • 1) (A : H →L[ℂ] H) (hA : ψ (C (X none)) = A) (hsa : IsSelfAdjoint A)
    (η : ℝ) (m : ℕ) : ψ (chebP η m) = fcalc (cheb η m) A := by
  have e1 : fcalc (fun x : ℝ => 2 * x / η - 1) A = ((2 / η : ℝ) : ℂ) • A - 1 := by
    unfold fcalc
    have : (fun x : ℝ => 2 * x / η - 1) = fun x : ℝ => (2 / η) • x - 1 := by
      funext x; simp only [smul_eq_mul]; ring
    rw [this, cfc_sub _ _ A, cfc_smul (2 / η) (fun x : ℝ => x) A, cfc_id' ℝ A, cfc_const_one ℝ A]
    rfl
  have e2 : fcalc (cheb η m) A =
      Polynomial.aeval (((2 / η : ℝ) : ℂ) • A - 1) (Polynomial.Chebyshev.T ℝ m) := by
    rw [← e1]
    unfold fcalc
    rw [← cfc_polynomial (R := ℝ) (Polynomial.Chebyshev.T ℝ m) (cfc (fun x : ℝ => 2 * x / η - 1) A),
      ← cfc_comp' (fun y => (Polynomial.Chebyshev.T ℝ m).eval y) (fun x : ℝ => 2 * x / η - 1) A]
    rfl
  let φ : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℤ] (H →L[ℂ] H) := (ψ.comp C).toIntAlgHom
  have e3 : ψ (chebP η m) = φ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)
      (Polynomial.Chebyshev.T ℤ m)) := by
    unfold chebP
    rw [← Polynomial.Chebyshev.map_T (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap]
    rfl
  have e4 : φ (C ((2 / η : ℝ) : ℂ) * X none - 1) = ((2 / η : ℝ) : ℂ) • A - 1 := by
    rw [map_sub, map_mul, map_one]
    show ψ (C (C _)) * ψ (C (X none)) - 1 = _
    rw [hc, hA, smul_mul_assoc, one_mul]
  rw [e3, ← Polynomial.aeval_algHom_apply, e4, e2, ← Polynomial.Chebyshev.map_T (algebraMap ℤ ℝ),
    Polynomial.aeval_map_algebraMap]

/- English proof (translation)
Unfold `fcalc`. Use `norm_cfc_le hc fun x hx => h x ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩` and prove the remaining obligations. Break down `subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs` into its components or cases. Simplify using `[spectrum.of_subsingleton] at hx`. Conclude with `(le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h1)`.
-/
private theorem fcalc_norm_le (A : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (φ : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ c) : ‖fcalc φ A‖ ≤ c := by
  unfold fcalc
  refine norm_cfc_le hc fun x hx => h x ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs
  · simp [spectrum.of_subsingleton] at hx
  · exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h1)

/- English proof (translation)
Establish `hsa : IsSelfAdjoint A` using `isSelfAdjoint_of_nonneg h0`. Establish `hcm : Commute (fcalc χ A) Q` using `hQ.cfc_real χ`. Establish `e1 : fcalc t A = fcalc (fun x => t x * (1 - χ x)) A + fcalc t A * fcalc χ A`. Unfold `fcalc`. Rewrite using `[← cfc_mul t χ A, ← cfc_add A _ _]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Establish `n1 : ‖fcalc (fun x => t x * (1 - χ x)) A‖ ≤ 1`. Use `fcalc_norm_le A h0 h1 _ 1 zero_le_one fun x hx => ?_` and prove the remaining obligations.

Break down `le_total x η with h | h` into its components or cases. Rewrite using `[abs_mul]`. Apply the tactic sequence `have : |1 - χ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ1 x]`. Conclude with `mul_le_one₀ (ht1 x ⟨hx.1, h⟩) (abs_nonneg _) this`. Simplify using `[hχ2 x h]`.

Establish `n2` using `fcalc_norm_le A h0 h1 t c hc ht2`. Establish `hW' : W * (1 - P) = (1 - P) * W` using `((Commute.one_right W).sub_right hW).eq`. Establish `e2 : fcalc t A * Q * W * (1 - P) = (fcalc (fun x => t x * (1 - χ x)) A * (Q * (1 - P)) + fcalc t A * (Q * (fcalc χ A * (1 - P)))) * W`. Rewrite using `[mul_assoc _ W, hW', ← mul_assoc]`. Use `congr 1`.

Use `conv_lhs => rw [e1]`. Rewrite using `[add_mul, add_mul, mul_assoc (fcalc t A), hcm.eq]`. Simplify using `only [mul_assoc]`. Rewrite using `[e2, mul_comm ‖W‖]`. Use `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _))` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))`.
-/
private theorem off_est (A Q W P : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (hQ : Commute A Q) (hW : Commute W P)
    (hP : ‖1 - P‖ ≤ 1) (η c : ℝ) (hc : 0 ≤ c) (t χ : ℝ → ℝ) (ht : Continuous t) (hχ : Continuous χ)
    (ht1 : ∀ x ∈ Set.Icc 0 η, |t x| ≤ 1) (ht2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |t x| ≤ c)
    (hχ1 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ2 : ∀ x ≥ η, χ x = 1) :
    ‖fcalc t A * Q * W * (1 - P)‖ ≤ ‖W‖ * (‖Q‖ + c * ‖Q * (fcalc χ A * (1 - P))‖) := by
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg h0
  have hcm : Commute (fcalc χ A) Q := hQ.cfc_real χ
  have e1 : fcalc t A = fcalc (fun x => t x * (1 - χ x)) A + fcalc t A * fcalc χ A := by
    unfold fcalc
    rw [← cfc_mul t χ A, ← cfc_add A _ _]
    congr 1
    funext x; ring
  have n1 : ‖fcalc (fun x => t x * (1 - χ x)) A‖ ≤ 1 := by
    refine fcalc_norm_le A h0 h1 _ 1 zero_le_one fun x hx => ?_
    rcases le_total x η with h | h
    · rw [abs_mul]
      have : |1 - χ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ1 x]
      exact mul_le_one₀ (ht1 x ⟨hx.1, h⟩) (abs_nonneg _) this
    · simp [hχ2 x h]
  have n2 := fcalc_norm_le A h0 h1 t c hc ht2
  have hW' : W * (1 - P) = (1 - P) * W := ((Commute.one_right W).sub_right hW).eq
  have e2 : fcalc t A * Q * W * (1 - P) =
      (fcalc (fun x => t x * (1 - χ x)) A * (Q * (1 - P)) + fcalc t A * (Q * (fcalc χ A * (1 - P)))) * W := by
    rw [mul_assoc _ W, hW', ← mul_assoc]
    congr 1
    conv_lhs => rw [e1]
    rw [add_mul, add_mul, mul_assoc (fcalc t A), hcm.eq]
    simp only [mul_assoc]
  rw [e2, mul_comm ‖W‖]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _))
  · calc _ ≤ 1 * (‖Q‖ * 1) := (norm_mul_le _ _).trans
          (mul_le_mul n1 ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (norm_nonneg _))) (norm_nonneg _) zero_le_one)
      _ = ‖Q‖ := by ring
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))

omit [CompleteSpace H] in
/- English proof (translation)
Break down `j with _ | j` into its components or cases. Rewrite using `[pow_zero, pow_zero]`. Conclude with `ContinuousLinearMap.norm_id_le`. Conclude with `norm_pow_le' U j.succ_pos`.
-/
private theorem norm_pow_le_clm (U : H →L[ℂ] H) (j : ℕ) : ‖U ^ j‖ ≤ ‖U‖ ^ j := by
  rcases j with _ | j
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' U j.succ_pos

/- English proof (translation)
Establish `hc : V.topologicalClosure = V` using `hV.submodule_topologicalClosure_eq`. Establish `hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V` using `fun v => by rw [hc]`. Conclude with `⟨fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v), fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), isSelfAdjoint_starProjection _⟩`.
-/
private theorem prj_facts (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ IsSelfAdjoint (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  exact ⟨fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v),
    fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), isSelfAdjoint_starProjection _⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨a1, a2, -⟩` from `prj_facts V hV`. Use `congrArg (fun S : H →L[ℂ] H => S v) h` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply, a2 v hv] at this`. Rewrite using `[this]`.

Conclude with `a1 _`.
-/
private theorem pres_of_comm (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (h : T * prj V = prj V * T) : ∀ v ∈ V, T v ∈ V := by
  intro v hv
  obtain ⟨a1, a2, -⟩ := prj_facts V hV
  have := congrArg (fun S : H →L[ℂ] H => S v) h
  simp only [ContinuousLinearMap.mul_apply, a2 v hv] at this
  rw [this]; exact a1 _

/- English proof (translation)
Introduce `v hv`. Use `⟨pres_of_comm V hV T h.eq v hv.1, ?_⟩` and prove the remaining obligations. Establish `h2 : A v = (x : ℂ) • v` using `Module.End.mem_eigenspace_iff.1 hv.2`. Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations. Use `congrArg (fun S : H →L[ℂ] H => S v) hA.eq` as an intermediate fact.

Simplify using `only [ContinuousLinearMap.mul_apply, h2, map_smul] at this`. Conclude with `this.symm`.
-/
private theorem eig_pres (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A T : H →L[ℂ] H) (x : ℝ)
    (h : Commute T (prj V)) (hA : Commute T A) : ∀ v ∈ eigIn V A x, T v ∈ eigIn V A x := by
  intro v hv
  refine ⟨pres_of_comm V hV T h.eq v hv.1, ?_⟩
  have h2 : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv.2
  refine Module.End.mem_eigenspace_iff.2 ?_
  have := congrArg (fun S : H →L[ℂ] H => S v) hA.eq
  simp only [ContinuousLinearMap.mul_apply, h2, map_smul] at this
  exact this.symm

/- English proof (translation)
Establish `hE : IsClosed (eigIn V A x : Set H)` using `(eigIn V A x).closed_of_finiteDimensional`. Take `⟨a1, a2, a3⟩` from `prj_facts _ hE`. Take `⟨-, -, b3⟩` from `prj_facts _ hV`. Establish `hc : (eigIn V A x).topologicalClosure = eigIn V A x` using `hE.submodule_topologicalClosure_eq`. Establish `hT1 : Commute (A * Q) (prj V)` using `hAV.mul_left hQV`.

Establish `hT2 : Commute (A * Q) A` using `(Commute.refl A).mul_left hQA`. Establish `hcomm : (A * Q) ∘L prj (eigIn V A x) = prj (eigIn V A x) ∘L (A * Q)`. Use `K.commProj _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `eig_pres V hV A _ x hT1 hT2`.

Rewrite using `[hc]`. Use `eig_pres V hV A _ x ?_ ?_` and prove the remaining obligations. Use `hT1.star_star` as an intermediate fact. Rewrite `this` using `[b3.star_eq]`. Then use the resulting hypothesis. Use `hT2.star_star` as an intermediate fact.

Rewrite `this` using `[hsa.star_eq]`. Then use the resulting hypothesis. Establish `e : prj (eigIn V A x) ∘L (A * Q * B) ∘L prj (eigIn V A x) = ((x : ℂ) * a) • (prj (eigIn V A x) ∘L B ∘L prj (eigIn V A x))`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun S : H →L[ℂ] H => S (B (prj (eigIn V A x) v))) hcomm`. Establish `hm` using `a1 (B (prj (eigIn V A x) v))`.

Establish `h2 : A (prj (eigIn V A x) (B (prj (eigIn V A x) v))) = (x : ℂ) • _` using `Module.End.mem_eigenspace_iff.1 hm.2`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h1 ⊢`. Rewrite using `[← h1, hQ _ hm, map_smul, h2, smul_smul, mul_comm]`. Unfold `trOn`. Rewrite using `[e]`.

Unfold `trace`. Simplify using `only [ContinuousLinearMap.smul_apply, inner_smul_right]`. Conclude with `tsum_mul_left`.
-/
private theorem trOn_scalar (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A Q B : H →L[ℂ] H) (x : ℝ) (a : ℂ)
    (hsa : IsSelfAdjoint A) (hAV : Commute A (prj V)) (hQV : Commute Q (prj V)) (hQA : Commute Q A)
    [FiniteDimensional ℂ (eigIn V A x)] (hQ : ∀ v ∈ eigIn V A x, Q v = a • v) :
    trOn (eigIn V A x) (A * Q * B) = x * a * trOn (eigIn V A x) B := by
  have hE : IsClosed (eigIn V A x : Set H) := (eigIn V A x).closed_of_finiteDimensional
  obtain ⟨a1, a2, a3⟩ := prj_facts _ hE
  obtain ⟨-, -, b3⟩ := prj_facts _ hV
  have hc : (eigIn V A x).topologicalClosure = eigIn V A x := hE.submodule_topologicalClosure_eq
  have hT1 : Commute (A * Q) (prj V) := hAV.mul_left hQV
  have hT2 : Commute (A * Q) A := (Commute.refl A).mul_left hQA
  have hcomm : (A * Q) ∘L prj (eigIn V A x) = prj (eigIn V A x) ∘L (A * Q) := by
    refine K.commProj _ _ ?_ ?_
    · rw [hc]; exact eig_pres V hV A _ x hT1 hT2
    · rw [hc]
      refine eig_pres V hV A _ x ?_ ?_
      · have := hT1.star_star
        rwa [b3.star_eq] at this
      · have := hT2.star_star
        rwa [hsa.star_eq] at this
  have e : prj (eigIn V A x) ∘L (A * Q * B) ∘L prj (eigIn V A x) =
      ((x : ℂ) * a) • (prj (eigIn V A x) ∘L B ∘L prj (eigIn V A x)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 := congrArg (fun S : H →L[ℂ] H => S (B (prj (eigIn V A x) v))) hcomm
    have hm := a1 (B (prj (eigIn V A x) v))
    have h2 : A (prj (eigIn V A x) (B (prj (eigIn V A x) v))) = (x : ℂ) • _ := Module.End.mem_eigenspace_iff.1 hm.2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h1 ⊢
    rw [← h1, hQ _ hm, map_smul, h2, smul_smul, mul_comm]
  unfold trOn
  rw [e]
  unfold trace
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  exact tsum_mul_left

/- English proof (translation)
Establish `hz0 : 0 ≤ zN` using `zero_le_one.trans hz`. Establish `h1 : C * zN * x ≤ |C| * zN * (u * (q + k * r))`. Use `le_abs_self C` as an intermediate fact. Use `gcongr`. Establish `h2 : C * zN' * y ≤ |C| * zN' * (k * q * u)`.

Use `le_abs_self C` as an intermediate fact. Use `gcongr`. Establish `h3 : q ≤ zN * (q + k * r) + k * zN' * q`. Establish `a : 0 ≤ k * r` using `by positivity`. Establish `b : 0 ≤ k * zN' * q` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : τ * u * q ≤ τ * u * (zN * (q + k * r) + k * zN' * q)` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem final_arith (C τ u q r k zN zN' x y : ℝ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (hz : 1 ≤ zN) (hz' : 0 ≤ zN') (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ u * (q + k * r)) (hy : y ≤ k * q * u) :
    C * zN * x + C * zN' * y + 1 * (q * u * τ) ≤ (|C| + τ) * u * (zN * (q + k * r) + k * zN' * q) := by
  have hz0 : 0 ≤ zN := zero_le_one.trans hz
  have h1 : C * zN * x ≤ |C| * zN * (u * (q + k * r)) := by
    have := le_abs_self C
    gcongr
  have h2 : C * zN' * y ≤ |C| * zN' * (k * q * u) := by
    have := le_abs_self C
    gcongr
  have h3 : q ≤ zN * (q + k * r) + k * zN' * q := by
    have a : 0 ≤ k * r := by positivity
    have b : 0 ≤ k * zN' * q := by positivity
    nlinarith
  have h4 : τ * u * q ≤ τ * u * (zN * (q + k * r) + k * zN' * q) := by gcongr
  nlinarith

end SlopeTestRemainingChoices

set_option maxHeartbeats 1600000 in
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core in
/- English proof (translation)
Introduce `hK hPB hSD hDT hCB hMO hEv K _ _ _ n l hn μ _ θ 𝔰 ev hev hin`. Take `⟨h0, h1, -, -⟩` from `hEv K n hn μ 𝔰.toAmp`. Establish `da` using `hSD K n μ 𝔰.a 𝔰.a_smooth`. Establish `dg` using `hSD K n μ _ 𝔰.g_smooth`. Take `⟨N, hN⟩` from `hK K n μ θ 𝔰.a 𝔰.g (hPB K n μ _) da (hPB K n μ _) dg`.

Use `⟨N, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩` and prove the remaining obligations. Establish `hsa : IsSelfAdjoint 𝔰.toAmp.A` using `isSelfAdjoint_of_nonneg h0`. Establish `hPc : prj (cuspidalL2 μ) = Pc μ`. Unfold `prj Pc`. Use `congr 1`.

Conclude with `(isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq`. Establish `hcP : ∀ T, Inner μ T → Commute T (Pc μ)` using `fun T hT => by`. Rewrite using `[← hPc]`. Conclude with `hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)`. Establish `hcV : ∀ T, Inner μ T → ∀ V, IsSummand μ V → Commute T (prj V)` using `fun T hT V hV => hT _ hV.closed hV.inv`.

Establish `hAin : Inner μ 𝔰.toAmp.A` using `hev.amp ▸ hin _`. Establish `hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A` using `fun Q => hev.amp ▸ (Commute.all Q _).map ev`. Establish `hcomp : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ)`. Rewrite using `[← hPc, ← 𝔰.a_op]`. Conclude with `(opBasics K n μ 𝔰.a).2.2`.

Take `⟨s, hs1, hs2, hs3⟩` from `hCB K n μ θ (hMO K n μ) 𝔰.toAmp.A h0 (fun V hV => pres_of_comm V hV.closed _ (hcV _ hAin V hV).eq) hcomp η hη`. Use `⟨s, hs1, hs2, fun N' => ?_⟩` and prove the remaining obligations. Take `⟨C₀, hC⟩` from `hN N'`. Establish `htc : IsTraceClass (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)`. Use `hDT K n μ 𝔰.a 𝔰.g 1 da dg (Commute.one_left (Pc μ)).eq` as an intermediate fact.

Rewrite `this` using `[𝔰.a_op]`. Conclude with `this`. Use `⟨|C₀| + (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal, fun Q a ha m j Z f hZ hf => ?_⟩` and prove the remaining obligations. Take `⟨hb1, hb2, -⟩` from `FX.cheb_bound η m hη hη1`. Establish `hk : 0 ≤ (4 / η) ^ m` using `by positivity`.

Establish `hch : ev (chebP η m * Q) = fcalc (cheb η m) 𝔰.toAmp.A * ev Q`. Rewrite using `[map_mul, ev_cheb ev hev.const _ hev.amp hsa]`. Establish `hUP : Commute (𝔰.Uq 0 ^ j) (Pc μ)` using `(hcP _ (𝔰.Uq_inner 0)).pow_left j`. Establish `hUA : Commute (𝔰.Uq 0 ^ j) 𝔰.toAmp.A` using `(𝔰.Uq_amp 0).pow_left j`. Establish `hMP : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) (Pc μ)` using `(hcP _ (hin _)).mul_left hUP`.

Establish `k1` using `hC f (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) Z hZ hMP.eq (by rw [𝔰.a_op]; exact hf.1) hf.2`. Establish `hP : ‖1 - Pc μ‖ ≤ 1`. Establish `: 1 - Pc μ = (cuspidalL2 μ)ᗮ.starProjection`. Unfold `Pc`. Rewrite using `[Submodule.starProjection_orthogonal]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.starProjection_norm_le _`. Establish `hu` using `norm_pow_le_clm (𝔰.Uq 0) j`. Establish `k2` using `off_est 𝔰.toAmp.A (ev Q) (𝔰.Uq 0 ^ j) (Pc μ) h0 h1 (hQA Q).symm hUP hP η _ hk (cheb η m) χ (cheb_cont η m) hχ hb1 hb2 hχ1 hχ2`.

Establish `k2'` using `k2.trans (mul_le_mul_of_nonneg_right hu (by positivity))`. Rewrite `k2'` using `[← hch]`. Establish `k3 : ‖ev (chebP η m * Q) * 𝔰.Uq 0 ^ j‖ ≤ (4 / η) ^ m * ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j`. Rewrite using `[hch]`. Use `(norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hu (norm_nonneg _) (by positivity))` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (fcalc_norm_le _ h0 h1 _ _ hk hb2) (norm_nonneg _)`. Establish `eT : Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ = (ev Q * 𝔰.Uq 0 ^ j) * (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)`. Establish `c1 : Commute (ev Q * 𝔰.Uq 0 ^ j) (Pc μ * 𝔰.toAmp.A)` using `((hcP _ (hin Q)).mul_left hUP).mul_right ((hQA Q).mul_left hUA)`. Combine the equalities or inequalities in the displayed calculation. Establish `hTt : IsTraceClass (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ)`.

Rewrite using `[eT]`. Conclude with `htc.comp_left _`. Establish `hTn : (traceNorm (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ)).toReal ≤ ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j * (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal`. Rewrite using `[eT]`. Use `(ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top htc.ne) (traceNorm_comp_left_le _ _)).trans ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.toReal_mul, toReal_enorm]`. Conclude with `mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))) ENNReal.toReal_nonneg`. Establish `k4` using `hs3 (cheb η m) 1 (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) (cheb_cont η m) zero_le_one hb1 (fun V hV v hv => pres_of_comm V hV.closed (𝔰.toAmp.A * ev Q * 𝔰.Uq 0 ^ j) (((hcV _ hAin V hV).mul_left (hcV _ (hin Q) V hV)).mul_left ((hcV _ (𝔰.Uq_inner 0) V hV).pow_left j)).eq _ ((o …`. Establish `e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U ∘L Pc μ)`. Establish `c : Commute (fcalc (cheb η m) 𝔰.toAmp.A) 𝔰.toAmp.A` using `(Commute.refl _).cfc_real _`.

Unfold `cuspTr`. Rewrite using `[hf.1, hch]`. Simplify using `only [← ContinuousLinearMap.mul_def, mul_assoc]`. Rewrite using `[← mul_assoc 𝔰.toAmp.A, ← c.eq, mul_assoc]`. Establish `e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) = ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U)`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hV` using `((hs1 p).1 hp).2.1`. Use `haveI := hs2 p hp`. Rewrite using `[← trOn_scalar p.2 hV.closed 𝔰.toAmp.A (ev Q) _ p.1 (a p) hsa (hcV _ hAin _ hV) (hcV _ (hin Q) _ hV) (hQA Q) (ha p hp)]`. Both sides reduce to the same expression.

Rewrite using `[e2]`. Rewrite `k4` using `[← e1]`. Use `(norm_sub_le_norm_sub_add_norm_sub _ (cuspTr μ θ f) _).trans ((add_le_add k1 (k4.trans (mul_le_mul_of_nonneg_left hTn zero_le_one))).trans ?_)` and prove the remaining obligations. Conclude with `final_arith _ _ _ _ _ _ _ _ _ _ ENNReal.toReal_nonneg (by positivity) (norm_nonneg _) (norm_nonneg _) hk (one_le_pow₀ hZ) (by have := zero_le_one.trans hZ; positivity) (norm_nonneg _) (norm_nonneg _) k2' k3`.
-/
theorem UpperTheory.ConvolutionTheory.Ci.oneSide :
    K.Kern2 → PolyBdAll → SmoothDecay → DecayTraceClass → CuspTrBand → CuspidalMultiplicityOneTotallyComplex → EvEx → OneSide := by
  intro hK hPB hSD hDT hCB hMO hEv K _ _ _ n l hn μ _ θ 𝔰 ev hev hin
  obtain ⟨h0, h1, -, -⟩ := hEv K n hn μ 𝔰.toAmp
  have da := hSD K n μ 𝔰.a 𝔰.a_smooth
  have dg := hSD K n μ _ 𝔰.g_smooth
  obtain ⟨N, hN⟩ := hK K n μ θ 𝔰.a 𝔰.g (hPB K n μ _) da (hPB K n μ _) dg
  refine ⟨N, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  have hsa : IsSelfAdjoint 𝔰.toAmp.A := isSelfAdjoint_of_nonneg h0
  have hPc : prj (cuspidalL2 μ) = Pc μ := by
    unfold prj Pc
    congr 1
    exact (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
  have hcP : ∀ T, Inner μ T → Commute T (Pc μ) := fun T hT => by
    rw [← hPc]; exact hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
  have hcV : ∀ T, Inner μ T → ∀ V, IsSummand μ V → Commute T (prj V) := fun T hT V hV => hT _ hV.closed hV.inv
  have hAin : Inner μ 𝔰.toAmp.A := hev.amp ▸ hin _
  have hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A := fun Q => hev.amp ▸ (Commute.all Q _).map ev
  have hcomp : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ) := by
    rw [← hPc, ← 𝔰.a_op]; exact (opBasics K n μ 𝔰.a).2.2
  obtain ⟨s, hs1, hs2, hs3⟩ := hCB K n μ θ (hMO K n μ) 𝔰.toAmp.A h0
    (fun V hV => pres_of_comm V hV.closed _ (hcV _ hAin V hV).eq) hcomp η hη
  refine ⟨s, hs1, hs2, fun N' => ?_⟩
  obtain ⟨C₀, hC⟩ := hN N'
  have htc : IsTraceClass (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have := hDT K n μ 𝔰.a 𝔰.g 1 da dg (Commute.one_left (Pc μ)).eq
    rw [𝔰.a_op] at this
    exact this
  refine ⟨|C₀| + (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal, fun Q a ha m j Z f hZ hf => ?_⟩
  obtain ⟨hb1, hb2, -⟩ := FX.cheb_bound η m hη hη1
  have hk : 0 ≤ (4 / η) ^ m := by positivity
  have hch : ev (chebP η m * Q) = fcalc (cheb η m) 𝔰.toAmp.A * ev Q := by
    rw [map_mul, ev_cheb ev hev.const _ hev.amp hsa]
  have hUP : Commute (𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (𝔰.Uq_inner 0)).pow_left j
  have hUA : Commute (𝔰.Uq 0 ^ j) 𝔰.toAmp.A := (𝔰.Uq_amp 0).pow_left j
  have hMP : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (hin _)).mul_left hUP
  have k1 := hC f (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) Z hZ hMP.eq (by rw [𝔰.a_op]; exact hf.1) hf.2
  have hP : ‖1 - Pc μ‖ ≤ 1 := by
    have : 1 - Pc μ = (cuspidalL2 μ)ᗮ.starProjection := by
      unfold Pc
      rw [Submodule.starProjection_orthogonal]; rfl
    rw [this]
    exact Submodule.starProjection_norm_le _
  have hu := norm_pow_le_clm (𝔰.Uq 0) j
  have k2 := off_est 𝔰.toAmp.A (ev Q) (𝔰.Uq 0 ^ j) (Pc μ) h0 h1 (hQA Q).symm hUP hP η _ hk (cheb η m) χ (cheb_cont η m) hχ
    hb1 hb2 hχ1 hχ2
  have k2' := k2.trans (mul_le_mul_of_nonneg_right hu (by positivity))
  rw [← hch] at k2'
  have k3 : ‖ev (chebP η m * Q) * 𝔰.Uq 0 ^ j‖ ≤ (4 / η) ^ m * ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j := by
    rw [hch]
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hu (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (fcalc_norm_le _ h0 h1 _ _ hk hb2) (norm_nonneg _)
  have eT : Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ =
      (ev Q * 𝔰.Uq 0 ^ j) * (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have c1 : Commute (ev Q * 𝔰.Uq 0 ^ j) (Pc μ * 𝔰.toAmp.A) :=
      ((hcP _ (hin Q)).mul_left hUP).mul_right ((hQA Q).mul_left hUA)
    calc _ = (Pc μ * 𝔰.toAmp.A) * (ev Q * 𝔰.Uq 0 ^ j) * (Rop μ 𝔰.g * Pc μ) := by simp only [mul_assoc]
      _ = _ := by rw [← c1.eq]; simp only [mul_assoc]
  have hTt : IsTraceClass (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ) := by
    rw [eT]; exact htc.comp_left _
  have hTn : (traceNorm (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ)).toReal ≤
      ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j * (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal := by
    rw [eT]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top htc.ne) (traceNorm_comp_left_le _ _)).trans ?_
    rw [ENNReal.toReal_mul, toReal_enorm]
    exact mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _)))
      ENNReal.toReal_nonneg
  have k4 := hs3 (cheb η m) 1 (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) (cheb_cont η m) zero_le_one hb1
    (fun V hV v hv => pres_of_comm V hV.closed (𝔰.toAmp.A * ev Q * 𝔰.Uq 0 ^ j)
      (((hcV _ hAin V hV).mul_left (hcV _ (hin Q) V hV)).mul_left ((hcV _ (𝔰.Uq_inner 0) V hV).pow_left j)).eq _
      ((opBasics K n μ 𝔰.g).1 V hV v hv)) hTt
  have e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L
      (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U ∘L Pc μ) := by
    have c : Commute (fcalc (cheb η m) 𝔰.toAmp.A) 𝔰.toAmp.A := (Commute.refl _).cfc_real _
    unfold cuspTr
    rw [hf.1, hch]
    simp only [← ContinuousLinearMap.mul_def, mul_assoc]
    rw [← mul_assoc 𝔰.toAmp.A, ← c.eq, mul_assoc]
  have e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p *
      trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) =
      ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1)
        ((𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hV := ((hs1 p).1 hp).2.1
    haveI := hs2 p hp
    rw [← trOn_scalar p.2 hV.closed 𝔰.toAmp.A (ev Q) _ p.1 (a p) hsa (hcV _ hAin _ hV) (hcV _ (hin Q) _ hV) (hQA Q) (ha p hp)]
    rfl
  rw [e2]
  rw [← e1] at k4
  refine (norm_sub_le_norm_sub_add_norm_sub _ (cuspTr μ θ f) _).trans
    ((add_le_add k1 (k4.trans (mul_le_mul_of_nonneg_left hTn zero_le_one))).trans ?_)
  exact final_arith _ _ _ _ _ _ _ _ _ _ ENNReal.toReal_nonneg (by positivity) (norm_nonneg _) (norm_nonneg _) hk
    (one_le_pow₀ hZ) (by have := zero_le_one.trans hZ; positivity) (norm_nonneg _) (norm_nonneg _) k2' k3
