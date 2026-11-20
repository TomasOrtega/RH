import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandPairConvolution.Unimod

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

local notation "adj" => ContinuousLinearMap.adjoint

def gram : E →L[ℂ] E := ∫ k, adj (F k) * F k ∂μ

variable {F}

/- English proof (translation)
Establish `hc : Continuous fun k => adj (F k) * F k` using `((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp hF).mul hF`. Conclude with `hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem integrable_gram (hF : Continuous F) : Integrable (fun k => adj (F k) * F k) μ := by
  have hc : Continuous fun k => adj (F k) * F k :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp hF).mul hF
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Establish `h` using `integrable_gram μ hF`. Establish `h1 : gram μ F v = ∫ k, (adj (F k) * F k) v ∂μ` using `ContinuousLinearMap.integral_apply h v`. Establish `h2 : Integrable (fun k => (adj (F k) * F k) v) μ` using `(ContinuousLinearMap.apply ℂ E v).integrable_comp h`. Rewrite using `[h1, ← integral_inner h2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Simplify using `[ContinuousLinearMap.adjoint_inner_right]`.
-/
theorem inner_gram (hF : Continuous F) (v w : E) :
    ⟪w, gram μ F v⟫_ℂ = ∫ k, ⟪F k w, F k v⟫_ℂ ∂μ := by
  have h := integrable_gram μ hF
  have h1 : gram μ F v = ∫ k, (adj (F k) * F k) v ∂μ := ContinuousLinearMap.integral_apply h v
  have h2 : Integrable (fun k => (adj (F k) * F k) v) μ :=
    (ContinuousLinearMap.apply ℂ E v).integrable_comp h
  rw [h1, ← integral_inner h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [ContinuousLinearMap.adjoint_inner_right]

/- English proof (translation)
Rewrite using `[← inner_conj_symm, inner_gram μ hF, inner_gram μ hF, ← integral_conj]`. Simplify using `only [inner_conj_symm]`.
-/
theorem gram_symm (hF : Continuous F) (v w : E) : ⟪gram μ F v, w⟫_ℂ = ⟪v, gram μ F w⟫_ℂ := by
  rw [← inner_conj_symm, inner_gram μ hF, inner_gram μ hF, ← integral_conj]
  simp only [inner_conj_symm]

/- English proof (translation)
Rewrite using `[inner_gram μ hF, ← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `[inner_self_eq_norm_sq_to_K]`.
-/
theorem inner_self_gram (hF : Continuous F) (v : E) :
    ⟪v, gram μ F v⟫_ℂ = ((∫ k, ‖F k v‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [inner_gram μ hF, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [inner_self_eq_norm_sq_to_K]

/- English proof (translation)
The claim follows from `((hF.clm_apply continuous_const).norm).pow 2`.
-/
theorem continuous_norm_apply (hF : Continuous F) (v : E) : Continuous fun k => ‖F k v‖ ^ 2 :=
  ((hF.clm_apply continuous_const).norm).pow 2

/- English proof (translation)
Rewrite using `[ContinuousLinearMap.isPositive_def']`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Conclude with `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun v w => gram_symm μ hF v w`. Rewrite using `[ContinuousLinearMap.reApplyInnerSelf_apply, gram_symm μ hF, inner_self_gram μ hF]`. Simplify using `using integral_nonneg fun k => by positivity`.
-/
theorem gram_isPositive (hF : Continuous F) : (gram μ F).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun v => ?_⟩
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun v w => gram_symm μ hF v w
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, gram_symm μ hF, inner_self_gram μ hF]
    simpa using integral_nonneg fun k => by positivity

/- English proof (translation)
The claim follows from `(ContinuousLinearMap.nonneg_iff_isPositive _).2 (gram_isPositive μ hF)`.
-/
theorem gram_nonneg (hF : Continuous F) : 0 ≤ gram μ F :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).2 (gram_isPositive μ hF)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Assume the negation of the conclusion as `h0`. Establish `hpos : 0 < ∫ k, ‖F k v‖ ^ 2 ∂μ` using `(continuous_norm_apply hF v).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by simpa using h0)`. Establish `h` using `inner_self_gram μ hF v`.

Rewrite `h` using `[hv, inner_zero_right]`. Conclude with `hpos.ne (by exact_mod_cast h)`.
-/
theorem gram_injective (hF : Continuous F) : Function.Injective (gram μ F) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra h0
  have hpos : 0 < ∫ k, ‖F k v‖ ^ 2 ∂μ :=
    (continuous_norm_apply hF v).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by simpa using h0)
  have h := inner_self_gram μ hF v
  rw [hv, inner_zero_right] at h
  exact hpos.ne (by exact_mod_cast h)

/- English proof (translation)
Rewrite using `[ContinuousLinearMap.isUnit_iff_bijective]`. Establish `hi` using `gram_injective μ hF`. Conclude with `⟨hi, LinearMap.injective_iff_surjective (f := (gram μ F : E →ₗ[ℂ] E)).1 hi⟩`.
-/
theorem gram_isUnit (hF : Continuous F) : IsUnit (gram μ F) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hi := gram_injective μ hF
  exact ⟨hi, LinearMap.injective_iff_surjective (f := (gram μ F : E →ₗ[ℂ] E)).1 hi⟩

/- English proof (translation)
Use `haveI := PI.UnitaryGroupMassFormula.GelfConv.isMulRightInvariant_of_compact μ`. Establish `h` using `integrable_gram μ hF`. Establish `e : ∀ h : K, adj (F k) * (adj (F h) * F h) * F k = adj (F (h * k)) * F (h * k)`. Introduce `h`. Simplify using `only [map_mul, ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, star_mul, mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[gram, ← integral_const_mul_of_integrable h, ← integral_mul_const_of_integrable (h.const_mul _)]`. Use `_ = ∫ h, adj (F (h * k)) * F (h * k) ∂μ := by simp only [e]`. Use `_ = gram μ F := integral_mul_right_eq_self (fun h => adj (F h) * F h) k`.
-/
theorem gram_invariant (hF : Continuous F) (k : K) : adj (F k) * gram μ F * F k = gram μ F := by
  haveI := PI.UnitaryGroupMassFormula.GelfConv.isMulRightInvariant_of_compact μ
  have h := integrable_gram μ hF
  have e : ∀ h : K, adj (F k) * (adj (F h) * F h) * F k = adj (F (h * k)) * F (h * k) := by
    intro h
    simp only [map_mul, ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, star_mul, mul_assoc]
  calc adj (F k) * gram μ F * F k = ∫ h, adj (F k) * (adj (F h) * F h) * F k ∂μ := by
        rw [gram, ← integral_const_mul_of_integrable h, ← integral_mul_const_of_integrable (h.const_mul _)]
    _ = ∫ h, adj (F (h * k)) * F (h * k) ∂μ := by simp only [e]
    _ = gram μ F := integral_mul_right_eq_self (fun h => adj (F h) * F h) k

/- English proof (translation)
Establish `h` using `integrable_gram μ hF`. Establish `e1 : ∀ k, adj A * F k = F k * adj A` using `fun k => by`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : ∀ k, adj (F k) * A = A * adj (F k)` using `fun k => by`. Use `congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)) (e1 k)` as an intermediate fact.

Simplify `this` using `[← ContinuousLinearMap.star_eq_adjoint, star_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[gram, integral_const_mul_of_integrable h]`. Use `_ = ∫ k, (adj (F k) * F k) * A ∂μ := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Use `show A * (adj (F k) * F k) = adj (F k) * F k * A`. Rewrite using `[← mul_assoc, ← e2 k, mul_assoc, hc k, mul_assoc]`. Use `_ = gram μ F * A := by rw [gram, integral_mul_const_of_integrable h]`.
-/
theorem gram_commute (hF : Continuous F) (A : E →L[ℂ] E) (hA1 : adj A * A = 1) (hA2 : A * adj A = 1)
    (hc : ∀ k, A * F k = F k * A) : A * gram μ F = gram μ F * A := by
  have h := integrable_gram μ hF
  have e1 : ∀ k, adj A * F k = F k * adj A := fun k => by
    calc adj A * F k = adj A * F k * (A * adj A) := by rw [hA2, mul_one]
      _ = adj A * (A * F k) * adj A := by rw [hc k]; simp only [mul_assoc]
      _ = F k * adj A := by rw [← mul_assoc, hA1, one_mul]
  have e2 : ∀ k, adj (F k) * A = A * adj (F k) := fun k => by
    have := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)) (e1 k)
    simpa [← ContinuousLinearMap.star_eq_adjoint, star_mul] using this
  calc A * gram μ F = ∫ k, A * (adj (F k) * F k) ∂μ := by
        rw [gram, integral_const_mul_of_integrable h]
    _ = ∫ k, (adj (F k) * F k) * A ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        show A * (adj (F k) * F k) = adj (F k) * F k * A
        rw [← mul_assoc, ← e2 k, mul_assoc, hc k, mul_assoc]
    _ = gram μ F * A := by rw [gram, integral_mul_const_of_integrable h]

/- English proof (translation)
Establish `hG` using `gram_nonneg μ hF`. Establish `hcG` using `gram_commute μ hF A hA1 hA2 hc`. Use `set s := CFC.sqrt (gram μ F) with hs`. Establish `hss : s * s = gram μ F` using `CFC.sqrt_mul_sqrt_self _ hG`. Establish `hs0 : 0 ≤ s` using `CFC.sqrt_nonneg _`.

Establish `hb0 : 0 ≤ A * s * adj A`. Use `star_right_conjugate_nonneg hs0 A` as an intermediate fact. Simplify `this` using `[ContinuousLinearMap.star_eq_adjoint]`. Establish `hbb : (A * s * adj A) * (A * s * adj A) = gram μ F`. Combine the equalities or inequalities in the displayed calculation.

Establish `hu : s = A * s * adj A` using `CFC.sqrt_unique hbb hb0`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sqrt_commute (hF : Continuous F) (A : E →L[ℂ] E) (hA1 : adj A * A = 1) (hA2 : A * adj A = 1)
    (hc : ∀ k, A * F k = F k * A) : A * CFC.sqrt (gram μ F) = CFC.sqrt (gram μ F) * A := by
  have hG := gram_nonneg μ hF
  have hcG := gram_commute μ hF A hA1 hA2 hc
  set s := CFC.sqrt (gram μ F) with hs
  have hss : s * s = gram μ F := CFC.sqrt_mul_sqrt_self _ hG
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg _
  have hb0 : 0 ≤ A * s * adj A := by
    have := star_right_conjugate_nonneg hs0 A
    simpa [ContinuousLinearMap.star_eq_adjoint] using this
  have hbb : (A * s * adj A) * (A * s * adj A) = gram μ F := by
    calc (A * s * adj A) * (A * s * adj A) = A * s * (adj A * A) * s * adj A := by simp only [mul_assoc]
      _ = A * (s * s) * adj A := by rw [hA1]; simp only [mul_assoc, mul_one]
      _ = gram μ F * (A * adj A) := by rw [hss, hcG, mul_assoc]
      _ = gram μ F := by rw [hA2, mul_one]
  have hu : s = A * s * adj A := CFC.sqrt_unique hbb hb0
  calc A * s = A * s * (adj A * A) := by rw [hA1, mul_one]
    _ = (A * s * adj A) * A := by simp only [mul_assoc]
    _ = s * A := by rw [← hu]

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

local notation "KU" n => Matrix.unitaryGroup (Fin n) ℂ

instance secondCountable_unitary : SecondCountableTopology (KU n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

/- English proof (translation)
Establish `h : (ExteriorAlgebra.map (Matrix.toLin' (1 : Matrix (Md n) (Md n) ℂ))).toLinearMap = LinearMap.id`. Rewrite using `[Matrix.toLin'_one, ExteriorAlgebra.map_id]`. Both sides reduce to the same expression. Rewrite using `[gamM, h]`. Conclude with `LinearMap.toMatrix_id _`.
-/
theorem gamM_one : gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 := by
  have h : (ExteriorAlgebra.map (Matrix.toLin' (1 : Matrix (Md n) (Md n) ℂ))).toLinearMap = LinearMap.id := by
    rw [Matrix.toLin'_one, ExteriorAlgebra.map_id]; rfl
  rw [gamM, h]
  exact LinearMap.toMatrix_id _

/- English proof (translation)
Establish `e : (ExteriorAlgebra.map (Matrix.toLin' (g * h))).toLinearMap = (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap ∘ₗ (ExteriorAlgebra.map (Matrix.toLin' h)).toLinearMap`. Rewrite using `[Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]`. Both sides reduce to the same expression. Rewrite using `[gamM, e]`. Conclude with `LinearMap.toMatrix_comp _ _ _ _ _`.
-/
theorem gamM_mul (g h : Matrix (Md n) (Md n) ℂ) : gamM (g * h) = gamM g * gamM h := by
  have e : (ExteriorAlgebra.map (Matrix.toLin' (g * h))).toLinearMap =
      (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap ∘ₗ (ExteriorAlgebra.map (Matrix.toLin' h)).toLinearMap := by
    rw [Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]; rfl
  rw [gamM, e]
  exact LinearMap.toMatrix_comp _ _ _ _ _

/- English proof (translation)
Proceed by induction on `w using ExteriorAlgebra.induction with`. Consider the case `algebraMap r => intro φ`. Simplify using `using continuous_const`. Consider the case `ι v`. Introduce `φ`.

Establish `h1 : Continuous fun u : Md n → ℂ => φ (ExteriorAlgebra.ι ℂ u)` using `(φ ∘ₗ ExteriorAlgebra.ι ℂ).continuous_of_finiteDimensional`. Establish `h2 : Continuous fun g : Matrix (Md n) (Md n) ℂ => g *ᵥ v` using `Continuous.matrix_mulVec continuous_id continuous_const`. Establish `e : (fun g : Matrix (Md n) (Md n) ℂ => φ (ExteriorAlgebra.map (Matrix.toLin' g) (ExteriorAlgebra.ι ℂ v))) = fun g => φ (ExteriorAlgebra.ι ℂ (g *ᵥ v))`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h1.comp h2`. Consider the case `add a b ha hb`. Introduce `φ`. Simplify using `only [map_add]`.

Conclude with `(ha φ).add (hb φ)`. Consider the case `mul a b ha hb`. Introduce `φ`. Establish `key : ∀ x y : abelian₂ n, φ (x * y) = ∑ s, ∑ t, ((fb n).coord s x * (fb n).coord t y) * φ (fb n s * fb n t)`. Introduce `x y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[(fb n).sum_repr, (fb n).sum_repr]`. Use `_ = _ := by`. Simplify using `only [Finset.sum_mul_sum, map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul, Module.Basis.coord_apply]`. Establish `e : ∀ g : Matrix (Md n) (Md n) ℂ, φ (ExteriorAlgebra.map (Matrix.toLin' g) (a * b)) = ∑ s, ∑ t, ((fb n).coord s (ExteriorAlgebra.map (Matrix.toLin' g) a) * (fb n).coord t (ExteriorAlgebra.map (Matrix.toLin' g) b)) * φ (fb n s * fb n t)` using `fun g => by rw [map_mul, key]`.

Simplify using `only [e]`. Conclude with `continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun t _ => ((ha _).mul (hb _)).mul continuous_const`.
-/
theorem continuous_map_dual (w : abelian₂ n) : ∀ φ : Module.Dual ℂ (abelian₂ n),
    Continuous fun g : Matrix (Md n) (Md n) ℂ => φ (ExteriorAlgebra.map (Matrix.toLin' g) w) := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r => intro φ; simpa using continuous_const
  | ι v =>
    intro φ
    have h1 : Continuous fun u : Md n → ℂ => φ (ExteriorAlgebra.ι ℂ u) :=
      (φ ∘ₗ ExteriorAlgebra.ι ℂ).continuous_of_finiteDimensional
    have h2 : Continuous fun g : Matrix (Md n) (Md n) ℂ => g *ᵥ v :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have e : (fun g : Matrix (Md n) (Md n) ℂ => φ (ExteriorAlgebra.map (Matrix.toLin' g) (ExteriorAlgebra.ι ℂ v))) =
        fun g => φ (ExteriorAlgebra.ι ℂ (g *ᵥ v)) := by
      funext g; simp
    rw [e]
    exact h1.comp h2
  | add a b ha hb =>
    intro φ
    simp only [map_add]
    exact (ha φ).add (hb φ)
  | mul a b ha hb =>
    intro φ
    have key : ∀ x y : abelian₂ n, φ (x * y) =
        ∑ s, ∑ t, ((fb n).coord s x * (fb n).coord t y) * φ (fb n s * fb n t) := by
      intro x y
      calc φ (x * y) = φ ((∑ s, (fb n).repr x s • fb n s) * (∑ t, (fb n).repr y t • fb n t)) := by
            rw [(fb n).sum_repr, (fb n).sum_repr]
        _ = _ := by
            simp only [Finset.sum_mul_sum, map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul,
              Module.Basis.coord_apply]
    have e : ∀ g : Matrix (Md n) (Md n) ℂ, φ (ExteriorAlgebra.map (Matrix.toLin' g) (a * b)) =
        ∑ s, ∑ t, ((fb n).coord s (ExteriorAlgebra.map (Matrix.toLin' g) a) *
          (fb n).coord t (ExteriorAlgebra.map (Matrix.toLin' g) b)) * φ (fb n s * fb n t) :=
      fun g => by rw [map_mul, key]
    simp only [e]
    exact continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun t _ =>
      ((ha _).mul (hb _)).mul continuous_const

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `e : (fun g : Matrix (Md n) (Md n) ℂ => gamM g i j) = fun g => (fb n).coord i (ExteriorAlgebra.map (Matrix.toLin' g) (fb n j))`. Use function extensionality and compare the values at `g`. Simplify using `[gamM, matL, LinearMap.toMatrix_apply]`. Rewrite using `[e]`.

Conclude with `continuous_map_dual (fb n j) ((fb n).coord i)`.
-/
theorem continuous_gamM : Continuous (gamM (n := n)) := by
  refine continuous_matrix fun i j => ?_
  have e : (fun g : Matrix (Md n) (Md n) ℂ => gamM g i j) =
      fun g => (fb n).coord i (ExteriorAlgebra.map (Matrix.toLin' g) (fb n j)) := by
    funext g
    simp [gamM, matL, LinearMap.toMatrix_apply]
  rw [e]
  exact continuous_map_dual (fb n j) ((fb n).coord i)

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose _`.
-/
theorem hbM_conjTranspose (m : Md n) : (hbM m)ᴴ = hbM m := GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose _

/- English proof (translation)
Establish `h` using `GlobalTheory.CompanionTheory.HbBasis.hOf_coords hH`. Use `conv_lhs => rw [← h]`. Simplify using `only [hOf, LfSt.coords]`. Rewrite using `[← Equiv.sum_comp finProdFinEquiv.symm]`. Simplify using `[hbM, Complex.coe_smul]`.
-/
theorem herm_exp {H : Mat n} (hH : H.IsHermitian) : H = ∑ r : Md n, ((H * hbM r).trace.re : ℝ) • hbM r := by
  have h := GlobalTheory.CompanionTheory.HbBasis.hOf_coords hH
  conv_lhs => rw [← h]
  simp only [hOf, LfSt.coords]
  rw [← Equiv.sum_comp finProdFinEquiv.symm]
  simp [hbM, Complex.coe_smul]

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Use `set H := y * hbM q * yᴴ with hHdef`. Establish `hH : H.IsHermitian`. Simplify using `[Matrix.IsHermitian, hHdef, Matrix.conjTranspose_mul, hbM_conjTranspose, Matrix.mul_assoc]`.

Establish `e : x * y * hbM q * (x * y)ᴴ = ∑ r : Md n, ((H * hbM r).trace.re : ℝ) • (x * hbM r * xᴴ)`. Establish `h1 : x * y * hbM q * (x * y)ᴴ = x * H * xᴴ`. Simplify using `[hHdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[h1]`. Use `conv_lhs => rw [herm_exp hH]`.

Simplify using `[Matrix.mul_sum, Matrix.sum_mul]`. Use `show cf n (x * y * hbM q * (x * y)ᴴ) p = _`. Rewrite using `[e, map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply]`.

Use `show _ = cf n (x * hbM r * xᴴ) p * cf n H r`. Simplify using `[cf, mul_comm]`.
-/
theorem Mt_mul (x y : Mat n) : Mt (x * y) = Mt x * Mt y := by
  ext p q
  rw [Matrix.mul_apply]
  set H := y * hbM q * yᴴ with hHdef
  have hH : H.IsHermitian := by
    simp [Matrix.IsHermitian, hHdef, Matrix.conjTranspose_mul, hbM_conjTranspose, Matrix.mul_assoc]
  have e : x * y * hbM q * (x * y)ᴴ = ∑ r : Md n, ((H * hbM r).trace.re : ℝ) • (x * hbM r * xᴴ) := by
    have h1 : x * y * hbM q * (x * y)ᴴ = x * H * xᴴ := by
      simp [hHdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h1]
    conv_lhs => rw [herm_exp hH]
    simp [Matrix.mul_sum, Matrix.sum_mul]
  show cf n (x * y * hbM q * (x * y)ᴴ) p = _
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, Pi.smul_apply]
  show _ = cf n (x * hbM r * xᴴ) p * cf n H r
  simp [cf, mul_comm]

/- English proof (translation)
Use extensionality with `p q`. Use `show cf n (1 * hbM q * (1 : Mat n)ᴴ) p = _`. Establish `h` using `GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb (finProdFinEquiv.symm q) (finProdFinEquiv.symm p)`. Simplify using `only [cf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_one, mul_one, one_mul, hbM]`. Rewrite using `[h]`.

Distinguish the cases in `e : p = q`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, Matrix.one_apply_eq]`. Simplify using the standard rewrite rules. Establish `: ¬ finProdFinEquiv.symm q = finProdFinEquiv.symm p` using `fun h' => e (finProdFinEquiv.symm.injective h').symm`.

Rewrite using `[if_neg this, Matrix.one_apply_ne e]`. Simplify using the standard rewrite rules.
-/
theorem Mt_one : Mt (1 : Mat n) = 1 := by
  ext p q
  show cf n (1 * hbM q * (1 : Mat n)ᴴ) p = _
  have h := GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb (finProdFinEquiv.symm q) (finProdFinEquiv.symm p)
  simp only [cf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_one, mul_one, one_mul, hbM]
  rw [h]
  by_cases e : p = q
  · subst e
    rw [if_pos rfl, Matrix.one_apply_eq]
    simp
  · have : ¬ finProdFinEquiv.symm q = finProdFinEquiv.symm p :=
      fun h' => e (finProdFinEquiv.symm.injective h').symm
    rw [if_neg this, Matrix.one_apply_ne e]
    simp

/- English proof (translation)
Use `continuous_matrix fun p q => ?_` and prove the remaining obligations. Use `show Continuous fun y : Mat n => cf n (y * hbM q * yᴴ) p`. Simplify using `only [cf, LinearMap.coe_mk, AddHom.coe_mk]`. Establish `: Continuous fun y : Mat n => (y * hbM q * yᴴ * hbM p).trace` using `(((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_trace`. Conclude with `Complex.continuous_ofReal.comp (Complex.continuous_re.comp this)`.
-/
theorem continuous_Mt : Continuous (Mt (n := n)) := by
  refine continuous_matrix fun p q => ?_
  show Continuous fun y : Mat n => cf n (y * hbM q * yᴴ) p
  simp only [cf, LinearMap.coe_mk, AddHom.coe_mk]
  have : Continuous fun y : Mat n => (y * hbM q * yᴴ * hbM p).trace :=
    (((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).matrix_trace
  exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp this)

/- English proof (translation)
Establish `h : IsUnit k.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit`. Establish `e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k` using `Units.ext rfl`. Rewrite using `[Rm, dif_pos h, e]`.
-/
theorem Rm_unitary (lam : Fin n → ℤ) (k : KU n) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dif_pos h, e]

/- English proof (translation)
Rewrite using `[Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]`. Conclude with `LinearMap.toMatrix_comp _ _ _ _ _`.
-/
theorem Rm_mul (lam : Fin n → ℤ) (k k' : KU n) : Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

/- English proof (translation)
Rewrite using `[Rm_unitary, map_one, map_one]`. Conclude with `LinearMap.toMatrix_id _`.
-/
theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : KU n).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Conclude with `⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩`.
-/
theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

/- English proof (translation)
Simplify using `only [Rm_unitary]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.toMatrix_apply]`. Conclude with `(GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp continuous_unitaryIncl`.
-/
theorem continuous_Rm (lam : Fin n → ℤ) : Continuous fun k : KU n => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (congrArg Subtype.val (mul_inv_cancel k))`.
-/
theorem inv_val (k : KU n) : (k.1)⁻¹ = (k⁻¹).1 :=
  Matrix.inv_eq_right_inv (congrArg Subtype.val (mul_inv_cancel k))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_val (k : KU n) : k.1ᴴ = (k⁻¹).1 := rfl

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (by rw [← Rm_mul, mul_inv_cancel, Rm_one])`.
-/
theorem Rm_inv (lam : Fin n → ℤ) (k : KU n) : (Rm lam k.1)⁻¹ = Rm lam (k⁻¹).1 :=
  Matrix.inv_eq_right_inv (by rw [← Rm_mul, mul_inv_cancel, Rm_one])

/- English proof (translation)
The claim follows from `continuous_matrix fun i j => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)`.
-/
theorem continuous_kron {X a b c d : Type*} [TopologicalSpace X] {A : X → Matrix a b ℂ} {B : X → Matrix c d ℂ}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => A x ⊗ₖ B x :=
  continuous_matrix fun i j => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

/- English proof (translation)
Rewrite using `[fr0, rhoW, inv_val, conj_val, Rm_inv]`.
-/
theorem frame_rep_unitary (lam : Fin n → ℤ) (k : KU n) :
    fr0 lam k.1 = gamM (Mt (k⁻¹).1)ᵀ ⊗ₖ ((Rm lam (k⁻¹).1)ᵀ ⊗ₖ (Rm lam (k⁻¹).1)ᵀ) := by
  rw [fr0, rhoW, inv_val, conj_val, Rm_inv]

/- English proof (translation)
Rewrite using `[frame_rep_unitary, frame_rep_unitary, frame_rep_unitary, _root_.mul_inv_rev]`. Establish `hM : (Mt (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Mt (k⁻¹).1)ᵀ * (Mt (k'⁻¹).1)ᵀ`. Rewrite using `[show (k'⁻¹ * k⁻¹ : KU n).1 = (k'⁻¹).1 * (k⁻¹).1 from rfl, Mt_mul, Matrix.transpose_mul]`. Establish `hR : (Rm lam (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Rm lam (k⁻¹).1)ᵀ * (Rm lam (k'⁻¹).1)ᵀ`. Rewrite using `[Rm_mul, Matrix.transpose_mul]`.

Rewrite using `[hM, hR, gamM_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]`.
-/
theorem frame_rep_mul (lam : Fin n → ℤ) (k k' : KU n) : fr0 lam (k * k').1 = fr0 lam k.1 * fr0 lam k'.1 := by
  rw [frame_rep_unitary, frame_rep_unitary, frame_rep_unitary, _root_.mul_inv_rev]
  have hM : (Mt (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Mt (k⁻¹).1)ᵀ * (Mt (k'⁻¹).1)ᵀ := by
    rw [show (k'⁻¹ * k⁻¹ : KU n).1 = (k'⁻¹).1 * (k⁻¹).1 from rfl, Mt_mul, Matrix.transpose_mul]
  have hR : (Rm lam (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Rm lam (k⁻¹).1)ᵀ * (Rm lam (k'⁻¹).1)ᵀ := by
    rw [Rm_mul, Matrix.transpose_mul]
  rw [hM, hR, gamM_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

/- English proof (translation)
Rewrite using `[frame_rep_unitary, inv_one, Rm_one]`. Use `show gamM (Mt (1 : Mat n))ᵀ ⊗ₖ _ = 1`. Rewrite using `[Mt_one, Matrix.transpose_one, gamM_one, Matrix.transpose_one, Matrix.one_kronecker_one, Matrix.one_kronecker_one]`.
-/
theorem frame_rep_one (lam : Fin n → ℤ) : fr0 lam (1 : KU n).1 = 1 := by
  rw [frame_rep_unitary, inv_one, Rm_one]
  show gamM (Mt (1 : Mat n))ᵀ ⊗ₖ _ = 1
  rw [Mt_one, Matrix.transpose_one, gamM_one, Matrix.transpose_one, Matrix.one_kronecker_one,
    Matrix.one_kronecker_one]

/- English proof (translation)
The claim follows from `map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)) A B`.
-/
theorem clm_mul (lam : Fin n → ℤ) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    clm lam (A * B) = clm lam A * clm lam B :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)) A B

/- English proof (translation)
The claim follows from `map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam))`.
-/
theorem clm_one (lam : Fin n → ℤ) : clm lam 1 = 1 :=
  map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam))

/- English proof (translation)
Rewrite using `[← ContinuousLinearMap.star_eq_adjoint]`. Conclude with `(map_star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)) A).symm`.
-/
theorem adjoint_clm (lam : Fin n → ℤ) (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    ContinuousLinearMap.adjoint (clm lam A) = clm lam (star A) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (map_star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)) A).symm

/- English proof (translation)
The claim follows from `(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional`.
-/
theorem continuous_clm (lam : Fin n → ℤ) : Continuous (clm (n := n) lam) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

def fK (lam : Fin n → ℤ) : (KU n) →* (EV n lam →L[ℂ] EV n lam) where
  toFun k := clm lam (fr0 lam k.1)
  map_one' := by rw [frame_rep_one, clm_one]
  map_mul' k k' := by rw [frame_rep_mul, clm_mul]

/- English proof (translation)
Establish `hS : Continuous fun k : KU n => (Rm lam (k⁻¹).1)ᵀ` using `((continuous_Rm lam).comp continuous_inv).matrix_transpose`. Establish `hI : Continuous fun k : KU n => (k⁻¹).1` using `continuous_subtype_val.comp continuous_inv`. Establish `hT : Continuous fun k : KU n => gamM (Mt (k⁻¹).1)ᵀ` using `continuous_gamM.comp (continuous_Mt.comp hI).matrix_transpose`. Establish `h : Continuous fun k : KU n => fr0 lam k.1`. Simplify using `only [frame_rep_unitary]`.

Conclude with `continuous_kron hT (continuous_kron hS hS)`. Conclude with `(continuous_clm lam).comp h`.
-/
theorem continuous_fK (lam : Fin n → ℤ) : Continuous (fK (n := n) lam) := by
  have hS : Continuous fun k : KU n => (Rm lam (k⁻¹).1)ᵀ :=
    ((continuous_Rm lam).comp continuous_inv).matrix_transpose
  have hI : Continuous fun k : KU n => (k⁻¹).1 := continuous_subtype_val.comp continuous_inv
  have hT : Continuous fun k : KU n => gamM (Mt (k⁻¹).1)ᵀ :=
    continuous_gamM.comp (continuous_Mt.comp hI).matrix_transpose
  have h : Continuous fun k : KU n => fr0 lam k.1 := by
    simp only [frame_rep_unitary]
    exact continuous_kron hT (continuous_kron hS hS)
  exact (continuous_clm lam).comp h

/- English proof (translation)
Introduce `n lam`. Establish `hF` using `continuous_fK (n := n) lam`. Establish `hG : gramQ lam = gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam)` using `rfl`. Establish `hQ : sqQ lam = CFC.sqrt (gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam))` using `rfl`. Establish `hG0 : 0 ≤ gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam)` using `gram_nonneg _ hF`.

Establish `hs : sqQ lam * sqQ lam = gramQ lam`. Rewrite using `[hQ, hG]`. Conclude with `CFC.sqrt_mul_sqrt_self _ hG0`. Use `⟨?_, ?_, hs, fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam))` using `gram_isUnit _ hF`.

Rewrite `hu` using `[← hG, ← hs]`. Conclude with `((Commute.refl _).isUnit_mul_iff.1 hu).1`. Rewrite using `[hQ]`. Conclude with `(CFC.sqrt_nonneg _).isSelfAdjoint`. Rewrite using `[hG]`.

Conclude with `gram_invariant _ hF k`. Introduce `U hU hc`. Rewrite using `[hQ]`. Use `sqrt_commute _ hF (clm lam U) ?_ ?_ fun k => ?_` and prove the remaining obligations. Rewrite using `[adjoint_clm, ← clm_mul, Matrix.mem_unitaryGroup_iff'.1 hU, clm_one]`.

Rewrite using `[adjoint_clm, ← clm_mul, Matrix.mem_unitaryGroup_iff.1 hU, clm_one]`. Use `show clm lam U * clm lam (fr0 lam k.1) = clm lam (fr0 lam k.1) * clm lam U`. Rewrite using `[← clm_mul, ← clm_mul, hc k]`.
-/
theorem avg : Avg := by
  intro n lam
  have hF := continuous_fK (n := n) lam
  have hG : gramQ lam = gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam) := rfl
  have hQ : sqQ lam = CFC.sqrt (gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam)) := rfl
  have hG0 : 0 ≤ gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam) := gram_nonneg _ hF
  have hs : sqQ lam * sqQ lam = gramQ lam := by
    rw [hQ, hG]
    exact CFC.sqrt_mul_sqrt_self _ hG0
  refine ⟨?_, ?_, hs, fun k => ?_, ?_⟩
  · have hu : IsUnit (gram (MeasureTheory.Measure.haar : Measure (KU n)) (fK lam)) := gram_isUnit _ hF
    rw [← hG, ← hs] at hu
    exact ((Commute.refl _).isUnit_mul_iff.1 hu).1
  · rw [hQ]
    exact (CFC.sqrt_nonneg _).isSelfAdjoint
  · rw [hG]
    exact gram_invariant _ hF k
  · intro U hU hc
    rw [hQ]
    refine sqrt_commute _ hF (clm lam U) ?_ ?_ fun k => ?_
    · rw [adjoint_clm, ← clm_mul, Matrix.mem_unitaryGroup_iff'.1 hU, clm_one]
    · rw [adjoint_clm, ← clm_mul, Matrix.mem_unitaryGroup_iff.1 hU, clm_one]
    · show clm lam U * clm lam (fr0 lam k.1) = clm lam (fr0 lam k.1) * clm lam U
      rw [← clm_mul, ← clm_mul, hc k]

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
