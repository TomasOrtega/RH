import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.ConvLap

open Set Filter Topology MeasureTheory

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤}

open IsExpLieAlgebra

/- English proof (translation)
The claim follows from `isSmoothFun_comp_inv (h := h) (κ := h.rightDeriv X fun z : G => κ z⁻¹) (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)`.
-/
theorem isSmoothFun_convDeriv {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (X : 𝔤) :
    h.IsSmoothFun (h.convDeriv X κ) :=
  isSmoothFun_comp_inv (h := h) (κ := h.rightDeriv X fun z : G => κ z⁻¹)
    (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

/- English proof (translation)
Establish `hec : Continuous fun t : ℝ => h.expG (t • X)` using `h.continuous_expG.comp (continuous_id.smul continuous_const)`. Establish `hfg : Continuous fun y : G => f (g * y)` using `hfc.comp (continuous_const.mul continuous_id)`. Establish `hκ'c : Continuous fun z : G => κ z⁻¹` using `continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)`. Establish `hDc` using `continuous_rightDeriv_comp_inv hκ X`. Establish `hshift : ∀ t : ℝ, F (g * h.expG (t • X)) = ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ`.

Introduce `t`. Rewrite using `[hconv (g * h.expG (t • X))]`. Use `integral_mul_left_eq_self (μ := μ) (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]`. Establish `hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹) (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t`. Introduce `y t`. Establish `h1` using `h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))`.

Establish `h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹) (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t)`. Rewrite using `[sub_self]`. Conclude with `h1`. Use `(h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]`.

Use `set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) '' (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef`. Establish `hS : IsCompact S` using `((isCompact_closedBall 0 1).prod hκc).image ((hec.comp continuous_fst).mul continuous_snd)`. Establish `hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S → h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0`. Introduce `y t ht hy`. Use `rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X` and prove the remaining obligations.

Simplify `hk` using `[mul_inv_rev]`. Simplify using the standard rewrite rules. Take `⟨M, hM⟩` from `exists_bound_rightDeriv_comp_inv hκ hκc X`. Establish `hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ`. Use `IntegrableOn.integrable_indicator ?_ hS.measurableSet` and prove the remaining obligations.

Conclude with `(hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS`. Establish `hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ`. Establish `: (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ)) (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (F' := fun (t : ℝ) (y : G) => f (g * y) * h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1) (bound …`. Distinguish the cases in `hy : y ∈ S`. Rewrite using `[indicator_of_mem hy, norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)`. Rewrite using `[indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero, norm_zero])`. Use `hbound`. Use the proof step `(Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))`. Establish `hd1 : HasDerivAt (fun t : ℝ => F (g * h.expG (t • X))) (h.rightDeriv X F g) 0` using `h.hasDerivAt_rightDeriv hF X g`.

Establish `hd2` using `key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)`. Rewrite using `[hd1.unique hd2]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `[convDeriv]`.
-/
theorem rightDeriv_eq_integral_convDeriv_of_conv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (hκc : HasCompactSupport κ)
    {f F : G → ℂ} (hfc : Continuous f) (hF : h.IsSmoothFun F)
    (hconv : ∀ x, F x = ∫ y, f (x * y) * κ y ∂μ) (X : 𝔤) (g : G) :
    h.rightDeriv X F g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X
  have hshift : ∀ t : ℝ, F (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]
  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]
  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => F (g * h.expG (t • X))) (h.rightDeriv X F g) 0 :=
    h.hasDerivAt_rightDeriv hF X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end General

section Adelic

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Rewrite using `[uAction_ι_apply]`. Establish `hconv : ∀ x, archSlice (u : AdelicGLn.AdelicGL K n → ℂ) g x = ∫ y, archSlice (ψ : AdelicGLn.AdelicGL K n → ℂ) g (x * y) * κ y ∂μ`. Introduce `x`. Simplify using `only [archSlice_apply, map_mul, ← mul_assoc]`. Conclude with `hu _`.

Rewrite using `[rightDeriv_eq_integral_convDeriv_of_conv hκ hκc (IsExpLieAlgebra.continuous_of_isSmoothFun (ψ.2 g)) (u.2 g) hconv]`. Simplify using `only [archSlice_apply, one_mul]`.
-/
theorem uAction_ι_eq_integral_convDeriv [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] {μ : MeasureTheory.Measure (archGroup K n)} [μ.IsHaarMeasure]
    (ψ u : archSmooth K n) {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsSmoothFun κ) (hκc : HasCompactSupport κ)
    (hu : ∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ)
    (X : (isExpLieAlgebra K n).lieSubalgebra) (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) *
        (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
  rw [uAction_ι_apply]
  have hconv : ∀ x, archSlice (u : AdelicGLn.AdelicGL K n → ℂ) g x =
      ∫ y, archSlice (ψ : AdelicGLn.AdelicGL K n → ℂ) g (x * y) * κ y ∂μ := by
    intro x
    simp only [archSlice_apply, map_mul, ← mul_assoc]
    exact hu _
  rw [rightDeriv_eq_integral_convDeriv_of_conv hκ hκc
    (IsExpLieAlgebra.continuous_of_isSmoothFun (ψ.2 g)) (u.2 g) hconv]
  simp only [archSlice_apply, one_mul]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `J u κ hκ hκc hu`. Use `⟨κ, hκ, hκc, fun g => ?_⟩` and prove the remaining obligations. Simplify `hu g` using `[CuspidalSpectrum.uJ]`.

Consider the case `succ k ih`. Introduce `J u κ hκ hκc hu`. Use `set X := CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis K n (J 0)) with hX`. Take `⟨D, hD, hDc, hrep⟩` from `ih (Fin.tail J) (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u) ((isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ) (isSmoothFun_convDeriv hκ _) (IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _) (fun g => uAction_ι_eq_integral_convDeriv ψ u hκ hκc hu X g)`. Use `⟨D, hD, hDc, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[CuspidalSpectrum.uAction_uJ_succ]`. Conclude with `hrep g`.
-/
theorem exists_kernel_uAction_uJ [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (μ : MeasureTheory.Measure (archGroup K n)) [μ.IsHaarMeasure]
    (ψ : archSmooth K n) (k : ℕ) :
    ∀ (J : Fin k → Fin (CuspidalSpectrum.archDim K n)) (u : archSmooth K n)
      (κ : archGroup K n → ℂ), (isExpLieAlgebra K n).IsSmoothFun κ → HasCompactSupport κ →
      (∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
        ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ) →
      ∃ D : archGroup K n → ℂ, (isExpLieAlgebra K n).IsSmoothFun D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) u :
            ↥(archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * D y ∂μ := by
  induction k with
  | zero =>
    intro J u κ hκ hκc hu
    refine ⟨κ, hκ, hκc, fun g => ?_⟩
    simpa [CuspidalSpectrum.uJ] using hu g
  | succ k ih =>
    intro J u κ hκ hκc hu
    set X := CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis K n (J 0)) with hX
    obtain ⟨D, hD, hDc, hrep⟩ := ih (Fin.tail J)
      (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u)
      ((isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ)
      (isSmoothFun_convDeriv hκ _) (IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _)
      (fun g => uAction_ι_eq_integral_convDeriv ψ u hκ hκc hu X g)
    refine ⟨D, hD, hDc, fun g => ?_⟩
    rw [CuspidalSpectrum.uAction_uJ_succ]
    exact hrep g

/- English proof (translation)
Introduce `K _ _ n ψ d b P hPm hPd hP _ _ μ _ k J`. Take `⟨κ, hκs, hκc, -, hκ⟩` from `(isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd Filter.univ_mem`. Establish `h1 : ∀ g, (ψ : AdelicGLn.AdelicGL K n → ℂ) g = ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ`. Introduce `g`. Use `hκ (sliceL g ψ) (hP g) 1` as an intermediate fact.

Simplify `this` using `[archSlice_apply]`. Take `⟨D, hD, hDc, hrep⟩` from `exists_kernel_uAction_uJ μ ψ k J ψ κ hκs hκc h1`. Conclude with `⟨D, IsExpLieAlgebra.continuous_of_isSmoothFun hD, hDc, hrep⟩`.
-/
theorem exists_conv_uJ_of_aeval_laplacian : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  intro K _ _ n ψ d b P hPm hPd hP _ _ μ _ k J
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P
    hPm hPd Filter.univ_mem
  have h1 : ∀ g, (ψ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ := by
    intro g
    have := hκ (sliceL g ψ) (hP g) 1
    simpa [archSlice_apply] using this
  obtain ⟨D, hD, hDc, hrep⟩ := exists_kernel_uAction_uJ μ ψ k J ψ κ hκs hκc h1
  exact ⟨D, IsExpLieAlgebra.continuous_of_isSmoothFun hD, hDc, hrep⟩

end Adelic

end GlobalTheory.CompanionTheory.HCRep.ConvLap
