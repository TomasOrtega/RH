import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInteriorEstimateDerivWordPolyLaplacianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralNormProdExpMulLeHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftSmoothingProdExpSmoothCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSobolevRepresentationProdExpStatement
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.DerivBoundIntegral

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

noncomputable def wordEnd (w : List 𝔤) : Module.End ℂ (h.smoothFuns (F := ℂ)) :=
  (w.map (h.rightDerivEnd (F := ℂ))).prod

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [wordEnd]`. Consider the case `cons X w ih`. Simplify using `only [wordEnd, List.map_cons, List.prod_cons, Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd, List.foldr_cons] at ih ⊢`. Rewrite using `[ih]`.
-/
theorem coe_wordEnd (w : List 𝔤) (f : h.smoothFuns (F := ℂ)) :
    ((wordEnd h w f : h.smoothFuns (F := ℂ)) : G → ℂ) = w.foldr h.rightDeriv (f : G → ℂ) := by
  induction w with
  | nil => simp [wordEnd]
  | cons X w ih =>
    simp only [wordEnd, List.map_cons, List.prod_cons, Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
      List.foldr_cons] at ih ⊢
    rw [ih]

/- English proof (translation)
Apply `Subalgebra.list_prod_mem` to reduce the goal to its premises. Introduce `x hx`. Take `⟨X, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `Algebra.subset_adjoin ⟨X, rfl⟩`.
-/
theorem wordEnd_mem (w : List 𝔤) :
    wordEnd h w ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := by
  apply Subalgebra.list_prod_mem
  intro x hx
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
  exact Algebra.subset_adjoin ⟨X, rfl⟩

end GlobalTheory.DerivBoundIntegral

namespace GlobalTheory

open GlobalTheory.DerivBoundIntegral in

/- English proof (translation)
Introduce `𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ`. Take `⟨Kc, hKc, hD⟩` from `GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian 𝔸 G 𝔤 h d b P hP`. Take `⟨ρ, hρ, hH⟩` from `GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar 𝔸 G 𝔤 h d b μ hμ`. Take `⟨C₀, K, hC₀, hK, hHK⟩` from `hH Kc hKc`. Take `⟨N, lw, κ, hκ, hrep⟩` from `GlobalTheory.T.exists_sobolev_representation_prodExp' 𝔸 G 𝔤 h ρ hρ d (⇑b)`.

Use `⟨K, hK, fun l => ?_⟩` and prove the remaining obligations. Establish `hS : ∀ i, ∃ S : ℝ, 0 ≤ S ∧ ∀ t, ‖κ i t‖ ≤ S`. Introduce `i`. Establish `hcs : HasCompactSupport (κ i)` using `(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2`. Take `⟨S, hS⟩` from `(hκ i).1.bounded_above_of_compact_support hcs`.

Conclude with `⟨max S 0, le_max_right _ _, fun t => (hS t).trans (le_max_left _ _)⟩`. Use `choose S hS0 hS using hS`. Use `choose C hC0 hC using fun i => hD (lw i ++ l)`. Use `set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔ`. Use `set A := Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) with hA`.

Establish `hΔmem : Δ ∈ A` using `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)`. Establish `hPmem : Polynomial.aeval Δ P ∈ A`. Use `Polynomial.aeval_algHom_apply A.val (⟨Δ, hΔmem⟩ : A) P` as an intermediate fact. Simplify using `only [Subalgebra.coe_val] at this`. Rewrite using `[this]`.

Conclude with `(Polynomial.aeval (⟨Δ, hΔmem⟩ : A) P).2`. Use `⟨∑ i, C i * (S i * C₀), fun f hf => ?_⟩` and prove the remaining obligations. Use `set I := ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ with hI`. Establish `hfc : Continuous (f : G → ℂ)`. Use `letI := h.chartedSpace`.

Conclude with `ContMDiff.continuous f.2`. Establish `hFs : h.IsSmoothFun ((wordEnd h l f : h.smoothFuns (F` using `ℂ)) : G → ℂ) := (wordEnd h l f).2`. Establish `hrep1` using `hrep _ hFs 1`. Simplify using `only [coe_wordEnd] at hrep1`. Rewrite using `[hrep1]`.

Establish `hterm : ∀ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ)) (1 * h.prodExp (⇑b) t)‖ ≤ C i * (S i * C₀) * I`. Introduce `i`. Take `⟨v, hv, hTv⟩` from `GlobalTheory.T.leftSmoothing_prodExp_smooth_commute 𝔸 G 𝔤 h d (⇑b) (κ i) (hκ i).1 ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2) f`. Establish `hkill : Polynomial.aeval Δ P v = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `y`. Rewrite using `[hTv _ hPmem y, hf]`. Simplify using the standard rewrite rules. Establish `heq : ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ)) (1 * h.prodExp (⇑b) t) = (lw i ++ l).foldr h.rightDeriv (v : G → ℂ) 1`. Establish `e1` using `hTv _ (wordEnd_mem h (lw i ++ l)) 1`.

Simplify using `only [coe_wordEnd] at e1`. Rewrite using `[e1]`. Simplify using `[List.foldr_append]`. Rewrite using `[heq]`. Establish `hvb : ∀ y ∈ Kc, ‖(v : G → ℂ) (1 * y)‖ ≤ S i * C₀ * I`.

Introduce `y hy`. Rewrite using `[one_mul, hv y]`. Establish `hcont : Continuous fun t : Fin d → ℝ => ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖` using `(hfc.comp ((h.continuous_prodExp (⇑b)).mul continuous_const)).norm`. Combine the equalities or inequalities in the displayed calculation. Use `symm`.

Apply `setIntegral_eq_integral_of_forall_compl_eq_zero` to reduce the goal to its premises. Introduce `t ht`. Establish `: κ i t = 0` using `image_eq_zero_of_notMem_tsupport fun h' => ht ((hκ i).2 h')`. Simplify using `[this]`. Use `_ ≤ ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, S i * ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by`.

Apply `integral_mono_of_nonneg` to reduce the goal to its premises. Conclude with `Filter.Eventually.of_forall fun t => norm_nonneg _`. Conclude with `(continuous_const.mul hcont).continuousOn.integrableOn_compact (isCompact_closedBall _ _)`. Use `Filter.Eventually.of_forall fun t => ?_` and prove the remaining obligations. Simplify using `only [norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hS i t) (norm_nonneg _)`. Use `_ = S i * ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := integral_const_mul _ _`. Use `_ ≤ S i * (C₀ * I) := mul_le_mul_of_nonneg_left (hHK _ hfc y hy) (hS0 i)`. Use `_ = S i * C₀ * I := by ring`. Use `hC i v hkill 1 (S i * C₀ * I) hvb` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem derivWord_le_integral_of_aeval_casimir_eq_zero :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  obtain ⟨Kc, hKc, hD⟩ := GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian 𝔸 G 𝔤 h d b P hP
  obtain ⟨ρ, hρ, hH⟩ := GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar 𝔸 G 𝔤 h d b μ hμ
  obtain ⟨C₀, K, hC₀, hK, hHK⟩ := hH Kc hKc
  obtain ⟨N, lw, κ, hκ, hrep⟩ := GlobalTheory.T.exists_sobolev_representation_prodExp' 𝔸 G 𝔤 h ρ hρ d (⇑b)
  refine ⟨K, hK, fun l => ?_⟩
  have hS : ∀ i, ∃ S : ℝ, 0 ≤ S ∧ ∀ t, ‖κ i t‖ ≤ S := by
    intro i
    have hcs : HasCompactSupport (κ i) :=
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2
    obtain ⟨S, hS⟩ := (hκ i).1.bounded_above_of_compact_support hcs
    exact ⟨max S 0, le_max_right _ _, fun t => (hS t).trans (le_max_left _ _)⟩
  choose S hS0 hS using hS
  choose C hC0 hC using fun i => hD (lw i ++ l)
  set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔ
  set A := Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) with hA
  have hΔmem : Δ ∈ A := Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
  have hPmem : Polynomial.aeval Δ P ∈ A := by
    have := Polynomial.aeval_algHom_apply A.val (⟨Δ, hΔmem⟩ : A) P
    simp only [Subalgebra.coe_val] at this
    rw [this]
    exact (Polynomial.aeval (⟨Δ, hΔmem⟩ : A) P).2
  refine ⟨∑ i, C i * (S i * C₀), fun f hf => ?_⟩
  set I := ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ with hI
  have hfc : Continuous (f : G → ℂ) := by
    letI := h.chartedSpace
    exact ContMDiff.continuous f.2

  have hFs : h.IsSmoothFun ((wordEnd h l f : h.smoothFuns (F := ℂ)) : G → ℂ) := (wordEnd h l f).2
  have hrep1 := hrep _ hFs 1
  simp only [coe_wordEnd] at hrep1
  rw [hrep1]
  have hterm : ∀ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
      (1 * h.prodExp (⇑b) t)‖ ≤ C i * (S i * C₀) * I := by
    intro i
    obtain ⟨v, hv, hTv⟩ := GlobalTheory.T.leftSmoothing_prodExp_smooth_commute 𝔸 G 𝔤 h d (⇑b) (κ i) (hκ i).1
      ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hκ i).2) f
    have hkill : Polynomial.aeval Δ P v = 0 := by
      apply Subtype.ext
      funext y
      rw [hTv _ hPmem y, hf]
      simp
    have heq : ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t) = (lw i ++ l).foldr h.rightDeriv (v : G → ℂ) 1 := by
      have e1 := hTv _ (wordEnd_mem h (lw i ++ l)) 1
      simp only [coe_wordEnd] at e1
      rw [e1]
      simp [List.foldr_append]
    rw [heq]
    have hvb : ∀ y ∈ Kc, ‖(v : G → ℂ) (1 * y)‖ ≤ S i * C₀ * I := by
      intro y hy
      rw [one_mul, hv y]
      have hcont : Continuous fun t : Fin d → ℝ => ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ :=
        (hfc.comp ((h.continuous_prodExp (⇑b)).mul continuous_const)).norm
      calc ‖∫ t, κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖
          ≤ ∫ t, ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := norm_integral_le_integral_norm _
        _ = ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖κ i t * (f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            symm
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro t ht
            have : κ i t = 0 := image_eq_zero_of_notMem_tsupport fun h' => ht ((hκ i).2 h')
            simp [this]
        _ ≤ ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              S i * ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun t => norm_nonneg _
            · exact (continuous_const.mul hcont).continuousOn.integrableOn_compact
                (isCompact_closedBall _ _)
            · refine Filter.Eventually.of_forall fun t => ?_
              simp only [norm_mul]
              exact mul_le_mul_of_nonneg_right (hS i t) (norm_nonneg _)
        _ = S i * ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ,
              ‖(f : G → ℂ) (h.prodExp (⇑b) t * y)‖ := integral_const_mul _ _
        _ ≤ S i * (C₀ * I) := mul_le_mul_of_nonneg_left (hHK _ hfc y hy) (hS0 i)
        _ = S i * C₀ * I := by ring
    have := hC i v hkill 1 (S i * C₀ * I) hvb
    calc _ ≤ C i * (S i * C₀ * I) := this
      _ = _ := by ring
  calc ‖∑ i, ∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖
      ≤ ∑ i, ‖∫ t, κ i t * (lw i).foldr h.rightDeriv (l.foldr h.rightDeriv (f : G → ℂ))
        (1 * h.prodExp (⇑b) t)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * (S i * C₀) * I := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, C i * (S i * C₀)) * I := (Finset.sum_mul _ _ _).symm

end GlobalTheory
