import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Use `set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef`. Establish `hCmeas : ∀ x, MeasurableSet (C x)` using `fun x => (hK.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hCμ : ∀ x, μ (C x) = 1`. Introduce `x`. Simplify using `only [C]`.

Rewrite using `[measure_preimage_mul]`. Conclude with `hμ`. Establish `hconst : ∀ x, ∀ y ∈ C x, F y = F x.out`. Introduce `x y hy`. Establish `hy' : x.out⁻¹ * y ∈ K` using `hy`.

Use `hF x.out _ hy'` as an intermediate fact. Simplify using `using this`. Establish `hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x`. Introduce `x y hy`. Establish `hy' : x.out⁻¹ * y ∈ K` using `hy`.

Establish `h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out` using `(QuotientGroup.eq.mpr hy').symm`. Rewrite using `[h1]`. Conclude with `Quotient.out_eq x`. Establish `hdisj : Pairwise (Function.onFun Disjoint C)`. Introduce `x y hxy`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `z hzx hzy`. Conclude with `hxy ((hmk x z hzx).symm.trans (hmk y z hzy))`. Establish `hnorm : Integrable (fun y => ‖F y‖) μ` using `hint.norm`. Establish `hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖`.

Introduce `x`. Rewrite using `[setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by`. Simplify using `only`. Rewrite using `[hconst x y hy])]`. Rewrite using `[setIntegral_const]`.

Simplify using `[Measure.real, hCμ x]`. Use `summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_` and prove the remaining obligations. Introduce `S`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hterm]`.

Use `_ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by`. Rewrite using `[integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _) (fun x _ => hnorm.integrableOn)]`. Use `_ ≤ ∫ y, ‖F y‖ ∂μ := setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))`.
-/
theorem summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  classical
  set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef
  have hCmeas : ∀ x, MeasurableSet (C x) := fun x =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCμ : ∀ x, μ (C x) = 1 := by
    intro x
    simp only [C]
    rw [measure_preimage_mul]; exact hμ
  have hconst : ∀ x, ∀ y ∈ C x, F y = F x.out := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have := hF x.out _ hy'
    simpa using this
  have hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out :=
      (QuotientGroup.eq.mpr hy').symm
    rw [h1]; exact Quotient.out_eq x
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    exact hxy ((hmk x z hzx).symm.trans (hmk y z hzy))
  have hnorm : Integrable (fun y => ‖F y‖) μ := hint.norm
  have hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖ := by
    intro x
    rw [setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by
      simp only; rw [hconst x y hy])]
    rw [setIntegral_const]
    simp [Measure.real, hCμ x]
  refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_
  intro S
  calc ∑ x ∈ S, ‖F x.out‖ = ∑ x ∈ S, ∫ y in C x, ‖F y‖ ∂μ := by
        simp only [hterm]
    _ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by
        rw [integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _)
          (fun x _ => hnorm.integrableOn)]
    _ ≤ ∫ y, ‖F y‖ ∂μ :=
        setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))

end GlobalTheory
