import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Complex

namespace GlobalTheory.ExpSeries

/- English proof (translation)
Establish `h` using `(convexOn_exp.comp_linearMap (Complex.reLm ∘ₗ (L.restrictScalars ℝ))).smul (norm_nonneg c)`. Rewrite `h` using `[Set.preimage_univ]`. Establish `e : (fun z : V => ‖c * cexp (L z)‖) = fun z : V => ‖c‖ • (Real.exp ∘ ⇑(Complex.reLm ∘ₗ (L.restrictScalars ℝ))) z`. Use function extensionality and compare the values at `z`. Simplify using `[Complex.norm_exp]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem convexOn_norm_mul_cexp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (L : V →ₗ[ℂ] ℂ) :
    ConvexOn ℝ Set.univ (fun z : V => ‖c * cexp (L z)‖) := by
  have h := (convexOn_exp.comp_linearMap
    (Complex.reLm ∘ₗ (L.restrictScalars ℝ))).smul (norm_nonneg c)
  rw [Set.preimage_univ] at h
  have e : (fun z : V => ‖c * cexp (L z)‖) = fun z : V =>
      ‖c‖ • (Real.exp ∘ ⇑(Complex.reLm ∘ₗ (L.restrictScalars ℝ))) z := by
    funext z
    simp [Complex.norm_exp]
  rw [e]
  exact h

/- English proof (translation)
Introduce `V _ _ _ J c L`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy a b ha hb hab`. Simplify using `only [Set.mem_ofPred_eq] at hx hy ⊢`. Rewrite `hx`, `hy`, the goal using `[← summable_norm_iff]`.

Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) ((hx.mul_left a).add (hy.mul_left b))` and prove the remaining obligations. Conclude with `(convexOn_norm_mul_cexp (c j) (L j)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab`. Introduce `z0 hz0`. Establish `: FiniteDimensional ℝ V` using `Module.Finite.trans ℂ V`. Take `⟨b, hb0, hb⟩` from `exists_mem_interior_convexHull_affineBasis (mem_interior_iff_mem_nhds.1 hz0)`.

Establish `hsum : Summable fun j => ∑ i, ‖c j * cexp (L j (b i))‖`. Use `summable_sum fun i _ => ?_` and prove the remaining obligations. Establish `: b i ∈ {z : V | Summable fun j => c j * cexp (L j z)}` using `hb (subset_convexHull ℝ _ ⟨i, rfl⟩)`. Conclude with `summable_norm_iff.2 this`. Establish `hd` using `(GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts (F := fun j z => c j * cexp (L j z)) (U := interior (convexHull ℝ (Set.range b))) isOpen_interior (fun j => ((((L j).toContinuousLinearMap.differentiable).cexp).const_mul (c j)).differentiableOn) (fun K hK _ => ⟨_, hsu …`.

Take `⟨y, ⟨i, rfl⟩, hy⟩` from `(convexOn_norm_mul_cexp (c j) (L j)).exists_ge_of_mem_convexHull (Set.subset_univ _) (interior_subset (hK hz))`. Conclude with `hy.trans (Finset.single_le_sum (f := fun i => ‖c j * cexp (L j (b i))‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩)).1`. Conclude with `(hd.differentiableAt (isOpen_interior.mem_nhds hb0)).differentiableWithinAt`.
-/
theorem convex_and_differentiableOn_tsum_cexp :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : Type)
      (c : J → ℂ) (L : J → V →ₗ[ℂ] ℂ),
      Convex ℝ {z : V | Summable fun j => c j * cexp (L j z)} ∧
      DifferentiableOn ℂ (fun z : V => ∑' j, c j * cexp (L j z))
        (interior {z : V | Summable fun j => c j * cexp (L j z)}) := by
  intro V _ _ _ J c L
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [← summable_norm_iff] at hx hy ⊢
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((hx.mul_left a).add (hy.mul_left b))
    exact (convexOn_norm_mul_cexp (c j) (L j)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  · intro z0 hz0
    have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
    obtain ⟨b, hb0, hb⟩ := exists_mem_interior_convexHull_affineBasis
      (mem_interior_iff_mem_nhds.1 hz0)
    have hsum : Summable fun j => ∑ i, ‖c j * cexp (L j (b i))‖ := by
      refine summable_sum fun i _ => ?_
      have : b i ∈ {z : V | Summable fun j => c j * cexp (L j z)} :=
        hb (subset_convexHull ℝ _ ⟨i, rfl⟩)
      exact summable_norm_iff.2 this
    have hd := (GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
      (F := fun j z => c j * cexp (L j z)) (U := interior (convexHull ℝ (Set.range b)))
      isOpen_interior
      (fun j => ((((L j).toContinuousLinearMap.differentiable).cexp).const_mul
        (c j)).differentiableOn)
      (fun K hK _ => ⟨_, hsum, fun j z hz => by
        obtain ⟨y, ⟨i, rfl⟩, hy⟩ := (convexOn_norm_mul_cexp (c j) (L j)).exists_ge_of_mem_convexHull
          (Set.subset_univ _) (interior_subset (hK hz))
        exact hy.trans (Finset.single_le_sum (f := fun i => ‖c j * cexp (L j (b i))‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩)).1
    exact (hd.differentiableAt (isOpen_interior.mem_nhds hb0)).differentiableWithinAt

end GlobalTheory.ExpSeries
