import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Unfold `wt`. Distinguish the cases in `hv : finPartPi v ∈ K`. Rewrite using `[if_pos hv, if_pos (h hv)]`. Rewrite using `[if_neg hv] split_ifs`. Check the signs of the components of the expression.

Conclude with `le_rfl`.
-/
private theorem wt_mono' {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

/- English proof (translation)
Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`. Establish `hgc : Continuous g` using `((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous`. Establish `hgs : HasCompactSupport g` using `((mem_finiteSchwartzBruhatPi F).mp hg).2`.

Take `⟨C₂, h₂⟩` from `hgc.bounded_above_of_compact_support hgs`. Use `⟨tsupport g, hgs.isCompact, fun N => ?_⟩` and prove the remaining obligations. Take `⟨C₁, hC₁, h₁⟩` from `exists_norm_le_inv_one_add_pow φ N`. Use `⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [schwartzBruhatTensorPi, norm_mul]`.

Distinguish the cases in `hx : finPartPi v ∈ tsupport g`. Rewrite using `[wt, if_pos hx]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]`. Simplify using the standard rewrite rules.

Consider the case `zero`. Conclude with `⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩`. Consider the case `add G H _ _ hG hH`. Take `⟨K₁, hK₁, h₁⟩` from `hG`. Take `⟨K₂, hK₂, h₂⟩` from `hH`.

Use `⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩` and prove the remaining obligations. Take `⟨B₁, hB₁, b₁⟩` from `h₁ N`. Take `⟨B₂, hB₂, b₂⟩` from `h₂ N`. Use `⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Consider the case `smul c G _ hG`. Take `⟨K, hK, h⟩` from `hG`. Use `⟨K, hK, fun N => ?_⟩` and prove the remaining obligations. Take `⟨B, hB, b⟩` from `h N`. Use `⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)`.
-/
private theorem majorant {F : Type} [Field F] [NumberField F] {G : V4 F → ℂ}
    (hG : G ∈ schwartzBruhatPi F (Fin 4)) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖G v‖ ≤ B * wt K N v := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi F).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨tsupport g, hgs.isCompact, fun N => ?_⟩
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ N
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi v ∈ tsupport g
    · rw [wt, if_pos hx]
      calc ‖φ (infPartPi v)‖ * ‖g (finPartPi v)‖
          ≤ (C₁ * ((1 + ‖infPartPi v‖) ^ N)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi v‖) ^ N)⁻¹ := by ring
    · rw [wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  | zero =>
    exact ⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, hK₁, h₁⟩ := hG
    obtain ⟨K₂, hK₂, h₂⟩ := hH
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩
    obtain ⟨B₁, hB₁, b₁⟩ := h₁ N
    obtain ⟨B₂, hB₂, b₂⟩ := h₂ N
    refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩
    calc ‖(G + H) v‖ ≤ ‖G v‖ + ‖H v‖ := norm_add_le _ _
      _ ≤ B₁ * wt K₁ N v + B₂ * wt K₂ N v := add_le_add (b₁ v) (b₂ v)
      _ ≤ B₁ * wt (K₁ ∪ K₂) N v + B₂ * wt (K₁ ∪ K₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_left N v) hB₁)
            (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_right N v) hB₂)
      _ = (B₁ + B₂) * wt (K₁ ∪ K₂) N v := by ring
  | smul c G _ hG =>
    obtain ⟨K, hK, h⟩ := hG
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB, b⟩ := h N
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)

/- English proof (translation)
Introduce `F _ _ φ`. Use `⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩` and prove the remaining obligations. Take `⟨K, hK, h⟩` from `majorant φ.2`. Use `⟨K, hK, fun N => ?_⟩` and prove the remaining obligations. Take `⟨B, _, b⟩` from `h N`.

Conclude with `⟨B, fun _ _ v => b v⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtBound :
    ∀ (F : Type) [Field F] [NumberField F], WtBound F := by
  intro F _ _ φ
  refine ⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩
  obtain ⟨K, hK, h⟩ := majorant φ.2
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨B, _, b⟩ := h N
  exact ⟨B, fun _ _ v => b v⟩
