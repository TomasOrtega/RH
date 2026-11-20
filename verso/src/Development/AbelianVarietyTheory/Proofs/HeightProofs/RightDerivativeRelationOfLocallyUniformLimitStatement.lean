import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimit
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `n ε F hF m c u hlim y hy`. Establish `hmem : ∀ g : UJ ε, umat g ∈ UJset ε` using `fun g => g.2`. Establish `hcont : Continuous fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)`. Use `continuous_finset_sum _ (fun i _ => ?_)` and prove the remaining obligations. Conclude with `continuous_const.mul (CSm.continuous (CSm.wordF hF (u i)))`.

Establish `key : ∀ φ, IsTest ε φ → ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) = 0`. Introduce `φ hφ`. Use `choose ψ hψ hadj using fun i => exists_adjoint_word (u i) hφ`. Establish `expand : ∀ G, CSm ε G → ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) G (umat g) ∂(muG ε) = ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * G (umat g) ∂(muG ε)`. Introduce `G hG`.

Establish `hfun : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) G (umat g)) = fun g => ∑ i, c i * (φ (umat g) * wordF (u i) G (umat g))`. Use function extensionality and compare the values at `g`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`. Rewrite using `[hfun, MeasureTheory.integral_finset_sum]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[MeasureTheory.integral_const_mul, hadj i G hG]`. Introduce `i _`. Conclude with `(IsTest.integrable hφ (CSm.wordF hG (u i))).const_mul (c i)`. Establish `h1 : CSm ε (fun _ : Mx n => (1 : ℂ))` using `cSm_of_contDiff _ contDiff_const`.

Establish `hint1 : ∀ i, MeasureTheory.Integrable (fun g : UJ ε => ‖ψ i (umat g)‖) (muG ε)`. Introduce `i`. Simplify using `using (IsTest.integrable (hψ i) h1).norm`. Use `set A : Fin m → ℝ := fun i => ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε) with hA`. Use `set B : ℝ := ∑ i, ‖c i‖ * A i with hB`.

Establish `hA0 : ∀ i, 0 ≤ A i` using `fun i => MeasureTheory.integral_nonneg (fun g => norm_nonneg _)`. Establish `hB0 : 0 ≤ B` using `Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA0 i))`. Use `set X := ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) with hX`. Establish `bound : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ δ * B`. Introduce `δ hδ`.

Set `K : Set (UJ ε)` to `⋃ i, tsupport (fun g : UJ ε => ψ i (umat g))`. Establish `hK : IsCompact K` using `isCompact_iUnion (fun i => (hψ i).2.isCompact)`. Establish `hC : IsCompact ((fun g : UJ ε => umat g) '' K)` using `hK.image (umat_emb ε).continuous`. Take `⟨f, hf, hclose, hzero⟩` from `hlim _ hC δ hδ`. Establish `e0 : ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε) = 0`.

Rewrite using `[← expand f hf]`. Establish `hz : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) f (umat g)) = fun _ => 0`. Use function extensionality and compare the values at `g`. Rewrite using `[hzero _ (hmem g), mul_zero]`. Rewrite using `[hz, MeasureTheory.integral_zero]`.

Establish `hXf : X = ∑ i, c i * ((∫ g : UJ ε, ψ i (umat g) * F (umat g) ∂(muG ε)) - ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε))`. Rewrite using `[hX, expand F hF]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]`. Rewrite using `[hXf]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Use `(Finset.sum_le_sum (fun i _ => ?_ : ∀ i ∈ Finset.univ, _ ≤ ‖c i‖ * (δ * A i))).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Use `show _ ≤ δ * ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε)`. Rewrite using `[← MeasureTheory.integral_sub (IsTest.integrable (hψ i) hF) (IsTest.integrable (hψ i) hf), ← MeasureTheory.integral_const_mul]`.

Use `MeasureTheory.norm_integral_le_of_norm_le ((hint1 i).const_mul δ) (Filter.Eventually.of_forall (fun g => ?_))` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul]`. Distinguish the cases in `hg : g ∈ tsupport (fun g : UJ ε => ψ i (umat g))`. Establish `hgC : umat g ∈ (fun g : UJ ε => umat g) '' K` using `⟨g, Set.mem_iUnion.2 ⟨i, hg⟩, rfl⟩`. Rewrite using `[mul_comm δ]`.

Conclude with `mul_le_mul_of_nonneg_left (hclose _ hgC (hmem g)).le (norm_nonneg _)`. Establish `h0 : ψ i (umat g) = 0` using `image_eq_zero_of_notMem_tsupport (f := fun g : UJ ε => ψ i (umat g)) hg`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[hB, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖X‖` using `norm_pos_iff.2 hne`. Establish `hle` using `bound (‖X‖ / (B + 1)) (div_pos hpos (by linarith))`. Establish `hlt : ‖X‖ / (B + 1) * B < ‖X‖`.

Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `eq_zero_of_test (fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)) hcont key (mkU y hy)`. Simplify `h` using `[umat_mkU]`.
-/
theorem _root_.GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Mx n → ℂ), CSm ε F → ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)),
    (∀ C : Set (Mx n), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ f : Mx n → ℂ, CSm ε f ∧
      (∀ y ∈ C, y ∈ UJset ε → ‖F y - f y‖ < δ) ∧ ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) f y = 0) →
    ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) F y = 0 := by
  intro n ε F hF m c u hlim y hy
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcont : Continuous fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g) := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact continuous_const.mul (CSm.continuous (CSm.wordF hF (u i)))
  have key : ∀ φ, IsTest ε φ →
      ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) = 0 := by
    intro φ hφ
    choose ψ hψ hadj using fun i => exists_adjoint_word (u i) hφ

    have expand : ∀ G, CSm ε G →
        ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) G (umat g) ∂(muG ε)
          = ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * G (umat g) ∂(muG ε) := by
      intro G hG
      have hfun : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) G (umat g))
          = fun g => ∑ i, c i * (φ (umat g) * wordF (u i) G (umat g)) := by
        funext g
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfun, MeasureTheory.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_const_mul, hadj i G hG]
      · intro i _
        exact (IsTest.integrable hφ (CSm.wordF hG (u i))).const_mul (c i)
    have h1 : CSm ε (fun _ : Mx n => (1 : ℂ)) := cSm_of_contDiff _ contDiff_const
    have hint1 : ∀ i, MeasureTheory.Integrable (fun g : UJ ε => ‖ψ i (umat g)‖) (muG ε) := by
      intro i
      simpa using (IsTest.integrable (hψ i) h1).norm
    set A : Fin m → ℝ := fun i => ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε) with hA
    set B : ℝ := ∑ i, ‖c i‖ * A i with hB
    have hA0 : ∀ i, 0 ≤ A i := fun i => MeasureTheory.integral_nonneg (fun g => norm_nonneg _)
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA0 i))
    set X := ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) with hX

    have bound : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ δ * B := by
      intro δ hδ
      let K : Set (UJ ε) := ⋃ i, tsupport (fun g : UJ ε => ψ i (umat g))
      have hK : IsCompact K := isCompact_iUnion (fun i => (hψ i).2.isCompact)
      have hC : IsCompact ((fun g : UJ ε => umat g) '' K) := hK.image (umat_emb ε).continuous
      obtain ⟨f, hf, hclose, hzero⟩ := hlim _ hC δ hδ
      have e0 : ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε) = 0 := by
        rw [← expand f hf]
        have hz : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) f (umat g)) = fun _ => 0 := by
          funext g
          rw [hzero _ (hmem g), mul_zero]
        rw [hz, MeasureTheory.integral_zero]
      have hXf : X = ∑ i, c i * ((∫ g : UJ ε, ψ i (umat g) * F (umat g) ∂(muG ε))
          - ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε)) := by
        rw [hX, expand F hF]
        simp only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]
      rw [hXf]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => ?_ : ∀ i ∈ Finset.univ, _ ≤ ‖c i‖ * (δ * A i))).trans
        (le_of_eq ?_)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        show _ ≤ δ * ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε)
        rw [← MeasureTheory.integral_sub (IsTest.integrable (hψ i) hF) (IsTest.integrable (hψ i) hf),
          ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.norm_integral_le_of_norm_le ((hint1 i).const_mul δ)
          (Filter.Eventually.of_forall (fun g => ?_))
        rw [← mul_sub, norm_mul]
        by_cases hg : g ∈ tsupport (fun g : UJ ε => ψ i (umat g))
        · have hgC : umat g ∈ (fun g : UJ ε => umat g) '' K := ⟨g, Set.mem_iUnion.2 ⟨i, hg⟩, rfl⟩
          rw [mul_comm δ]
          exact mul_le_mul_of_nonneg_left (hclose _ hgC (hmem g)).le (norm_nonneg _)
        · have h0 : ψ i (umat g) = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun g : UJ ε => ψ i (umat g)) hg
          rw [h0]
          simp
      · rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    by_contra hne
    have hpos : 0 < ‖X‖ := norm_pos_iff.2 hne
    have hle := bound (‖X‖ / (B + 1)) (div_pos hpos (by linarith))
    have hlt : ‖X‖ / (B + 1) * B < ‖X‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have h := eq_zero_of_test (fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)) hcont key (mkU y hy)
  simpa [umat_mkU] using h
