import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Unfold `wt`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
private theorem wt_nonneg' {K : Type} [Field K] [NumberField K]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := K))`.
-/
private theorem continuous_ab {K : Type} [Field K] [NumberField K] :
    Continuous (ab : (A K)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := K))

/- English proof (translation)
The claim follows from `(IdeleGroup.ideleModule K a).2`.
-/
private theorem ab_pos {K : Type} [Field K] [NumberField K] (a : (A K)ˣ) : 0 < ab a :=
  (IdeleGroup.ideleModule K a).2

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC`. Take `⟨K, hK, hΦ⟩` from `hΦ`. Take `⟨ρ, hρ, hact, hnu, -, -⟩` from `actCont F E D`. Set `r : GL (Fin 2) (A E) → GL (Fin 4) (A F)` to `fun h => ρ h⁻¹`. Establish `hr : Continuous r` using `hρ.comp continuous_inv`.

Take `⟨K', hK', hlin⟩` from `wtLin F (r '' C) (hC.image hr) K hK`. Set `β : GL (Fin 2) (A E) → ℝ` to `fun h => (ab (nu F h))⁻¹`. Establish `hβ : Continuous β` using `(continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'`. Take `⟨A₀, hA₀⟩` from `(hC.image hβ).bddAbove`. Use `⟨K', hK', fun N => ?_⟩` and prove the remaining obligations.

Take `⟨B, hB⟩` from `hΦ N`. Take `⟨B', hB'⟩` from `hlin N`. Use `⟨|A₀| * (|B| * B'), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h, i⟩ ⟨hh, hi⟩ v`. Establish `hβ0 : 0 ≤ β h` using `(inv_pos.2 (ab_pos _)).le`.

Establish `hβA : β h ≤ |A₀|` using `(hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)`. Establish `hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖`. Rewrite using `[W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]`. Establish `h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v)`. Establish `h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v` using `hB' (r h) ⟨h, hh, rfl⟩ v`.

Establish `h3` using `hB i hi (D.act h⁻¹ v)`. Rewrite `h3`, the goal using `[hact h⁻¹ v]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.lDom :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), LDom W := by
  intro F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC
  obtain ⟨K, hK, hΦ⟩ := hΦ
  obtain ⟨ρ, hρ, hact, hnu, -, -⟩ := actCont F E D

  let r : GL (Fin 2) (A E) → GL (Fin 4) (A F) := fun h => ρ h⁻¹
  have hr : Continuous r := hρ.comp continuous_inv
  obtain ⟨K', hK', hlin⟩ := wtLin F (r '' C) (hC.image hr) K hK

  let β : GL (Fin 2) (A E) → ℝ := fun h => (ab (nu F h))⁻¹
  have hβ : Continuous β :=
    (continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'
  obtain ⟨A₀, hA₀⟩ := (hC.image hβ).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hB⟩ := hΦ N
  obtain ⟨B', hB'⟩ := hlin N
  refine ⟨|A₀| * (|B| * B'), ?_⟩
  rintro ⟨h, i⟩ ⟨hh, hi⟩ v
  have hβ0 : 0 ≤ β h := (inv_pos.2 (ab_pos _)).le
  have hβA : β h ≤ |A₀| := (hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)
  have hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := by
    rw [W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v) := by
    have h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v := hB' (r h) ⟨h, hh, rfl⟩ v
    have h3 := hB i hi (D.act h⁻¹ v)
    rw [hact h⁻¹ v] at h3 ⊢
    calc _ ≤ B * wt K N ((r h).val *ᵥ v) := h3
      _ ≤ |B| * wt K N ((r h).val *ᵥ v) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := hnorm
    _ ≤ |A₀| * (|B| * (B' * wt K' N v)) :=
      mul_le_mul hβA h1 (norm_nonneg _) (abs_nonneg _)
    _ = |A₀| * (|B| * B') * wt K' N v := by ring
