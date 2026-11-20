import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[map_mulVec_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one h (map_zero h) (map_one h), Matrix.one_mulVec]`.
-/
private theorem inv_map_mulVec {R : Type} [CommRing R] (h : A K →+* R) (g : GL (Fin 4) (A K))
    (v : Fin 4 → A K) :
    (g⁻¹).val.map h *ᵥ (fun i => h ((g.val *ᵥ v) i)) = fun i => h (v i) := by
  rw [map_mulVec_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.map_one h (map_zero h) (map_one h), Matrix.one_mulVec]

/- English proof (translation)
The claim follows from `(homeomorphMixedSpace K).continuous.comp continuous_fst`.
-/
private theorem continuous_adeleInfHom : Continuous (adeleInfHom : A K → mixedSpace K) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

/- English proof (translation)
The claim follows from `continuous_snd`.
-/
private theorem continuous_adeleFinHom : Continuous (adeleFinHom : A K → FiniteAdeleRing (𝓞 K) K) :=
  continuous_snd

/- English proof (translation)
The claim follows from `(Units.continuous_val.comp continuous_inv).matrix_elem i j`.
-/
private theorem continuous_invEntry (i j : Fin 4) :
    Continuous fun x : GL (Fin 4) (A K) => (x⁻¹).val i j :=
  (Units.continuous_val.comp continuous_inv).matrix_elem i j

/- English proof (translation)
Unfold `wt`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
private theorem wt_nonneg (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) :
    0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

/- English proof (translation)
Establish `hm0 : 0 ≤ m ^ N` using `by positivity`. Distinguish the cases in `hv : finPartPi w ∈ S`. Take `⟨hfin, hs⟩` from `h hv`. Generalize the expression as in `hsd : ‖infPartPi v‖ = s at hs`. Generalize the expression as in `htd : ‖infPartPi w‖ = t at hs`.

Establish `ht0 : 0 ≤ t` using `htd ▸ norm_nonneg _`. Establish `hs0 : 0 ≤ s` using `hsd ▸ norm_nonneg _`. Establish `h1 : 1 + s ≤ m * (1 + t)` using `by nlinarith`. Establish `hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N`. Rewrite using `[← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by positivity) h1 N`. Establish `e1 : wt S N w = ((1 + t) ^ N)⁻¹` using `by rw [← htd]; exact if_pos hv`. Establish `e2 : wt S' N v = ((1 + s) ^ N)⁻¹` using `by rw [← hsd]; exact if_pos hfin`. Rewrite using `[e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: wt S N w = 0` using `if_neg hv`. Rewrite using `[this]`. Conclude with `mul_nonneg hm0 (wt_nonneg _ _ _)`.
-/
private theorem wt_le_of {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)} {N : ℕ} {v w : V4 K} {m : ℝ}
    (hm1 : 1 ≤ m) (h : finPartPi w ∈ S → finPartPi v ∈ S' ∧ ‖infPartPi v‖ ≤ m * ‖infPartPi w‖) :
    wt S N w ≤ m ^ N * wt S' N v := by
  have hm0 : 0 ≤ m ^ N := by positivity
  by_cases hv : finPartPi w ∈ S
  · obtain ⟨hfin, hs⟩ := h hv
    generalize hsd : ‖infPartPi v‖ = s at hs
    generalize htd : ‖infPartPi w‖ = t at hs
    have ht0 : 0 ≤ t := htd ▸ norm_nonneg _
    have hs0 : 0 ≤ s := hsd ▸ norm_nonneg _
    have h1 : 1 + s ≤ m * (1 + t) := by nlinarith
    have hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 N
    have e1 : wt S N w = ((1 + t) ^ N)⁻¹ := by rw [← htd]; exact if_pos hv
    have e2 : wt S' N v = ((1 + s) ^ N)⁻¹ := by rw [← hsd]; exact if_pos hfin
    rw [e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have : wt S N w = 0 := if_neg hv
    rw [this]
    exact mul_nonneg hm0 (wt_nonneg _ _ _)

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)`.
-/
private theorem norm_mulVec_le (M : Matrix (Fin 4) (Fin 4) (mixedSpace K))
    (u : Fin 4 → mixedSpace K) : ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

end

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding in
/- English proof (translation)
Introduce `F _ _ C hC K hK`. Set `ψ : GL (Fin 4) (A F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) → (Fin 4 → FiniteAdeleRing (𝓞 F) F)` to `fun p => (p.1⁻¹).val.map adeleFinHom *ᵥ p.2`. Establish `hψ : Continuous ψ`. Conclude with `(Continuous.matrix_map (Units.continuous_val.comp (continuous_inv.comp continuous_fst)) continuous_adeleFinHom).matrix_mulVec continuous_snd`. Use `⟨ψ '' (C ×ˢ K), (hC.prod hK).image hψ, fun N => ?_⟩` and prove the remaining obligations.

Set `β : GL (Fin 4) (A F) → ℝ` to `fun x => ∑ i, ∑ j, ‖(x⁻¹).val.map (adeleInfHom (K := F)) i j‖`. Establish `hβ : Continuous β`. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact (continuous_adeleInfHom.comp (continuous_invEntry i j)).norm`. Take `⟨B₀, hB₀⟩` from `(hC.image hβ).bddAbove`.

Establish `hβle : ∀ x ∈ C, β x ≤ B₀` using `fun x hx => hB₀ ⟨x, hx, rfl⟩`. Use `set m : ℝ := max 1 B₀ with hm`. Establish `hm1 : 1 ≤ m` using `le_max_left _ _`. Use `⟨m ^ N, fun x hx v => ?_⟩` and prove the remaining obligations. Use `wt_le_of hm1 fun hv => ?_` and prove the remaining obligations.

Establish `hfin : finPartPi v ∈ ψ '' (C ×ˢ K)`. Use `⟨(x, finPartPi (x.val *ᵥ v)), ⟨hx, hv⟩, ?_⟩` and prove the remaining obligations. Use `inv_map_mulVec (adeleFinHom (K := F)) x v` as an intermediate fact. Simplify `this` using `only [ψ, finPartPi_eq_adeleFinHom]`. Establish `hinf : infPartPi v = (x⁻¹).val.map adeleInfHom *ᵥ infPartPi (x.val *ᵥ v)`.

Use `inv_map_mulVec (adeleInfHom (K := F)) x v` as an intermediate fact. Simplify `this.symm` using `only [infPartPi_eq_adeleInfHom]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[hinf]`. Conclude with `(norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right ((hβle x hx).trans (le_max_right _ _)) (norm_nonneg _))`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtLin :
    ∀ (F : Type) [Field F] [NumberField F], WtLin F := by
  intro F _ _ C hC K hK

  let ψ : GL (Fin 4) (A F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) → (Fin 4 → FiniteAdeleRing (𝓞 F) F) :=
    fun p => (p.1⁻¹).val.map adeleFinHom *ᵥ p.2
  have hψ : Continuous ψ := by
    exact (Continuous.matrix_map (Units.continuous_val.comp (continuous_inv.comp continuous_fst))
      continuous_adeleFinHom).matrix_mulVec continuous_snd
  refine ⟨ψ '' (C ×ˢ K), (hC.prod hK).image hψ, fun N => ?_⟩

  let β : GL (Fin 4) (A F) → ℝ := fun x => ∑ i, ∑ j, ‖(x⁻¹).val.map (adeleInfHom (K := F)) i j‖
  have hβ : Continuous β := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (continuous_adeleInfHom.comp (continuous_invEntry i j)).norm
  obtain ⟨B₀, hB₀⟩ := (hC.image hβ).bddAbove
  have hβle : ∀ x ∈ C, β x ≤ B₀ := fun x hx => hB₀ ⟨x, hx, rfl⟩
  set m : ℝ := max 1 B₀ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  refine ⟨m ^ N, fun x hx v => ?_⟩
  refine wt_le_of hm1 fun hv => ?_
  have hfin : finPartPi v ∈ ψ '' (C ×ˢ K) := by
    refine ⟨(x, finPartPi (x.val *ᵥ v)), ⟨hx, hv⟩, ?_⟩
    have := inv_map_mulVec (adeleFinHom (K := F)) x v
    simpa only [ψ, finPartPi_eq_adeleFinHom] using this
  have hinf : infPartPi v = (x⁻¹).val.map adeleInfHom *ᵥ infPartPi (x.val *ᵥ v) := by
    have := inv_map_mulVec (adeleInfHom (K := F)) x v
    simpa only [infPartPi_eq_adeleInfHom] using this.symm
  refine ⟨hfin, ?_⟩
  rw [hinf]
  exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    ((hβle x hx).trans (le_max_right _ _)) (norm_nonneg _))
