import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsES

noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtAlg

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

def Ehat : MonoidAlgebra ℂ (G0g D.nd) := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (hat hS X.B.e))

/- English proof (translation)
Simplify using `[Ehat, MonoidAlgebra.coeff_ofCoeff]`.
-/
theorem Ehat_coeff (γ : G0g D.nd) : (Ehat hS).coeff γ = hat hS X.B.e γ := by
  simp [Ehat, MonoidAlgebra.coeff_ofCoeff]

/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[coeff_mul_fin]`. Simplify using `only [Ehat_coeff hS]`. Conclude with `hat_e_idem hS γ`.
-/
theorem Ehat_idem : Ehat hS * Ehat hS = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ehat_coeff hS]
  exact hat_e_idem hS γ

/- English proof (translation)
Establish `h1 : f ((sec hS γ⁻¹ : KSub X.B.I) : X.B.I.Gf) = f (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf)`. Rewrite using `[val_hat hS hf, val_hat hS hf, rho_sec, map_inv, rho_sec]`. Establish `hcoe : (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) = ((sec hS γ : KSub X.B.I) : X.B.I.Gf)⁻¹` using `rfl`. Unfold `hat`. Rewrite using `[h1, hcoe, hsa, star_mul', Complex.star_def, Complex.conj_ofReal]`.
-/
theorem hat_inv {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (hsa : ∀ x, f x⁻¹ = star (f x)) (γ : G0g D.nd) :
    hat hS f γ⁻¹ = star (hat hS f γ) := by
  have h1 : f ((sec hS γ⁻¹ : KSub X.B.I) : X.B.I.Gf) = f (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) := by
    rw [val_hat hS hf, val_hat hS hf, rho_sec, map_inv, rho_sec]
  have hcoe : (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) = ((sec hS γ : KSub X.B.I) : X.B.I.Gf)⁻¹ := rfl
  unfold hat
  rw [h1, hcoe, hsa, star_mul', Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `γ`. Rewrite using `[conjA_coeff, Ehat_coeff hS, Ehat_coeff hS, hat_inv hS (biInv_e X) X.B.e_adm.2.2.1 γ, star_star]`.
-/
theorem Ehat_selfadj : conjA (Ehat hS) = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [conjA_coeff, Ehat_coeff hS, Ehat_coeff hS, hat_inv hS (biInv_e X) X.B.e_adm.2.2.1 γ, star_star]

/- English proof (translation)
Rewrite using `[hat_eT hS S γ, coeff_mul_fin]`. Simplify using `only [Ehat_coeff hS]`.
-/
theorem hat_eT' (S : Set (Tup2 D)) (γ : G0g D.nd) : hat hS (eT X S) γ = (Ehat hS * ES S).coeff γ := by
  rw [hat_eT hS S γ, coeff_mul_fin]
  simp only [Ehat_coeff hS]

/- English proof (translation)
Rewrite using `[mul_assoc, ES_central S (Ehat hS * ES S), mul_assoc, ← mul_assoc (Ehat hS) (Ehat hS), Ehat_idem hS, ES_idem]`.
-/
theorem prod_idem (S : Set (Tup2 D)) : (Ehat hS * ES S) * (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [mul_assoc, ES_central S (Ehat hS * ES S), mul_assoc, ← mul_assoc (Ehat hS) (Ehat hS), Ehat_idem hS,
    ES_idem]

/- English proof (translation)
Rewrite using `[conjA_mul, ES_selfadj, Ehat_selfadj hS, ES_central]`.
-/
theorem prod_selfadj (S : Set (Tup2 D)) : conjA (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [conjA_mul, ES_selfadj, Ehat_selfadj hS, ES_central]

/- English proof (translation)
Apply `hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S)) (biInv_eT X S)` to reduce the goal to its premises. Introduce `γ`. Rewrite using `[conv_hat hS (biInv_eT X S) (biInv_eT X S) γ]`. Simplify using `only [hat_eT' hS S]`. Rewrite using `[← coeff_mul_fin, prod_idem hS S]`.
-/
theorem eT_idem (S : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S) = eT X S := by
  apply hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S)) (biInv_eT X S)
  intro γ
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S) γ]
  simp only [hat_eT' hS S]
  rw [← coeff_mul_fin, prod_idem hS S]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ X.B.I.Kset`. Establish `key : eT X S x = hat hS (eT X S) (rhoX X ⟨x, hx⟩) / (V X : ℂ)` using `val_hat hS (biInv_eT X S) ⟨x, hx⟩`. Establish `k1 : eT X S x⁻¹ = hat hS (eT X S) (rhoX X ⟨x, hx⟩)⁻¹ / (V X : ℂ)`. Use `val_hat hS (biInv_eT X S) (⟨x, hx⟩ : KSub X.B.I)⁻¹` as an intermediate fact. Rewrite `this` using `[map_inv]`. Then use the resulting hypothesis.

Establish `hc : ∀ γ, (Ehat hS * ES S).coeff γ⁻¹ = star ((Ehat hS * ES S).coeff γ)`. Introduce `γ`. Use `conv_lhs => rw [← prod_selfadj hS S]`. Rewrite using `[conjA_coeff, inv_inv]`. Rewrite using `[k1, key, hat_eT' hS S, hat_eT' hS S, hc, star_div₀, Complex.star_def, Complex.conj_ofReal]`.

Establish `hx' : x⁻¹ ∉ X.B.I.Kset` using `fun h => hx (by simpa using K_inv X.B.I h)`. Rewrite using `[eT_of_not_mem X S hx, eT_of_not_mem X S hx', star_zero]`.
-/
theorem eT_inv (S : Set (Tup2 D)) (x : X.B.I.Gf) : eT X S x⁻¹ = star (eT X S x) := by
  by_cases hx : x ∈ X.B.I.Kset
  · have key : eT X S x = hat hS (eT X S) (rhoX X ⟨x, hx⟩) / (V X : ℂ) := val_hat hS (biInv_eT X S) ⟨x, hx⟩
    have k1 : eT X S x⁻¹ = hat hS (eT X S) (rhoX X ⟨x, hx⟩)⁻¹ / (V X : ℂ) := by
      have := val_hat hS (biInv_eT X S) (⟨x, hx⟩ : KSub X.B.I)⁻¹
      rwa [map_inv] at this
    have hc : ∀ γ, (Ehat hS * ES S).coeff γ⁻¹ = star ((Ehat hS * ES S).coeff γ) := by
      intro γ
      conv_lhs => rw [← prod_selfadj hS S]
      rw [conjA_coeff, inv_inv]
    rw [k1, key, hat_eT' hS S, hat_eT' hS S, hc, star_div₀, Complex.star_def, Complex.conj_ofReal]
  · have hx' : x⁻¹ ∉ X.B.I.Kset := fun h => hx (by simpa using K_inv X.B.I h)
    rw [eT_of_not_mem X S hx, eT_of_not_mem X S hx', star_zero]

section Pos

open scoped ComplexOrder

omit hS in

/- English proof (translation)
Introduce `m x c`. Establish `hsub : ∀ i j, f ((x i)⁻¹ * x j) = ∫ z, star (f (z⁻¹ * x i)) * f (z⁻¹ * x j) ∂μ`. Introduce `i j`. Use `conv_lhs => rw [← hconv]`. Use `integral_mul_left_eq_self (μ := μ) (fun y => f y * f (y⁻¹ * ((x i)⁻¹ * x j))) (x i)⁻¹` as an intermediate fact.

Use `show ∫ y, f y * f (y⁻¹ * ((x i)⁻¹ * x j)) ∂μ = _`. Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[← hsa (z⁻¹ * x i)]`.

Apply the tactic sequence `congr 1 <;> congr 1 <;> group`. Establish `hint : ∀ i j, Integrable (fun z => star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) μ`. Introduce `i j`. Use `Continuous.integrable_of_hasCompactSupport ?_ ?_` and prove the remaining obligations. Conclude with `((hc.comp (continuous_inv.mul continuous_const)).star).mul (hc.comp (continuous_inv.mul continuous_const))`.

Use `HasCompactSupport.intro (IsCompact.image (f := fun y : I.Gf => x j * y⁻¹) hC (continuous_const.mul continuous_inv)) ?_` and prove the remaining obligations. Introduce `z hz`. Establish `h0 : f (z⁻¹ * x j) = 0`. Assume the negation of the conclusion as `h`. Apply `hz` to reduce the goal to its premises.

Conclude with `⟨z⁻¹ * x j, hsupp _ h, by group⟩`. Rewrite using `[h0, mul_zero]`. Establish `hF : ∀ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) = ∑ i, ∑ j, star (c i) * c j * (star (f (z⁻¹ * x i)) * f (z⁻¹ * x j))`. Introduce `z`. Rewrite using `[Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∫ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) ∂μ = ∑ i, ∑ j, star (c i) * c j * f ((x i)⁻¹ * x j)`. Repeatedly rewrite using `[hF]`.

Rewrite using `[integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hint i j).const_mul _))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, hsub]`.

Rewrite using `[← key, integral_complex_ofReal]`. Conclude with `Complex.zero_le_real.2 (integral_nonneg fun z => Complex.normSq_nonneg _)`.
-/
theorem posType_of (I : AutInst) (μ : Measure I.Gf) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {f : I.Gf → ℂ} (hc : Continuous f) {C : Set I.Gf} (hC : IsCompact C) (hCo : IsOpen C)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ C) (hconv : I.convF μ f f = f) (hsa : ∀ x, f x⁻¹ = star (f x)) :
    I.IsPosType f := by
  intro m x c
  have hsub : ∀ i j, f ((x i)⁻¹ * x j) = ∫ z, star (f (z⁻¹ * x i)) * f (z⁻¹ * x j) ∂μ := by
    intro i j
    conv_lhs => rw [← hconv]
    have := integral_mul_left_eq_self (μ := μ) (fun y => f y * f (y⁻¹ * ((x i)⁻¹ * x j))) (x i)⁻¹
    show ∫ y, f y * f (y⁻¹ * ((x i)⁻¹ * x j)) ∂μ = _
    rw [← this]
    congr 1
    funext z
    rw [← hsa (z⁻¹ * x i)]
    congr 1 <;> congr 1 <;> group
  have hint : ∀ i j, Integrable (fun z => star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) μ := by
    intro i j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hc.comp (continuous_inv.mul continuous_const)).star).mul
        (hc.comp (continuous_inv.mul continuous_const))
    · refine HasCompactSupport.intro
        (IsCompact.image (f := fun y : I.Gf => x j * y⁻¹) hC (continuous_const.mul continuous_inv)) ?_
      intro z hz
      have h0 : f (z⁻¹ * x j) = 0 := by
        by_contra h
        apply hz
        exact ⟨z⁻¹ * x j, hsupp _ h, by group⟩
      rw [h0, mul_zero]
  have hF : ∀ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (c i) * c j * (star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have key : ∫ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) ∂μ =
      ∑ i, ∑ j, star (c i) * c j * f ((x i)⁻¹ * x j) := by
    simp_rw [hF]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hint i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hsub]
  rw [← key, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun z => Complex.normSq_nonneg _)

end Pos

/- English proof (translation)
Conclude with `posType_of X.B.I X.B.μf (isLocallyConstant_eT X S).continuous (PI.WAU.Cpt.isCompact_Kset X.B.I) (PI.WAU.kset_open X.B.I) (fun x hx => by_contra fun h => hx (eT_of_not_mem X S h)) (eT_idem hS S) (eT_inv hS S)`.
-/
theorem eT_pos (S : Set (Tup2 D)) : X.B.I.IsPosType (eT X S) := by
  exact posType_of X.B.I X.B.μf (isLocallyConstant_eT X S).continuous (PI.WAU.Cpt.isCompact_Kset X.B.I)
    (PI.WAU.kset_open X.B.I) (fun x hx => by_contra fun h => hx (eT_of_not_mem X S h)) (eT_idem hS S)
    (eT_inv hS S)

/- English proof (translation)
Assemble the required witnesses or components as `⟨eT_idem hS S, eT_inv hS S, eT_pos hS S⟩`.
-/
theorem etAlg_of (S : Set (Tup2 D)) : EtAlg X S :=
  ⟨eT_idem hS S, eT_inv hS S, eT_pos hS S⟩

end Formalism.L2.SG.Pf.AllRowsEtAlg
