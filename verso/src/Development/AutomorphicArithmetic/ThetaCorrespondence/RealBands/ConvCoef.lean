import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

/- English proof (translation)
Introduce `n ε H _ _ σ d hrep hF v a`. Take `⟨⟨_, hmul⟩, hiso, hcont⟩` from `hrep`. Establish `hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun g hg x y => LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y`. Establish `hmem : ∀ g : UJ ε, umat g ∈ UJset ε` using `fun g => g.2`. Establish `hcoef : ∀ w z : H, Continuous (coefOn (ε` using `ε) σ w z) := by`.

Introduce `w z`. Establish `hu : Continuous fun g : UJ ε => umat g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hs : Continuous fun g : UJ ε => σ (umat g) w` using `(hcont w).comp_continuous hu hmem`. Conclude with `continuous_const.inner hs`. Use `⟨hcoef a v, fun x => ?_⟩` and prove the remaining obligations.

Establish `hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y`. Introduce `g y`. Establish `h` using `hmul _ (hmem g) _ (hmem g⁻¹)`. Establish `hone : umat g * umat g⁻¹ = 1` using `by show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1`. Rewrite using `[mul_inv_cancel]`.

Both sides reduce to the same expression. Rewrite `h` using `[hone]`. Establish `h1 : σ 1 = 1` using `by assumption`. Rewrite `h` using `[h1]`. Conclude with `(congrArg (fun f : H →L[ℂ] H => f y) h).symm`.

Establish `key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) = coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g)`. Introduce `g`. Use `congr 1`. Simplify using `only [coefOn]`. Establish `hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a)`.

Rewrite using `[show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]`. Both sides reduce to the same expression. Rewrite using `[hsplit]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← inner_conj_symm]`.

Both sides reduce to the same expression. Use `show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _`. Rewrite using `[show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) = fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key, (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]`. Use `show _ = _ * ⟪v, σ (umat x) a⟫_ℂ`. Use `push_cast`.

Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]`. Rewrite using `[mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Lit.Cusp.conv_coef :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → ∀ v a : H,
        Continuous (coefOn (ε := ε) σ a v) ∧
          ∀ x, conv (muG ε) (coefOn σ v v) (coefOn σ a v) x = ((‖v‖ ^ 2 / d : ℝ) : ℂ) * coefOn σ a v x := by
  intro n ε H _ _ σ d hrep hF v a
  obtain ⟨⟨_, hmul⟩, hiso, hcont⟩ := hrep
  have hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g hg x y =>
    LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcoef : ∀ w z : H, Continuous (coefOn (ε := ε) σ w z) := by
    intro w z
    have hu : Continuous fun g : UJ ε => umat g :=
      Units.continuous_val.comp continuous_subtype_val
    have hs : Continuous fun g : UJ ε => σ (umat g) w :=
      (hcont w).comp_continuous hu hmem
    exact continuous_const.inner hs
  refine ⟨hcoef a v, fun x => ?_⟩
  have hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y := by
    intro g y
    have h := hmul _ (hmem g) _ (hmem g⁻¹)
    have hone : umat g * umat g⁻¹ = 1 := by
      show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hone] at h
    have h1 : σ 1 = 1 := by assumption
    rw [h1] at h
    exact (congrArg (fun f : H →L[ℂ] H => f y) h).symm
  have key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) =
      coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) := by
    intro g
    congr 1
    simp only [coefOn]
    have hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a) := by
      rw [show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]
      rfl
    rw [hsplit]
    calc ⟪v, σ (umat g⁻¹) (σ (umat x) a)⟫_ℂ
        = ⟪σ (umat g) v, σ (umat g) (σ (umat g⁻¹) (σ (umat x) a))⟫_ℂ :=
          (hinner _ (hmem g) _ _).symm
      _ = ⟪σ (umat g) v, σ (umat x) a⟫_ℂ := by rw [hback]
      _ = star ⟪σ (umat x) a, σ (umat g) v⟫_ℂ := by
          rw [← inner_conj_symm]
          rfl
  show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _
  rw [show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) =
      fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key,
    (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]
  show _ = _ * ⟪v, σ (umat x) a⟫_ℂ
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]
  rfl
