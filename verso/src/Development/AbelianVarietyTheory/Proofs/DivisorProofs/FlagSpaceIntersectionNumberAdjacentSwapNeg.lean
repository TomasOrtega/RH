import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFuncStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `F _ X Y ι _ m E E' φ f hR gr hgr τ a b hab Q`. Take `⟨B, hB, hBg⟩` from `hgr`. Establish `hlt : a < b` using `by show (a : ℕ) < b`. Use linear arithmetic over natural numbers and integers. Take `⟨ψ₂, hgen, hφ, hpar⟩` from `GlobalTheory.T.exists_generic_pair_flags_differing_one_step F X Y ι m E E' φ f hR B hB τ a b hlt`.

Take `⟨W, j, h1, h2⟩` from `GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair F Y _ _ _ hgen`. Establish `hs : W.Small` using `GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc F Y W j h1`. Establish `e1 : ∀ u, j (W.α₁ u) = algebraMap Y.Fn (RatFunc Y.Fn) u` using `fun u => DFunLike.congr_fun h1 u`. Establish `e2 : ∀ u, j (W.α₂ u) = ψ₂ u` using `fun u => DFunLike.congr_fun h2 u`. Establish `hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)` using `fun u => j.injective (by rw [e1, e2, hφ])`.

Establish `m1 : (B.map W.α₁).map j = B.map (algebraMap Y.Fn (RatFunc Y.Fn))`. Use function extensionality and compare the values at `σ`. Use extensionality with `i k`. Conclude with `e1 _`. Establish `m2 : (B.map W.α₂).map j = B.map ψ₂`.

Use function extensionality and compare the values at `σ`. Use extensionality with `i k`. Conclude with `e2 _`. Establish `hlow : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)`. Use `GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic ι m τ a b hab _ _ j RatFunc.X RatFunc.X_ne_zero _ ?_` and prove the remaining obligations.

Rewrite using `[Mat.map_mul, Mat.map_inv, m1, m2]`. Conclude with `hpar`. Take `⟨D₁, D₂, Θ, h⟩` from `GlobalTheory.T.exists_divisors_doubleFlagSpace F X Y ι m E E' φ f hR gr B hB hBg W hα τ a b hab hlow`. Establish `hne : (⟨τ, a⟩ : Root m) ≠ ⟨τ, b⟩` using `fun h => hlt.ne (eq_of_heq (Sigma.mk.inj h).2)`. Use `GlobalTheory.T.intersectionNumber_swap_of_doubleSpace F Y W hs (Root m) _ _ hne gr D₁ D₂ Θ h Q` as an intermediate fact.

Use `this` and compare the differences between its conclusion and the goal.
-/
theorem interPoly_swap_adjacent : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), IsGraded E' gr → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q : MvPolynomial (Root m) ℝ, Y.interPoly gr (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - Y.interPoly gr Q := by
  intro F _ X Y ι _ m E E' φ f hR gr hgr τ a b hab Q
  obtain ⟨B, hB, hBg⟩ := hgr
  have hlt : a < b := by
    show (a : ℕ) < b
    omega
  obtain ⟨ψ₂, hgen, hφ, hpar⟩ := GlobalTheory.T.exists_generic_pair_flags_differing_one_step F X Y ι m E E' φ f hR B hB τ a b hlt
  obtain ⟨W, j, h1, h2⟩ := GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair F Y _ _ _ hgen
  have hs : W.Small := GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc F Y W j h1
  have e1 : ∀ u, j (W.α₁ u) = algebraMap Y.Fn (RatFunc Y.Fn) u := fun u => DFunLike.congr_fun h1 u
  have e2 : ∀ u, j (W.α₂ u) = ψ₂ u := fun u => DFunLike.congr_fun h2 u
  have hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u) := fun u =>
    j.injective (by rw [e1, e2, hφ])
  have m1 : (B.map W.α₁).map j = B.map (algebraMap Y.Fn (RatFunc Y.Fn)) := by
    funext σ; ext i k; exact e1 _
  have m2 : (B.map W.α₂).map j = B.map ψ₂ := by
    funext σ; ext i k; exact e2 _
  have hlow : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) := by
    refine GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic ι m τ a b hab _ _ j RatFunc.X RatFunc.X_ne_zero _ ?_
    rw [Mat.map_mul, Mat.map_inv, m1, m2]
    exact hpar
  obtain ⟨D₁, D₂, Θ, h⟩ := GlobalTheory.T.exists_divisors_doubleFlagSpace F X Y ι m E E' φ f hR gr B hB hBg W hα τ a b hab hlow
  have hne : (⟨τ, a⟩ : Root m) ≠ ⟨τ, b⟩ := fun h => hlt.ne (eq_of_heq (Sigma.mk.inj h).2)
  have := GlobalTheory.T.intersectionNumber_swap_of_doubleSpace F Y W hs (Root m) _ _ hne gr D₁ D₂ Θ h Q
  convert this

end GlobalTheory.FlagPush
