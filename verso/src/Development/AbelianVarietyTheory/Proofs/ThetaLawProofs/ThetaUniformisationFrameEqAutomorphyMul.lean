import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta.Frame
open Matrix

/- English proof (translation)
Establish `hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ)` using `rfl`. Establish `hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ)` using `rfl`. Rewrite using `[hk, hn, lat]`. Normalize the expressions using the abelian group laws.
-/
private lemma add_lat_eq_add_mulVec_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ)
    (z : Fin g → ℂ) :
    z + lat τ k n = z + τ *ᵥ ReciprocityTheory.PTheta.ofIntVec n + ReciprocityTheory.PTheta.ofIntVec k := by
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  rw [hk, hn, lat]
  abel

/- English proof (translation)
Rewrite using `[ReciprocityTheory.PTheta.autFactor, TorusAlg.ofRealVec_re ha, TorusAlg.ofRealVec_re hb]`. Establish `hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ)` using `rfl`. Establish `hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ)` using `rfl`. Simplify using `only [aut, ReciprocityTheory.PTheta.eC, hk, hn, ← Complex.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma autFactor_re_eq_aut_of_half_characteristics {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    ReciprocityTheory.PTheta.autFactor (fun i => (a i).re) (fun i => (b i).re) τ n k z =
      aut τ a b k n z := by
  rw [ReciprocityTheory.PTheta.autFactor, TorusAlg.ofRealVec_re ha, TorusAlg.ofRealVec_re hb]
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  simp only [aut, ReciprocityTheory.PTheta.eC, hk, hn, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Take `⟨ha, hb⟩` from `hab`. Take `⟨hne, hspan, -⟩` from `TorusAlg.thetaChar_level hs hp ha hb`. Establish `hmem : thetaChar τ a b ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_span_singleton_self _`.

Rewrite `hmem` using `[mem_thetaLevelChar_iff_autFactor]`. Use `⟨hmem.1, hne, fun k n z => ?_⟩` and prove the remaining obligations. Establish `hper` using `hmem.2 n k z`. Rewrite `hper` using `[pow_one]`. Rewrite using `[add_lat_eq_add_mulVec_add, hper, autFactor_re_eq_aut_of_half_characteristics ha hb]`.
-/
theorem thetaChar_law {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    Differentiable ℂ (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 ∧
      ∀ k n z, thetaChar τ a b (z + lat τ k n) = aut τ a b k n z * thetaChar τ a b z := by
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hne, hspan, -⟩ := TorusAlg.thetaChar_level hs hp ha hb
  have hmem : thetaChar τ a b ∈
      thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar_iff_autFactor] at hmem
  refine ⟨hmem.1, hne, fun k n z => ?_⟩
  have hper := hmem.2 n k z
  rw [pow_one] at hper
  rw [add_lat_eq_add_mulVec_add, hper, autFactor_re_eq_aut_of_half_characteristics ha hb]

/- English proof (translation)
Assume the negation of the conclusion as `hDz`. Establish `hθa : AnalyticOnNhd ℂ θ Set.univ` using `SCV.analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn`. Establish `hin : ∀ᶠ w in nhds z, w ∈ S` using `hS.mem_nhds hz`. Establish `hnear : ∀ᶠ w in nhds z, w ∈ S ∧ D w ≠ 0` using `hin.and ((hD.continuousAt (hS.mem_nhds hz)).eventually_ne hDz)`. Establish `hθz : θ =ᶠ[nhds z] 0` using `by filter_upwards [hnear] with w hw`.

Break down `mul_eq_zero.1 (h w hw.1) with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd h' hw.2`. Establish `hall` using `hθa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) hθz`. Conclude with `h0 (funext fun w => hall (Set.mem_univ w))`.
-/
theorem eq_zero_of_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hDz
  have hθa : AnalyticOnNhd ℂ θ Set.univ :=
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn
  have hin : ∀ᶠ w in nhds z, w ∈ S := hS.mem_nhds hz
  have hnear : ∀ᶠ w in nhds z, w ∈ S ∧ D w ≠ 0 :=
    hin.and ((hD.continuousAt (hS.mem_nhds hz)).eventually_ne hDz)
  have hθz : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hnear] with w hw
    rcases mul_eq_zero.1 (h w hw.1) with h' | h'
    · exact h'
    · exact absurd h' hw.2
  have hall := hθa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hθz
  exact h0 (funext fun w => hall (Set.mem_univ w))

/- English proof (translation)
Introduce `g x h u τ a b hab hw k n i z hz`. Take `⟨hs, hp, hΛ, -, hth, -⟩` from `hw`. Establish `hlaw` using `thetaChar_law hs hp hab`. Take `⟨ha, hb⟩` from `hab`. Establish `hlatΛ : lat τ k n ∈ u.Λ` using `(hΛ _).2 ⟨k, n, rfl⟩`.

Establish `hex : ∀ w, u.ex (w + lat τ k n) = u.ex w` using `fun w => CubeValues.ex_add_period u w _ hlatΛ`. Set `S : Set (Fin g → ℂ)` to `{w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i}`. Establish `hSo : IsOpen S` using `(u.hol (x.P.L.U i) 0).1`. Establish `hfr : ContinuousOn (u.fr i) S` using `(u.fr_hol i).continuousOn`. Establish `hfr' : ContinuousOn (fun w => u.fr i (w + lat τ k n)) S`.

Use `hfr.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_` and prove the remaining obligations. Use `show ⊤ ≤ (u.ex (w + lat τ k n)).left ⁻¹ᵁ x.P.L.U i`. Rewrite using `[hex]`. Conclude with `hw`. Establish `haut : Continuous fun w => aut τ a b k n w`.

Unfold `aut`. Simplify using `only [dotProduct]`. Use `fun_prop`. Establish `hD : ContinuousOn (fun w => u.fr i w - aut τ a b k n w * u.fr i (w + lat τ k n)) S` using `hfr.sub (haut.continuousOn.mul hfr')`. Use `sub_eq_zero.1 (eq_zero_of_mul_eq_zero hlaw.1 hlaw.2.1 hSo hD (fun w hwS => ?_) hz)` and prove the remaining obligations.

Distinguish the cases in `hθ : thetaChar τ a b w = 0`. Rewrite using `[hθ, zero_mul]`. Establish `hf` using `TorusAlg.frame_eq_autFactor_mul u x.th hs ha hb hΛ hth n k i w hwS hθ`. Rewrite `hf` using `[autFactor_re_eq_aut_of_half_characteristics ha hb, ← add_lat_eq_add_mulVec_add]`. Rewrite using `[← hf, sub_self, mul_zero]`.
-/
theorem frame_eq_aut_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  intro g x h u τ a b hab hw k n i z hz
  obtain ⟨hs, hp, hΛ, -, hth, -⟩ := hw
  have hlaw := thetaChar_law hs hp hab
  obtain ⟨ha, hb⟩ := hab
  have hlatΛ : lat τ k n ∈ u.Λ := (hΛ _).2 ⟨k, n, rfl⟩
  have hex : ∀ w, u.ex (w + lat τ k n) = u.ex w := fun w =>
    CubeValues.ex_add_period u w _ hlatΛ
  let S : Set (Fin g → ℂ) := {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i}
  have hSo : IsOpen S := (u.hol (x.P.L.U i) 0).1
  have hfr : ContinuousOn (u.fr i) S := (u.fr_hol i).continuousOn
  have hfr' : ContinuousOn (fun w => u.fr i (w + lat τ k n)) S := by
    refine hfr.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_
    show ⊤ ≤ (u.ex (w + lat τ k n)).left ⁻¹ᵁ x.P.L.U i
    rw [hex]
    exact hw
  have haut : Continuous fun w => aut τ a b k n w := by
    unfold aut
    simp only [dotProduct]
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - aut τ a b k n w * u.fr i (w + lat τ k n)) S :=
    hfr.sub (haut.continuousOn.mul hfr')
  refine sub_eq_zero.1 (eq_zero_of_mul_eq_zero hlaw.1 hlaw.2.1 hSo hD (fun w hwS => ?_) hz)
  by_cases hθ : thetaChar τ a b w = 0
  · rw [hθ, zero_mul]
  · have hf := TorusAlg.frame_eq_autFactor_mul u x.th hs ha hb hΛ hth n k i w hwS hθ
    rw [autFactor_re_eq_aut_of_half_characteristics ha hb, ← add_lat_eq_add_mulVec_add] at hf
    rw [← hf, sub_self, mul_zero]

end GlobalTheory.SimilTheta.Frame
end
