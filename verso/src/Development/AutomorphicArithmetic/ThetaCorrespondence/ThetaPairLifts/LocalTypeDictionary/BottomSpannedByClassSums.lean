import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleAlgebraicityFiniteData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumEqZeroOffFinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealTranslatePreservesRationalAction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFormRightTranslateLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassExistsFiniteReps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomIntegralRationalLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleAlgebraicityFiniteDataStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BotSpan
/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX`. Take `⟨K, hK⟩` from `_root_.GlobalTheory.T.bottomClassSum_finite_support hP hI hL hX`. Take `⟨M₁, hM₁, hr⟩` from `_root_.GlobalTheory.T.realTranslate_preserves_rationalAction hP hI hL hX`. Take `⟨J, M₂, hJ, hM₂, hl⟩` from `_root_.GlobalTheory.T.bottomForm_rightTranslate_level hP hI hL hX`. Take `⟨H, hH, hc⟩` from `_root_.GlobalTheory.T.bottomClasses_finite hP hI hL hX J hJ`.

Use `⟨H, K, M₁ ⊔ M₂, IntermediateField.finiteDimensional_sup M₁ M₂, hH, ?_⟩` and prove the remaining obligations. Introduce `t h hh k`. Take `⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩` from `hc h hh`. Establish `hx : h₀ * κ ∈ GfC WW` using `mul_mem (hH h₀ hh₀) hκf`. Establish `hγr : γ * r ∈ GfC WW`.

Establish `e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem hh (inv_mem hx)`. Take `⟨c, hcM, hcE⟩` from `hr t γ hγ r hrI hγr (h₀ * κ) k`. Take `⟨ℓ, hℓM, hℓ⟩` from `hl t κ hκJ hκf`.

Establish `e1 : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) = ∑ k' ∈ c.support, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀`. Establish `e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r)`. Rewrite using `[← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]`. Simplify using `only [mul_assoc]`. Rewrite using `[e0, _root_.GlobalTheory.T.bottomIntegral_leftInvariant_rationalPoints hP hI hL hX t _ γ hγ, hcE]`.

Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[hℓ, mul_assoc]`. Use `⟨fun h' k' => if h' = h₀ then c k' * ℓ else 0, fun a b => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`. Conclude with `mul_mem ((le_sup_left : M₁ ≤ M₁ ⊔ M₂) (hcM b)) ((le_sup_right : M₂ ≤ M₁ ⊔ M₂) hℓM)`.

Conclude with `zero_mem _`. Rewrite using `[e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]`. Simplify using `only [if_true]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finsupp.notMem_support_iff.1 hk', zero_mul, zero_mul]`.

Use `_ = ∑ k' ∈ K, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by`. Rewrite using `[hK t h₀ (hH h₀ hh₀) k' hk', mul_zero]).symm`.
-/
theorem classSums_span_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  classical
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.bottomClassSum_finite_support hP hI hL hX
  obtain ⟨M₁, hM₁, hr⟩ := _root_.GlobalTheory.T.realTranslate_preserves_rationalAction hP hI hL hX
  obtain ⟨J, M₂, hJ, hM₂, hl⟩ := _root_.GlobalTheory.T.bottomForm_rightTranslate_level hP hI hL hX
  obtain ⟨H, hH, hc⟩ := _root_.GlobalTheory.T.bottomClasses_finite hP hI hL hX J hJ
  refine ⟨H, K, M₁ ⊔ M₂, IntermediateField.finiteDimensional_sup M₁ M₂, hH, ?_⟩
  intro t h hh k
  obtain ⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩ := hc h hh
  have hx : h₀ * κ ∈ GfC WW := mul_mem (hH h₀ hh₀) hκf
  have hγr : γ * r ∈ GfC WW := by
    have e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹ := by group
    rw [e]; exact mul_mem hh (inv_mem hx)
  obtain ⟨c, hcM, hcE⟩ := hr t γ hγ r hrI hγr (h₀ * κ) k
  obtain ⟨ℓ, hℓM, hℓ⟩ := hl t κ hκJ hκf
  have e1 : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) =
      ∑ k' ∈ c.support, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := by
    have e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r) := by
      rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]; simp only [mul_assoc]
    rw [e0, _root_.GlobalTheory.T.bottomIntegral_leftInvariant_rationalPoints hP hI hL hX t _ γ hγ, hcE]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hℓ, mul_assoc]
  refine ⟨fun h' k' => if h' = h₀ then c k' * ℓ else 0, fun a b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact mul_mem ((le_sup_left : M₁ ≤ M₁ ⊔ M₂) (hcM b)) ((le_sup_right : M₂ ≤ M₁ ⊔ M₂) hℓM)
    · exact zero_mem _
  rw [e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]
  simp only [if_true]
  calc ∑ k' ∈ c.support, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀
      = ∑ k' ∈ c.support ∪ K, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        Finset.sum_subset Finset.subset_union_left fun k' _ hk' => by
          rw [Finsupp.notMem_support_iff.1 hk', zero_mul, zero_mul]
    _ = ∑ k' ∈ K, c k' * ℓ * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by
          rw [hK t h₀ (hH h₀ hh₀) k' hk', mul_zero]).symm
end GlobalTheory.BotSpan
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.BotSpan.classSums_span_bottom | exact _root_.GlobalTheory.BotSpan.classSums_span_bottom | (intros; apply _root_.GlobalTheory.BotSpan.classSums_span_bottom <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.bottom_spanned_by_classSums : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  first | exact @_root_.GlobalTheory.BotSpan.classSums_span_bottom | exact _root_.GlobalTheory.BotSpan.classSums_span_bottom | (intros; apply _root_.GlobalTheory.BotSpan.classSums_span_bottom <;> assumption)
end
