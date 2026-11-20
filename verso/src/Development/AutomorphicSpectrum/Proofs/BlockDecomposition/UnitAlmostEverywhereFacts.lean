import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitAEPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `filter_upwards [GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers E _ hP, GlobalTheory.BCT.GoodInt.eventually_mem_KGL δ, GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hgood hd hN`. Take `⟨-, hinv, hKθ, -, -, -, -, -, hchar, -⟩` from `GlobalTheory.BCT.ThBasic.twist_basic E hU n w`. Establish `hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w n`. Unfold `locEl`. Use `split_ifs`.

Conclude with `hN`. Conclude with `hd`. Establish `hgood' : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1`. Rewrite using `[hchar δ]`. Conclude with `hgood`.

Establish `hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n`. Unfold `nrmL`. Use `split_ifs with hs`. Conclude with `hy`. Establish `h2 : thetaGL n (cj w) (locEl n w δ) = thL n w (locEl n w δ)`.

Unfold `thL`. Rewrite using `[if_neg hs]`. Rewrite using `[h2]`. Conclude with `mul_mem hy (hKθ _ hy)`. Use `⟨hy, fun g hg => ?_, fun t ht hc => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hs : IsSplitAt w`. Establish `hθ1 : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hs]`. Establish `hn1 : nrmL n w (locEl n w δ) = locEl n w δ` using `by unfold nrmL; rw [if_pos hs]`. Rewrite `hgood'` using `[hn1]`. Rewrite `hg`, the goal using `[hθ1]`.

Take `⟨t, ht, k, hk, rfl⟩` from `GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w _ g hy hgood' hg`. Conclude with `⟨t, ht, by simpa using hk⟩`. Take `⟨t, ht, k, hk, rfl⟩` from `GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs _ g hy hgood' hg`. Conclude with `⟨t, ht, by simpa using hk⟩`. Use `GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w (locEl n w δ)) t hNK hgood' ?_ hc` and prove the remaining obligations.

Establish `ht' : t * locEl n w δ = locEl n w δ * thL n w t` using `ht`. Distinguish the cases in `hs : IsSplitAt w`. Establish `hθ1 : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hs]`. Establish `hn1 : nrmL n w (locEl n w δ) = locEl n w δ` using `by unfold nrmL; rw [if_pos hs]`. Rewrite using `[hn1]`.

Rewrite `ht'` using `[hθ1]`. Simplify using `using ht'`. Establish `hn1 : nrmL n w (locEl n w δ) = locEl n w δ * thL n w (locEl n w δ)`. Unfold `nrmL`. Rewrite using `[if_neg hs]`.

Unfold `thL`. Rewrite using `[if_neg hs]`. Rewrite using `[hn1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_one (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E)
    (hP : (δ * thE E n δ).val.charpoly.Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w n ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w n →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w n) ∧
      ∀ t ∈ twCent (thL n w) (locEl n w δ),
        IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) → t ∈ GlobalTheory.LFun.KGL w n := by
  filter_upwards [GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers E _ hP, GlobalTheory.BCT.GoodInt.eventually_mem_KGL δ,
    GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hgood hd hN
  obtain ⟨-, hinv, hKθ, -, -, -, -, -, hchar, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w n := by
    unfold locEl
    split_ifs
    · exact hN
    · exact hd
  have hgood' : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    rw [hchar δ]; exact hgood
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := by
    unfold nrmL
    split_ifs with hs
    · exact hy
    · have h2 : thetaGL n (cj w) (locEl n w δ) = thL n w (locEl n w δ) := by
        unfold thL; rw [if_neg hs]
      rw [h2]; exact mul_mem hy (hKθ _ hy)
  refine ⟨hy, fun g hg => ?_, fun t ht hc => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood'
      rw [hθ1] at hg ⊢
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
    · obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
  · refine GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w (locEl n w δ)) t hNK hgood' ?_ hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w (locEl n w δ) = locEl n w δ * thL n w (locEl n w δ) := by
        unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
      rw [hn1]
      calc t * (locEl n w δ * thL n w (locEl n w δ))
          = locEl n w δ * thL n w t * thL n w (locEl n w δ) := by rw [← mul_assoc, ht']
        _ = locEl n w δ * thL n w (t * locEl n w δ) := by simp only [map_mul, mul_assoc]
        _ = locEl n w δ * thL n w (locEl n w δ * thL n w t) := by rw [ht']
        _ = locEl n w δ * thL n w (locEl n w δ) * t := by simp only [map_mul, hinv, mul_assoc]

/- English proof (translation)
Use `(h.image continuous_fst).closure_of_subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩`.
-/
theorem isCompact_fst {A B : Type} [Group A] [TopologicalSpace A] [T2Space A] [Group B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  refine (h.image continuous_fst).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

/- English proof (translation)
Use `(h.image continuous_snd).closure_of_subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩`.
-/
theorem isCompact_snd {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] [T2Space B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  refine (h.image continuous_snd).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

/- English proof (translation)
Introduce `E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂`. Establish `e₁` using `eventually_one hU a δ₁ h₁.2.2.1`. Establish `e₂` using `eventually_one hU b δ₂ h₂.2.2.1`. Establish `hT : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite` using `Subtype.val_injective.tendsto_cofinite`. Use `filter_upwards [hT.eventually e₁, hT.eventually e₂] with w hw₁ hw₂ y hy`.

Substitute `hy` using the available equality. Take `⟨i₁, u₁, c₁⟩` from `hw₁`. Take `⟨i₂, u₂, c₂⟩` from `hw₂`. Use `⟨⟨i₁, i₂⟩, fun g hg => ?_, (Subgroup.closure_le _).2 ?_⟩` and prove the remaining obligations. Take `⟨t₁, ht₁, k₁⟩` from `u₁ g.1 hg.1`.

Take `⟨t₂, ht₂, k₂⟩` from `u₂ g.2 hg.2`. Use `⟨(t₁, t₂), ?_, ⟨k₁, k₂⟩⟩` and prove the remaining obligations. Conclude with `Prod.ext ht₁ ht₂`. Introduce and unpack `t ⟨ht, hc⟩`. Establish `ht' : t * _ = _ * _` using `ht`.

Conclude with `⟨c₁ t.1 (congrArg Prod.fst ht') (isCompact_fst t hc), c₂ t.2 (congrArg Prod.snd ht') (isCompact_snd t hc)⟩`.
-/
theorem main : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have e₁ := eventually_one hU a δ₁ h₁.2.2.1
  have e₂ := eventually_one hU b δ₂ h₂.2.2.1
  have hT : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [hT.eventually e₁, hT.eventually e₂] with w hw₁ hw₂ y hy
  subst hy
  obtain ⟨i₁, u₁, c₁⟩ := hw₁
  obtain ⟨i₂, u₂, c₂⟩ := hw₂
  refine ⟨⟨i₁, i₂⟩, fun g hg => ?_, (Subgroup.closure_le _).2 ?_⟩
  · obtain ⟨t₁, ht₁, k₁⟩ := u₁ g.1 hg.1
    obtain ⟨t₂, ht₂, k₂⟩ := u₂ g.2 hg.2
    refine ⟨(t₁, t₂), ?_, ⟨k₁, k₂⟩⟩
    exact Prod.ext ht₁ ht₂
  · rintro t ⟨ht, hc⟩
    have ht' : t * _ = _ * _ := ht
    exact ⟨c₁ t.1 (congrArg Prod.fst ht') (isCompact_fst t hc), c₂ t.2 (congrArg Prod.snd ht') (isCompact_snd t hc)⟩

end GlobalTheory.CompanionTheory.UnitAEPair

end
