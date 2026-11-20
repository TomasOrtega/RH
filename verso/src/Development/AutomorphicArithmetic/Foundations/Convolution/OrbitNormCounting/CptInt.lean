import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

/- English proof (translation)
Unfold `nrmL locEl`. Use `split_ifs with hs`. Both sides reduce to the same expression. Establish `hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ)` using `(GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm`. Rewrite using `[hm, ← map_mul]`.
-/
private theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  unfold nrmL locEl
  split_ifs with hs
  · rfl
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]

/- English proof (translation)
Introduce `E _ _ _ hU n δ hs`. Establish `hs' : (δ * thE E n δ).val.charpoly.Separable` using `hs`. Use `filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E _ hs', GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hb hK`. Take `⟨-, hinv, -, -, -, hKc, -⟩` from `GlobalTheory.BCT.ThBasic.twist_basic E hU n w`. Establish `hNe` using `nrmL_locEl hU n w δ`.

Establish `hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n` using `hNe ▸ hK`. Establish `hgood : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1`. Establish `e : (nrmL n w (locEl n w δ)).val.charpoly = (δ * thE E n δ).val.charpoly.map (algebraMap E (w.adicCompletion E))`. Rewrite using `[hNe]`. Conclude with `Matrix.charpoly_map _ _`.

Rewrite using `[e]`. Conclude with `hb`. Establish `hcomm : ∀ t ∈ twCent (thL n w) (locEl n w δ), t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t`. Introduce `t ht`. Establish `ht' : t * locEl n w δ = locEl n w δ * thL n w t` using `ht`.

Generalize the expression as in `locEl n w δ = y at ht' ⊢`. Distinguish the cases in `hsp : IsSplitAt w`. Establish `hθ1 : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hsp]`. Establish `hn1 : nrmL n w y = y` using `by unfold nrmL; rw [if_pos hsp]`. Rewrite using `[hn1]`.

Rewrite `ht'` using `[hθ1]`. Simplify using `using ht'`. Establish `hn1 : nrmL n w y = y * thL n w y`. Unfold `nrmL`. Rewrite using `[if_neg hsp]`.

Unfold `thL`. Rewrite using `[if_neg hsp]`. Rewrite using `[hn1]`. Combine the equalities or inequalities in the displayed calculation. Use `le_antisymm (le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)) ?_` and prove the remaining obligations.

Conclude with `GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hgood (hcomm t ht.1) ht.2`. Introduce `t ht`. Use `Subgroup.subset_closure ⟨ht.1, ?_⟩` and prove the remaining obligations. Use `hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)` and prove the remaining obligations. Conclude with `(Subgroup.zpowers_le.2 ht.2 : _)`.
-/
theorem UpperTheory.ConvolutionTheory.G3.cptInt :
    UpperTheory.ConvolutionTheory.G3.CptInt := by
  intro E _ _ _ hU n δ hs
  have hs' : (δ * thE E n δ).val.charpoly.Separable := hs
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E _ hs', GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hb hK
  obtain ⟨-, hinv, -, -, -, hKc, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hNe := nrmL_locEl hU n w δ
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := hNe ▸ hK
  have hgood : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (nrmL n w (locEl n w δ)).val.charpoly =
        (δ * thE E n δ).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
      rw [hNe]; exact Matrix.charpoly_map _ _
    rw [e]; exact hb
  have hcomm : ∀ t ∈ twCent (thL n w) (locEl n w δ),
      t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
    intro t ht
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    generalize locEl n w δ = y at ht' ⊢
    by_cases hsp : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hsp]
      have hn1 : nrmL n w y = y := by unfold nrmL; rw [if_pos hsp]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w y = y * thL n w y := by
        unfold nrmL; rw [if_neg hsp]; unfold thL; rw [if_neg hsp]
      rw [hn1]
      calc t * (y * thL n w y) = y * thL n w t * thL n w y := by rw [← mul_assoc, ht']
        _ = y * thL n w (t * y) := by simp only [map_mul, mul_assoc]
        _ = y * thL n w (y * thL n w t) := by rw [ht']
        _ = y * thL n w y * t := by simp only [map_mul, hinv, mul_assoc]
  refine le_antisymm (le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)) ?_
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hgood (hcomm t ht.1) ht.2
  · intro t ht
    refine Subgroup.subset_closure ⟨ht.1, ?_⟩
    refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
    exact (Subgroup.zpowers_le.2 ht.2 : _)
