import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocGoodP

/- English proof (translation)
Take `⟨-, -, hKθ, -⟩` from `GlobalTheory.BCT.ThBasic.twist_basic E hU n w`. Unfold `nrmL`. Use `split_ifs with hs`. Conclude with `hz`. Establish `: thetaGL n (cj w) z = thL n w z` using `by unfold thL; rw [if_neg hs]`.

Rewrite using `[this]`. Conclude with `(GlobalTheory.LFun.KGL w n).mul_mem hz (hKθ _ hz)`.
-/
theorem nrmL_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z : GLw n w) (hz : z ∈ GlobalTheory.LFun.KGL w n) : nrmL n w z ∈ GlobalTheory.LFun.KGL w n := by
  obtain ⟨-, -, hKθ, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  unfold nrmL
  split_ifs with hs
  · exact hz
  · have : thetaGL n (cj w) z = thL n w z := by unfold thL; rw [if_neg hs]
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem hz (hKθ _ hz)

/- English proof (translation)
Take `⟨-, hinv, -⟩` from `GlobalTheory.BCT.ThBasic.twist_basic E hU n w`. Establish `ht' : t * z = z * thL n w t` using `ht`. Distinguish the cases in `hs : IsSplitAt w`. Establish `hθ1 : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hs]`. Establish `hn1 : nrmL n w z = z` using `by unfold nrmL; rw [if_pos hs]`.

Rewrite using `[hn1]`. Rewrite `ht'` using `[hθ1]`. Simplify using `using ht'`. Establish `hn1 : nrmL n w z = z * thL n w z`. Unfold `nrmL`.

Rewrite using `[if_neg hs]`. Unfold `thL`. Rewrite using `[if_neg hs]`. Rewrite using `[hn1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commute_nrmL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z t : GLw n w) (ht : t ∈ twCent (thL n w) z) : t * nrmL n w z = nrmL n w z * t := by
  obtain ⟨-, hinv, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have ht' : t * z = z * thL n w t := ht
  by_cases hs : IsSplitAt w
  · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
    rw [hn1]; rw [hθ1] at ht'; simpa using ht'
  · have hn1 : nrmL n w z = z * thL n w z := by
      unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
    rw [hn1]
    calc t * (z * thL n w z) = z * thL n w t * thL n w z := by rw [← mul_assoc, ht']
      _ = z * thL n w (t * z) := by simp only [map_mul, mul_assoc]
      _ = z * thL n w (z * thL n w t) := by rw [ht']
      _ = z * thL n w z * t := by simp only [map_mul, hinv, mul_assoc]

end PositivityTheory.Rg.BcB.G3.LocGoodP

open PositivityTheory.Rg.BcB.G3.LocGoodP in
/- English proof (translation)
Introduce `E _ _ _ hU n P hP`. Use `filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1, GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep`. Introduce `z hzK hz`. Establish `hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1`. Rewrite using `[hz]`.

Conclude with `hgood`. Establish `hNK` using `nrmL_mem hU n w z hzK`. Use `⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : IsSplitAt w`. Establish `hθ1 : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hs]`.

Establish `hn1 : nrmL n w z = z` using `by unfold nrmL; rw [if_pos hs]`. Rewrite `hgood₀` using `[hn1]`. Rewrite `hg` using `[hθ1]`. Take `⟨t, ht, k, hk, rfl⟩` from `GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg`. Use `⟨t, ?_, k, hk, rfl⟩` and prove the remaining obligations.

Use `show t * z = z * thL n w t`. Rewrite using `[hθ1]`. Conclude with `ht`. Conclude with `GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg`. Conclude with `GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc`.

Conclude with `GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK`.
-/
theorem PositivityTheory.Rg.BcB.G3.locGood_pf : LocGood := by
  intro E _ _ _ hU n P hP
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1,
    GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep
  intro z hzK hz
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1 := by
    rw [hz]; exact hgood
  have hNK := nrmL_mem hU n w z hzK
  refine ⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg
      refine ⟨t, ?_, k, hk, rfl⟩
      show t * z = z * thL n w t
      rw [hθ1]; exact ht
    · exact GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc
  · exact GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK
