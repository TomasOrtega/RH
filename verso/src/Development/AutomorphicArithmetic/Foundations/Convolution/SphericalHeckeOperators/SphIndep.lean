import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Introduce `K _ _ n w p h hs inst instB m instH hm`. Take `⟨i', b', m', h', hm', H, hH⟩` from `hs`. Establish `e : i' = inst` using `(@BorelSpace.measurable_eq _ _ i' b').trans (@BorelSpace.measurable_eq _ _ inst instB).symm`. Substitute `e` using the available equality. Establish `hmm : m' = m`.

Establish `h1` using `Measure.isMulLeftInvariant_eq_smul m' m`. Establish `h2` using `congrArg (fun μ : Measure (GL (Fin n) (w.adicCompletion K)) => μ (GLnLocal.integralGL (w.adicCompletion K) n)) h1`. Simplify using `only [Measure.smul_apply, hm, hm'] at h2`. Establish `h3 : Measure.haarScalarFactor m' m = 1`. Simplify `h2.symm` using `[ENNReal.smul_def]`.

Rewrite using `[h1, h3, one_smul]`. Substitute `hmm` using the available equality. Conclude with `⟨H, hH⟩`.
-/
theorem UpperTheory.ConvolutionTheory.H.sphIndep :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.adicCompletion K) → ℂ),
      GM.IsSph w p h → ∀ [MeasurableSpace (GL (Fin n) (w.adicCompletion K))] [BorelSpace (GL (Fin n) (w.adicCompletion K))]
        (m : Measure (GL (Fin n) (w.adicCompletion K))) [m.IsHaarMeasure], m (GLnLocal.integralGL (w.adicCompletion K) n) = 1 →
        ∃ H : SphericalHecke m (F := w.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧ satakeTransform m H = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  intro K _ _ n w p h hs inst instB m instH hm
  obtain ⟨i', b', m', h', hm', H, hH⟩ := hs
  have e : i' = inst := (@BorelSpace.measurable_eq _ _ i' b').trans (@BorelSpace.measurable_eq _ _ inst instB).symm
  subst e
  have hmm : m' = m := by
    have h1 := Measure.isMulLeftInvariant_eq_smul m' m
    have h2 := congrArg (fun μ : Measure (GL (Fin n) (w.adicCompletion K)) => μ (GLnLocal.integralGL (w.adicCompletion K) n)) h1
    simp only [Measure.smul_apply, hm, hm'] at h2
    have h3 : Measure.haarScalarFactor m' m = 1 := by
      simpa [ENNReal.smul_def] using h2.symm
    rw [h1, h3, one_smul]
  subst hmm
  exact ⟨H, hH⟩
