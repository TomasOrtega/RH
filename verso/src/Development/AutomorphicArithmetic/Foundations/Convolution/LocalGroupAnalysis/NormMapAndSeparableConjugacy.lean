import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
open PositivityTheory.Rg.Tf.Geo

open PositivityTheory.Rg.Tf.Loc in
/- English proof (translation)
Unfold `UpperTheory.ConvolutionTheory.D.nm twNorm`. Use `congr 1`. Use `List.map_congr_left fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sigmaGL_pow]`. Both sides reduce to the same expression.
-/
private theorem nm_eq_normGL {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n q : ℕ)
    (d : GL (Fin n) E) : UpperTheory.ConvolutionTheory.D.nm σ q d = twNorm (sigmaGL σ) q d := by
  unfold UpperTheory.ConvolutionTheory.D.nm twNorm
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← sigmaGL_pow]
  rfl

open PositivityTheory.Rg.Tf.Loc in
/- English proof (translation)
Introduce `k E _ _ _ _ _ _ σ hσ n`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `δ δ' γ hγ h1 h2`. Establish `hg` using `UpperTheory.ConvolutionTheory.D.galField k E σ hσ`. Establish `e : ∀ d : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) d = normGL σ d` using `fun d => nm_eq_normGL σ n _ d`.

Establish `hsep : (UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) δ)).Separable`. Rewrite using `[e, h1]`. Establish `hm : UpperTheory.ConvolutionTheory.D.cp (incl γ : GL (Fin n) E) = ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E)`. Rewrite using `[← Matrix.charpoly_map]`. Both sides reduce to the same expression.

Rewrite using `[hm]`. Conclude with `hγ.map`. Take `⟨x, hx⟩` from `UpperTheory.ConvolutionTheory.D.nmInj k E σ _ hg n δ δ' hsep (by rw [e, e, h1, h2])`. Conclude with `⟨x, hx⟩`. Introduce `γ γ' hγ hc`.

Take `⟨x, hx⟩` from `(UpperTheory.ConvolutionTheory.D.conjSep k k n (γ : Matrix (Fin n) (Fin n) k) hγ).1 γ' hc.symm`. Establish `hx' : γ * x = x * γ'` using `Units.ext hx`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hx', inv_mul_cancel_left]`.
-/
theorem UpperTheory.ConvolutionTheory.G.nm_agrees_with_twisted_norm_sigmaGL :
    N2 := by
  intro k E _ _ _ _ _ _ σ hσ n
  refine ⟨?_, ?_⟩
  · intro δ δ' γ hγ h1 h2
    have hg := UpperTheory.ConvolutionTheory.D.galField k E σ hσ
    have e : ∀ d : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) d = normGL σ d :=
      fun d => nm_eq_normGL σ n _ d
    have hsep : (UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) δ)).Separable := by
      rw [e, h1]
      have hm : UpperTheory.ConvolutionTheory.D.cp (incl γ : GL (Fin n) E) =
          ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E) := by
        rw [← Matrix.charpoly_map]
        rfl
      rw [hm]
      exact hγ.map
    obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ hg n δ δ' hsep (by rw [e, e, h1, h2])
    exact ⟨x, hx⟩
  · intro γ γ' hγ hc
    obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n (γ : Matrix (Fin n) (Fin n) k) hγ).1 γ' hc.symm
    have hx' : γ * x = x * γ' := Units.ext hx
    refine ⟨x, ?_⟩
    rw [mul_assoc, hx', inv_mul_cancel_left]
