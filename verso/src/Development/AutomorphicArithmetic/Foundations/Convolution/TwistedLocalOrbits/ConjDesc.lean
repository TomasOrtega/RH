import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `k E _ _ _ n γ γ' hγ ⟨h, hh⟩`. Establish `hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly`. Apply `Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective` to reduce the goal to its premises. Rewrite using `[← Matrix.charpoly_map, ← Matrix.charpoly_map]`. Establish `e` using `congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh`.

Simplify using `only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e`. Conclude with `e`. Take `⟨x, hx⟩` from `(UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc`. Use `⟨x⁻¹, ?_⟩` and prove the remaining obligations. Establish `: γ * x = x * γ'` using `Units.ext hx`.

Rewrite using `[inv_inv, mul_assoc, this, inv_mul_cancel_left]`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.conjDesc :
    ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n : ℕ) (γ γ' : GL (Fin n) k), IsRegSemisimple γ →
      (∃ h : GL (Fin n) E, incl γ' = h * incl γ * h⁻¹) → ∃ y : GL (Fin n) k, γ' = y * γ * y⁻¹ := by
  intro k E _ _ _ n γ γ' hγ ⟨h, hh⟩
  have hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly := by
    apply Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    have e := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e
    exact e
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc
  refine ⟨x⁻¹, ?_⟩
  have : γ * x = x * γ' := Units.ext hx
  rw [inv_inv, mul_assoc, this, inv_mul_cancel_left]
