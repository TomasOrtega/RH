import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

/- English proof (translation)
Introduce `ι _ f k`. Establish `hlin : ∀ v : ι → ℝ, (lin v).IsHomogeneous 1` using `fun v => IsHomogeneous.sum _ _ _ fun i _ => by`. Simplify using `using (isHomogeneous_C ι ((v i : ℝ) : ℂ)).mul (isHomogeneous_X ℂ i)`. Unfold `piece Finsupp.sum`. Use `IsHomogeneous.sum _ _ _ fun v _ => IsHomogeneous.sum _ _ _ fun b hb => ?_` and prove the remaining obligations.

Establish `hbk : b ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)`. Establish `h` using `(homogeneousComponent_isHomogeneous (k - b) (f.coeff v)).mul ((isHomogeneous_C ι ((b.factorial : ℂ)⁻¹)).mul ((hlin v).pow b))`. Establish `e : k - b + (0 + 1 * b) = k` using `by omega`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.ConvolutionTheory.FX.piece_hom :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (k : ℕ), (piece k f).IsHomogeneous k := by
  intro ι _ f k
  have hlin : ∀ v : ι → ℝ, (lin v).IsHomogeneous 1 := fun v =>
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_C ι ((v i : ℝ) : ℂ)).mul (isHomogeneous_X ℂ i)
  unfold piece Finsupp.sum
  refine IsHomogeneous.sum _ _ _ fun v _ => IsHomogeneous.sum _ _ _ fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h := (homogeneousComponent_isHomogeneous (k - b) (f.coeff v)).mul
    ((isHomogeneous_C ι ((b.factorial : ℂ)⁻¹)).mul ((hlin v).pow b))
  have e : k - b + (0 + 1 * b) = k := by omega
  rwa [e] at h
