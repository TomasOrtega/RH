import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGContinuousInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralZeroOfDerivativeAlongConjCurve

open MeasureTheory GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM expG inG)

namespace GlobalTheory.PsCo.Pc1

/- English proof (translation)
Introduce `n ε μ _ s hs dt _ _ φ hφ`. Use `haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ`. Establish `hp` using `isProperOrbit_realUJ hs`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ hφ`.

Take `⟨Z, H, P, hZ, hH, rfl⟩` from `hφ`. Establish `hZ' : inG ε Z` using `(GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ`. Take `⟨hc, hinv⟩` from `GlobalTheory.expG_continuous_inv n ε Z hZ'`. Take `⟨hsh, hd⟩` from `GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH`. Establish `hb : bas ε H P ∈ ShapeM ε P.totalDegree` using `Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩`.

Take `⟨-, -, h1, h2⟩` from `GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb`. Take `⟨-, -, h3, h4⟩` from `GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh`. Use `hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_` and prove the remaining obligations. Establish `e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) = NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)` using `fun v => by`. Rewrite using `[← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']`.

Both sides reduce to the same expression. Simplify using `only [e]`. Conclude with `hd (toM g) u`. Consider the case `zero`. Establish `h` using `(hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0`.

Rewrite `h` using `[zero_mul, zero_smul]`. Conclude with `h`. Consider the case `add φ ψ _ _ h1 h2`. Establish `h` using `h1.add h2`. Rewrite `h` using `[add_zero]`.

Conclude with `h`. Consider the case `smul a φ _ h1`. Establish `h` using `h1.smul a`. Rewrite `h` using `[mul_zero]`. Conclude with `h`.
-/
theorem orbInt_adSpan_eq_zero : GlobalTheory.PsCo.Pc1.StOrbAd := by
  intro n ε μ _ s hs dt _ _ φ hφ
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ
  have hp := isProperOrbit_realUJ hs
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hφ
    have hZ' : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
    obtain ⟨hc, hinv⟩ := GlobalTheory.expG_continuous_inv n ε Z hZ'
    obtain ⟨hsh, hd⟩ := GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH
    have hb : bas ε H P ∈ ShapeM ε P.totalDegree := Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb
    obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh
    refine hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_
    have e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) =
        NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z) := fun v => by
      rw [← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']
      rfl
    simp only [e]
    exact hd (toM g) u
  | zero =>
    have h := (hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0
    rw [zero_mul, zero_smul] at h
    exact h
  | add φ ψ _ _ h1 h2 =>
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  | smul a φ _ h1 =>
    have h := h1.smul a
    rw [mul_zero] at h
    exact h

end GlobalTheory.PsCo.Pc1
