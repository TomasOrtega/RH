import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

/- English proof (translation)
Establish `hAe : A = (A.map Complex.re).map (Complex.ofRealHom : ℝ →+* ℂ)`. Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [hA i j]`. Rewrite using `[hAe, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]`. Simplify using the standard rewrite rules.
-/
theorem im_pow_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, (A i j).im = 0) (k : ℕ) (i j : Fin n) :
    ((A ^ k) i j).im = 0 := by
  have hAe : A = (A.map Complex.re).map (Complex.ofRealHom : ℝ →+* ℂ) := by
    ext i j
    apply Complex.ext <;> simp [hA i j]
  rw [hAe, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp

/- English proof (translation)
Establish `hχ : ∀ s a, (infOf lam s a).im = 0`. Introduce `s a`. Apply the tactic sequence `cases s <;> simp [infOf]`. Establish `hg : ∀ s, (GlobalTheory.Dec.gelfVal (infOf lam s) 2).im = 0`. Introduce `s`.

Unfold `GlobalTheory.Dec.gelfVal`. Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Apply `im_pow_entry` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp [hχ]`. Simplify using `[cas, hg]`.
-/
theorem cas_infOf_im' {n : ℕ} (lam : Fin n → ℤ) : (cas (infOf lam)).im = 0 := by
  have hχ : ∀ s a, (infOf lam s a).im = 0 := by
    intro s a
    cases s <;> simp [infOf]
  have hg : ∀ s, (GlobalTheory.Dec.gelfVal (infOf lam s) 2).im = 0 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    apply im_pow_entry
    intro i j
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs <;> simp [hχ]
  simp [cas, hg]

end PositivityTheory.Rg.BcB.F.F0

end
