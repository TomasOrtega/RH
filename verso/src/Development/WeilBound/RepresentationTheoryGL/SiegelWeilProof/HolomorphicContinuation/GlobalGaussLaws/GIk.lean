import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk`. Establish `key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P)`. Establish `h1` using `hL k Ψ hΨ P`. Rewrite `h1` using `[hρ k P hk]`. Establish `hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n`.

Rewrite using `[← h1]`. Conclude with `(ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[h1]`. Unfold `phiS`.

Rewrite using `[dif_pos hmem]`. Unfold `thF thetaInt theta`. Simplify using `only [map_mul, Module.End.mul_apply, key]`.
-/
theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dif_pos hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

end PositivityTheory.Rg.Sw.Glob
