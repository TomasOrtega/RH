import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g`. Establish `hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι`. Take `⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩` from `hC`. Conclude with `⟨hθ, hι⟩`. Take `⟨x, y, hx, hg, -⟩` from `hD D n θ τ ι hθι.1 hθι.2 g`.

Take `⟨A, hA'⟩` from `hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx`. Conclude with `⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩`.
-/
theorem awayFact_of (hA : AwayAct) (hD : DecompAway) : AwayFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  have hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι := by
    obtain ⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩ := hC
    exact ⟨hθ, hι⟩
  obtain ⟨x, y, hx, hg, -⟩ := hD D n θ τ ι hθι.1 hθι.2 g
  obtain ⟨A, hA'⟩ := hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx
  exact ⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩

end PositivityTheory.Rg.Sw.Glob
