import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussM

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

/- English proof (translation)
Take `⟨S, hS⟩` from `hf`. Conclude with `⟨c • S, by funext u; simp [hS]⟩`.
-/
theorem isSch_smul {m : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (c : ℂ) : IsSch (fun u => c * f u) := by
  obtain ⟨S, hS⟩ := hf
  exact ⟨c • S, by funext u; simp [hS]⟩

/- English proof (translation)
Establish `hcf` using `isSch_smul hf c`. Use `hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_` and prove the remaining obligations. Rewrite using `[← hL.2 y Ψ hΨ _ hcf]`. Establish `e : (⟨tens θ τ fr (fun u => c * f u) Ψ, hΨ.2 _ hcf⟩ : schwartzA θ V.rank n) = c • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`. Rewrite using `[e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf]`. Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`.
-/
theorem locLin (hTI : TensInj) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) (y : GR n) (c : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    L y (fun u => c * f u) = fun u => c * L y f u := by
  have hcf := isSch_smul hf c
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ _ hcf]
  have e : (⟨tens θ τ fr (fun u => c * f u) Ψ, hΨ.2 _ hcf⟩ : schwartzA θ V.rank n) = c • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ := by
    apply Subtype.ext
    funext x
    simp [tens, mul_assoc]
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf]
  funext x
  simp [tens, mul_assoc]

/- English proof (translation)
Simplify using `only [tLoc, cLoc, abs_mul, abs_of_pos Real.pi_pos, abs_two]`.
-/
theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  simp only [tLoc, cLoc, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem GR_ext {y y' : GR n} (h : mR y = mR y') : y = y' := Subtype.ext (Units.ext h)

end PositivityTheory.Rg.Sw.Glob.GaussH
