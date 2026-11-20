import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInD

noncomputable section

open scoped Matrix ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ`. Use `⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩` and prove the remaining obligations. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem φ hφ`. Take `⟨p, g, hg, hp, rfl⟩` from `hφ`.

Conclude with `AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf`. Consider the case `zero`. Establish `: tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0`. Use function extensionality and compare the values at `x`. Simplify using `[tens]`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `: tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b`. Use function extensionality and compare the values at `x`.

Simplify using `only [tens, Pi.add_apply, mul_add]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `: tens θ τ fr f (c • a) = c • tens θ τ fr f a`.

Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem awayIn : AwayIn := by
  intro D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ
  refine ⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, hp, rfl⟩ := hφ
    exact AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf
  | zero =>
    have : tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [tens]
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b := by
      funext x
      simp only [tens, Pi.add_apply, mul_add]
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens θ τ fr f (c • a) = c • tens θ τ fr f a := by
      funext x
      simp only [tens, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ c ha

end PositivityTheory.Rg.Sw.Glob
