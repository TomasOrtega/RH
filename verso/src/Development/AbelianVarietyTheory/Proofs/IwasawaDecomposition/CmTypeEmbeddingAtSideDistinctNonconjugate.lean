import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`.
-/
theorem complexConj_eq_hostConj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

/- English proof (translation)
Introduce `D T i b`. Establish `hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D))` using `RingHom.injective _`. Establish `hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h`. Introduce `g h e`. Conclude with `Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)`.

Establish `hk : ∀ t x, kEmbT D T i b t x = ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x)` using `fun _ _ => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `t t' e`. Apply `D.eTau.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hS` to reduce the goal to its premises. Introduce `x`. Apply `hR` to reduce the goal to its premises. Rewrite using `[← hk, ← hk, e]`. Introduce `t t' e`.

Establish `h1 : ((D.eTau t : D.R.Psi) : D.R.GG) = ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc`. Apply `hS` to reduce the goal to its premises. Introduce `x`. Apply `hR` to reduce the goal to its premises. Rewrite using `[← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf, ← complexConj_eq_hostConj D x]`.

Conclude with `DFunLike.congr_fun e x`. Establish `ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1` using `(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2`. Establish `ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1` using `(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2`. Establish `h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1)` using `by rw [h1]; rfl`. Rewrite `h2` using `[ht, ht']`.

Conclude with `absurd h2 (by decide)`.
-/
theorem kEmbT_cmDist : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  intro D T i b
  have hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) := RingHom.injective _
  have hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h := by
    intro g h e
    exact Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)
  have hk : ∀ t x, kEmbT D T i b t x =
      ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro t t' e
    apply D.eTau.injective
    apply Subtype.ext
    apply hS
    intro x
    apply hR
    rw [← hk, ← hk, e]
  · intro t t' e
    have h1 : ((D.eTau t : D.R.Psi) : D.R.GG) =
        ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc := by
      apply hS
      intro x
      apply hR
      rw [← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf,
        ← complexConj_eq_hostConj D x]
      exact DFunLike.congr_fun e x
    have ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2
    have ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2
    have h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 =
        ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [ht, ht'] at h2
    exact absurd h2 (by decide)

end GlobalTheory.HeightCounting.FormsStep
