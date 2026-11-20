import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ`. Establish `hfr : IsUnit fr.det` using `hC.hfr.1`. Establish `hΨ` using `LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ`. Establish `mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n` using `fun P => (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1`.

Use `⟨fun y a P Q => ?_, fun P => ?_⟩` and prove the remaining obligations. Apply `LocLawH.tens_cancel hσ V l s τ hfr` to reduce the goal to its premises. Establish `hlin : phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (a • P + Q) = a • phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) Q`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[LocLawH.phiS_val (mem _), Submodule.coe_add, Submodule.coe_smul, LocLawH.phiS_val (mem P), LocLawH.phiS_val (mem Q)]`.

Use function extensionality and compare the values at `x`. Simplify using `only [tens, fP, evX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, MvPolynomial.smul_eval]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hL y _ hΨ (a • P + Q), hlin, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hL y _ hΨ P, hL y _ hΨ Q]`. Use function extensionality and compare the values at `x`.

Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `show a * (L y (fP (cLoc l τ) P) _ * _) + L y (fP (cLoc l τ) Q) _ * _ = (a * L y (fP (cLoc l τ) P) _ + L y (fP (cLoc l τ) Q) _) * _`. Expand and normalize the polynomial expressions, which then agree. Apply `LocLawH.tens_cancel hσ V l s τ hfr` to reduce the goal to its premises. Establish `e` using `hL 1 _ hΨ P`.

Rewrite `e` using `[map_one, map_one, Module.End.one_apply, LocLawH.phiS_val (mem P)]`. Conclude with `e.symm`.
-/
theorem lIlin : LIlin := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hfr : IsUnit fr.det := hC.hfr.1
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  refine ⟨fun y a P Q => ?_, fun P => ?_⟩
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have hlin : phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (a • P + Q) =
        a • phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) Q := by
      apply Subtype.ext
      rw [LocLawH.phiS_val (mem _), Submodule.coe_add, Submodule.coe_smul, LocLawH.phiS_val (mem P), LocLawH.phiS_val (mem Q)]
      funext x
      simp only [tens, fP, evX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, MvPolynomial.smul_eval]
      ring
    rw [← hL y _ hΨ (a • P + Q), hlin, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hL y _ hΨ P,
      hL y _ hΨ Q]
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show a * (L y (fP (cLoc l τ) P) _ * _) + L y (fP (cLoc l τ) Q) _ * _ =
      (a * L y (fP (cLoc l τ) P) _ + L y (fP (cLoc l τ) Q) _) * _
    ring
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have e := hL 1 _ hΨ P
    rw [map_one, map_one, Module.End.one_apply, LocLawH.phiS_val (mem P)] at e
    exact e.symm

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P`. Establish `hΨ` using `LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ`. Establish `key : sLd L (cLoc l τ) P = fun y => (ω (ι y) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0`. Use function extensionality and compare the values at `y`. Rewrite using `[hL y _ hΨ P, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[key]`. Take `⟨𝓕, h𝓕⟩` from `hC.hμ`. Conclude with `(GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 h𝓕 ω hC.hω (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).comp hC.hι.1`.
-/
theorem lIcont : LIcont := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have key : sLd L (cLoc l τ) P = fun y => (ω (ι y) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 := by
    funext y
    rw [hL y _ hΨ P, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
    rfl
  rw [key]
  obtain ⟨𝓕, h𝓕⟩ := hC.hμ
  exact (GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 h𝓕 ω hC.hω
    (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).comp hC.hι.1

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk`. Establish `hΨ` using `LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ`. Establish `mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n` using `fun P => (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1`. Establish `hk' : ω (ι k) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P) = phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P)`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hL k _ hΨ P, hρ k P hk, LocLawH.phiS_val (mem _)]`. Establish `e : (ω (ι (g * k)) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 = (ω (ι g) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P))).1 0`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, hk']`. Rewrite `e` using `[hL (g * k) _ hΨ P, hL g _ hΨ (ρ k P), LocLawH.tens_zero, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one, mul_one]`. Conclude with `e`.
-/
theorem lIkact : LIkact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  have hk' : ω (ι k) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P) =
      phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P) := by
    apply Subtype.ext
    rw [hL k _ hΨ P, hρ k P hk, LocLawH.phiS_val (mem _)]
  have e : (ω (ι (g * k)) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 =
      (ω (ι g) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P))).1 0 := by
    rw [map_mul, map_mul, Module.End.mul_apply, hk']
  rw [hL (g * k) _ hΨ P, hL g _ hΨ (ρ k P), LocLawH.tens_zero, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one, mul_one] at e
  exact e

end PositivityTheory.Rg.Sw.Glob
