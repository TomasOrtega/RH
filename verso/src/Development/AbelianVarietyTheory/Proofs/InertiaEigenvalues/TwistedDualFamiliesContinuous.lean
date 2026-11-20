import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.FamCont

/- English proof (translation)
Establish `h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) = ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i)`. Introduce `g`. Use `R.rank_add_five_le` as an intermediate fact. Rewrite using `[← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]`. Simplify using `[Glob.epsO]`.

Simplify using `only [h]`. Conclude with `(N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)`.
-/
theorem epsU_cont {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    Continuous fun g => ((epsU N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := R.rank_add_five_le
    rw [← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]
    simp [Glob.epsO]
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

/- English proof (translation)
Introduce `D i r hr x`. Establish `hc` using `(hr x).1`. Prove the components needed by the constructor for the conclusion. Establish `h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)` using `(D.nd.chi_cont i 1).comp continuous_inv`. Use `(h1.smul hc).congr fun g => ?_` and prove the remaining obligations.

Simplify using `[rTwO, twistM, rO]`. Establish `h1` using `(D.nd.chi_cont i 1).mul (epsU_cont D.nd i)`. Establish `h2` using `(hc.comp continuous_inv).matrix_transpose`. Use `(h1.smul h2).congr fun g => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem stepCont : StepCont := by
  intro D i r hr x
  have hc := (hr x).1
  constructor
  · have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
      (D.nd.chi_cont i 1).comp continuous_inv
    refine (h1.smul hc).congr fun g => ?_
    simp [rTwO, twistM, rO]
  · have h1 := (D.nd.chi_cont i 1).mul (epsU_cont D.nd i)
    have h2 := (hc.comp continuous_inv).matrix_transpose
    refine (h1.smul h2).congr fun g => ?_
    rfl

end GlobalTheory.Pass.FamCont

end
