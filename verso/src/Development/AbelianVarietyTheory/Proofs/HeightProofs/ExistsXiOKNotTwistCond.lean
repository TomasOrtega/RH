import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FieldTwistConditions
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Formalism.LocalRingCardinality.HostCls

noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

variable {D : D7}

def Reformulated (D : D7) (p : ℕ) : Prop := p = D.host.pde ∨ p = D.host.pde'

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[GlobalTheory.XiCounterexample.conj_emb]`. Conclude with `(D.host.conjE_apply D.host.φ₀ a).symm`.
-/
theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

/- English proof (translation)
Rewrite using `[← cF_eq]`. Both sides reduce to the same expression.
-/
theorem barF_tmul (a : Af D.host.F) (e : D.host.E) :
    barF D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] D.host.conj e := by
  rw [← cF_eq]; rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a e => rw [barF_tmul, ← D.conjF_eq]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem bar_eq (x : AfE D) : FieldTwistConditions.bar D x = barF D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [barF_tmul, ← D.conjF_eq]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Unfold `FieldTwistConditions.NormOne NormOne`. Rewrite using `[bar_eq]`.
-/
theorem normOne_iff (x : (AfE D)ˣ) : FieldTwistConditions.NormOne D x ↔ NormOne x := by
  unfold FieldTwistConditions.NormOne NormOne
  rw [bar_eq]

def UnramOff (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop := ∀ x, NormOne x → CongOne p x → xi x = 1

def OrderFifteen (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ n : ℕ, (∀ u, FieldTwistConditions.InertiaAt D v u → xi u ^ n = 1) ↔ 15 ∣ n

end GlobalTheory.TwistFieldCompare
