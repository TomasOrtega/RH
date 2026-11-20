import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MapSubOneMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW.NRatW

def RatN {E : Type} [Field E] {n r : ℕ} (e K : Fin r → Fin n → E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a : Fin r, (M - 1) *ᵥ e a ∈ Submodule.span E (e '' {b | b < a})) ∧
  ∀ y : Fin n → E, (∀ a, ∑ j, K a j * y j = 0) → (M - 1) *ᵥ y ∈ Submodule.span E (Set.range e)

section Spec

variable {D : D7} (X : HidaSetting D)

def Kf {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) : Fin r → Fin X.B.I.n → X.B.I.E :=
  fun a j => ∑ i, star (x a i) * X.B.I.J i j

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem Kf_apply {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) (a : Fin r) (y : Fin X.B.I.n → X.B.I.E) :
    ∑ j, Kf X x a j * y j = hE X.B.I.cm.sig X.B.I.J (x a) y := by
  simp only [Kf, hE, Formalism.UG.hform, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem hE_swap (x y : Fin X.B.I.n → X.B.I.E) :
    hE X.B.I.cm.sig X.B.I.J x y = star (hE X.B.I.cm.sig X.B.I.J y x) := by
  have hJ : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := by
    intro i j
    have := congrFun (congrFun X.B.I.J_herm i) j
    simpa [Formalism.UG.cT, starRingEnd_apply] using this
  show (∑ i, ∑ j, star (x i) * X.B.I.J i j * y j) = star (∑ i, ∑ j, star (y i) * X.B.I.J i j * x j)
  rw [star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul, star_mul, star_star, hJ]
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem std (u : D.what₂.Word) : (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) :=
  MassDataLevelSSteps.FrameW.frameOf_isStd X u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hKf_f (u : D.what₂.Word) : ∀ a b, ∑ j, Kf X X.eR a j * X.fR b j = if a = b then 1 else 0 := by
  intro a b
  rw [Kf_apply]
  exact (std X u).2.2.1 a b

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem hK_e (u : D.what₂.Word) : ∀ c b, ∑ j, Kf X X.fR c j * X.eR b j = if c = b then 1 else 0 := by
  intro c b
  rw [Kf_apply, hE_swap]
  have := (std X u).2.2.1 b c
  change hE _ _ (X.eR b) (X.fR c) = _ at this
  rw [this]
  by_cases h : c = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_Kf_mul_zR_eq_zero (u : D.what₂.Word) : ∀ a, ∑ j, Kf X X.eR a j * X.zR u j = 0 := by
  intro a
  rw [Kf_apply]
  exact (std X u).2.2.2.1 a

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sigR_inclR (x : X.B.I.E) :
    sigR (AF X.B.I.F) X.B.I.cm.sig (inclR (AF X.B.I.F) x) = inclR (AF X.B.I.F) (X.B.I.cm.sig x) := by
  show (Algebra.TensorProduct.map (AlgHom.id X.B.I.F (AF X.B.I.F)) X.B.I.cm.sig)
      ((1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] x) = (1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] (X.B.I.cm.sig x)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hR_ratV_left (x : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    hR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (AF X.B.I.F) x) y =
      ∑ j, inclR (AF X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by
  simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, ratV, sigR_inclR, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem inclR_injective : Function.Injective (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) := by
  intro a b h
  obtain v := (inferInstance : Nonempty (InfinitePlace X.B.I.F)).some
  apply (X.B.I.φ v).injective
  rw [← thetaV_inclR X.B.I v a, ← thetaV_inclR X.B.I v b, h]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sigA_inclE (x : X.B.I.E) :
    Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.B.I.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hA_incl_left (x : Fin X.B.I.n → X.B.I.E) (y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    hA X.B.I (incl X.B.I x) y =
      ∑ j, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by
  simp only [hA, Formalism.UG.hform, Matrix.map_apply, incl, sigA_inclE, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclE_injective : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) :=
  Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (S := X.B.I.F)
    (MassDataMassesW.inj_Af X.B.I.F)

end Spec

end MassDataMassesW.NRatW
