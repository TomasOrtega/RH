import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialMemRangeGlue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt.GlueProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {a b : ℕ}

open Classical in

def rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ)

def ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : LPol b a →ₗ[ℂ] PolF D b a :=
  LinearMap.mulRight ℂ (rest τ P) ∘ₗ (MvPolynomial.rename (fun s => (τ, s))).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ins_apply (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    ins τ P p = MvPolynomial.rename (fun s => (τ, s)) p * rest τ P := rfl

open Classical in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem glue_update (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    glue (Function.update P τ p) = ins τ P p := by
  rw [ins_apply, glue, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), rest]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem glue_eq (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : glue P = ins τ P (P τ) := by
  classical
  rw [← glue_update, Function.update_eq_self]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pderiv_other {τ ρ : D.what₂.Tau} (h : ρ ≠ τ) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (MvPolynomial.rename (fun s => (ρ, s)) p : PolF D b a) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    rw [map_mul, Derivation.leibniz, hp, MvPolynomial.rename_X, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e
      exact h (congrArg Prod.fst e)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem pderiv_rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) :
    MvPolynomial.pderiv (τ, s) (rest τ P) = 0 := by
  classical
  unfold rest
  refine Finset.prod_induction _ (fun q : PolF D b a => MvPolynomial.pderiv (τ, s) q = 0) ?_ ?_ ?_
  · intro x y hx hy
    rw [Derivation.leibniz, hx, hy]; simp
  · simp
  · intro ρ hρ
    exact pderiv_other (Finset.ne_of_mem_erase hρ) s _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pderiv_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (ins τ P p) = ins τ P (MvPolynomial.pderiv s p) := by
  classical
  have hinj : Function.Injective (fun s : Fin b × Fin a => (τ, s)) := fun x y e => congrArg Prod.snd e
  have := MvPolynomial.pderiv_rename hinj s p
  rw [ins_apply, ins_apply, Derivation.leibniz, pderiv_rest, ← this]
  simp [mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mul_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.X (τ, s) * ins τ P p = ins τ P (MvPolynomial.X s * p) := by
  rw [ins_apply, ins_apply, map_mul, MvPolynomial.rename_X, mul_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem rai_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : raiO τ ε ε' i j (ins τ P p) = ins τ P (rai ε ε' i j p) := by
  unfold raiO rai
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, map_neg, Derivation.coeFn_coe]
    rw [← pderiv_ins]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem low_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : lowO τ ε ε' i j (ins τ P p) = ins τ P (low ε ε' i j p) := by
  unfold lowO low
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe]
    rw [← pderiv_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem fockS_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (X : Matrix (Fin a) (Fin a) ℂ) (p : LPol b a) :
    fockS τ ε ε' X (ins τ P p) = ins τ P (locS ε ε' X p) := by
  unfold fockS locS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add,
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem fockT_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin b) (Fin b) ℂ) (p : LPol b a) :
    fockT τ ε ε' Y (ins τ P p) = ins τ P (locT ε ε' Y p) := by
  unfold fockT locT
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add,
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem glue_span :
    Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | (apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue ..)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem glueLaw : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  intro D a b
  refine ⟨glue_span, fun τ ε ε' P => ⟨fun X => ?_, fun Y => ?_⟩⟩
  · rw [glue_update, glue_eq τ P, fockS_ins]
  · rw [glue_update, glue_eq τ P, fockT_ins]

end GlobalTheory.Chain.RealIt.GlueProof

end
