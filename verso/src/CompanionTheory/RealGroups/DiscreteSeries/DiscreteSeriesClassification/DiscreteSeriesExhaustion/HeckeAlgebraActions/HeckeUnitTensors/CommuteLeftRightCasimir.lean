import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.CompLeftSmulOne

noncomputable section

set_option linter.unusedVariables false

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_of_eig {T : Module.End ℂ (Fin (m + 1) → X.V)} {μ : ℂ} {f : Fin (m + 1) → X.V} (h : T f = μ • f) :
    f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Pr_mem (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) : Pr X χ s f ∈ stepSub X (χ s) :=
  mem_of_eig (om_Pr hS f)

variable (X) in

def y1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => (om X).comp (LinearMap.proj c)

variable (X) in

def y2 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  LinearMap.pi fun a => -∑ c, (tensE X a c).comp (LinearMap.proj c)

variable (X) in

def eta : X.V →ₗ[ℂ] (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => LinearMap.single ℂ (fun _ => X.V) c

variable (X) in

def psi : (Fin (m + 1) → Fin (m + 1) → X.V) →ₗ[ℂ] X.V where
  toFun H := ∑ c, H c c
  map_add' H K := by simp [Finset.sum_add_distrib]
  map_smul' r H := by simp [Finset.smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem left_casimir_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) (c : Fin (m + 1)) : y1 X H c = om X (H c) := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem right_casimir_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    y2 X H a = -∑ c, tensE X a c (H c) := by
  simp [y2, LinearMap.pi_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eta_apply (v : X.V) (c : Fin (m + 1)) : eta X v c = Pi.single c v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psi_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) : psi X H = ∑ c, H c c := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem commute_left_right_casimir : Commute (y1 X) (y2 X) := by
  refine LinearMap.ext fun H => funext fun a => ?_
  simp only [Module.End.mul_apply, left_casimir_apply, right_casimir_apply, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (LinearMap.congr_fun (commute_om X a c).eq (H c)).symm

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_tensE_single (v : X.V) (a : Fin (m + 1)) :
    ∑ c, tensE X a c (Pi.single c v) = om X (Pi.single a v) + ((m + 1 : ℕ) : ℂ) • (Pi.single a v : Fin (m + 1) → X.V) := by
  funext d
  simp only [Finset.sum_apply, tensE_apply, om_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single d]
    · rw [Pi.single_eq_same, Finset.sum_eq_single a]
      · rw [Pi.single_eq_same]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
      · intro h; exact absurd (mem_univ a) h
    · intro c _ hc; rw [Pi.single_eq_of_ne (Ne.symm hc), map_zero]
    · intro h; exact absurd (mem_univ d) h
  · by_cases h : d = a
    · subst h
      simp only [Pi.single_eq_same, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
    · simp [h]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem right_casimir_eta (v : X.V) : y2 X (eta X v) = -(y1 X (eta X v) + ((m + 1 : ℕ) : ℂ) • eta X v) := by
  funext a
  rw [right_casimir_apply]
  simp only [eta_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, left_casimir_apply]
  rw [sum_tensE_single]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem right_casimir_add_eta_psi (H : Fin (m + 1) → Fin (m + 1) → X.V) (a d : Fin (m + 1)) :
    (y2 X H + eta X (psi X H)) a d = -∑ c, X.E a c (H c d) := by
  rw [Pi.add_apply, right_casimir_apply, eta_apply, psi_apply]
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, tensE_apply]
  rw [Finset.sum_add_distrib]
  by_cases h : d = a
  · subst h; simp [Pi.single_eq_same]
  · simp [h, Pi.single_eq_of_ne h]

def liftL (T : Module.End ℂ (Fin (m + 1) → X.V)) : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun H := fun a d => T (fun c => H c d) a
  map_add' H K := by
    funext a d
    show T (fun c => H c d + K c d) a = T (fun c => H c d) a + T (fun c => K c d) a
    rw [show (fun c => H c d + K c d) = (fun c => H c d) + (fun c => K c d) from rfl, map_add]; rfl
  map_smul' r H := by
    funext a d
    show T (fun c => r • H c d) a = r • T (fun c => H c d) a
    rw [show (fun c => r • H c d) = r • (fun c => H c d) from rfl, map_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftL_apply (T : Module.End ℂ (Fin (m + 1) → X.V)) (H) (a d : Fin (m + 1)) :
    liftL T H a d = T (fun c => H c d) a := rfl

def liftR : Module.End ℂ (Fin (m + 1) → X.V) →+* Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun := liftL
  map_one' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_mul' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_zero' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_add' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem liftR_smul_one (μ : ℂ) : liftR (X := X) (μ • 1) = μ • 1 :=
  LinearMap.ext fun H => funext fun a => funext fun d => rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem omegaP_eq : liftR (X := X) (omD X) = y2 X + (eta X).comp (psi X) := by
  refine LinearMap.ext fun H => funext fun a => funext fun d => ?_
  show liftL (omD X) H a d = (y2 X H + eta X (psi X H)) a d
  rw [right_casimir_add_eta_psi, liftL_apply]
  simp [omD, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply]

end CompanionTheory.RgExh.Hk.UnitPf
