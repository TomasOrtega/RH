import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCoordinatesBoundedRise
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

noncomputable section
namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem logSize_nonneg_cm {n : ℕ} (g : GA E n) : 0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem redSize_ratGL_mul {n : ℕ} (γ : GL (Fin n) E) (g : GA E n) :
    redSize (ratGL E n γ * g) = redSize g := by
  unfold redSize
  rw [← (Equiv.mulRight γ).iInf_comp (g := fun δ : GL (Fin n) E => logSize (ratGL E n δ * g))]
  refine iInf_congr fun δ => ?_
  simp [map_mul, mul_assoc]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem bddBelow_sizes {n : ℕ} (g : GA E n) :
    BddBelow (Set.range fun γ : GL (Fin n) E => logSize (ratGL E n γ * g)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact logSize_nonneg_cm _⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  le_ciInf fun _ => logSize_nonneg_cm _

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem redSize_le {n : ℕ} (g : GA E n) : redSize g ≤ logSize g := by
  have h := ciInf_le (bddBelow_sizes g) (1 : GL (Fin n) E)
  simp only [map_one, one_mul] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem redSize_zero (g : GA E 0) : redSize g = 0 := by
  have h : ∀ A : Matrix (Fin 0) (Fin 0) (Ad E), logSizeM A = 0 := fun A => by
    simp [logSizeM]
  have h' : ∀ x : GA E 0, logSize x = 0 := fun x => by simp [logSize, h]
  simp [redSize, h']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wt_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : H E n 0),
    (∀ γ : GL (Fin n) E, wt ((ratGL E n γ * x.1, x.2) : H E n 0) = wt x) ∧ 1 ≤ wt x ∧ wt x ≤ 1 + logSize x.1 := by
  intro E _ _ _ n x
  refine ⟨fun γ => ?_, ?_, ?_⟩
  · simp only [wt, redSize_ratGL_mul]
  · have h1 := redSize_nonneg x.1
    have h2 := redSize_nonneg x.2
    simp only [wt]; linarith
  · have h1 := redSize_le x.1
    have h2 := redSize_zero x.2
    simp only [wt]; linarith

end GlobalTheory.CompanionTheory.PiVec
end
