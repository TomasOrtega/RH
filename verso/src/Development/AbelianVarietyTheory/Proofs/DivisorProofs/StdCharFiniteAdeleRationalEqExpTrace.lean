import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PsiFinRat

/- English proof (translation)
Take `⟨hchar, ⟨θ, hθ⟩, hall⟩` from `hψ`. Establish `hinf` using `hall θ hθ`. Establish `hsplit : pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q) = algebraMap D.host.F (AF D.host.F) q + pairA D.host.F (-(algebraMap D.host.F (Ainf D.host.F) q)) 0`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : Ainf D.host.F) = algebraMap D.host.F (Ainf D.host.F) q + -(algebraMap D.host.F (Ainf D.host.F) q)`.

Rewrite using `[add_neg_cancel]`. Use `show algebraMap D.host.F (Af D.host.F) q = algebraMap D.host.F (Af D.host.F) q + 0`. Rewrite using `[add_zero]`. Rewrite using `[hsplit, AddChar.map_add_eq_mul, hchar.2.2.1, one_mul]`. Establish `h1` using `hinf (-(algebraMap D.host.F (Ainf D.host.F) q))`.

Simplify using `only [psiInf] at h1`. Rewrite using `[h1]`. Establish `htm : ∀ τ, θ τ ((-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E)) = -tauE D τ (q : D.host.E)`. Introduce `τ`. Establish `e : (-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E) = -((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q))`.

Establish `e0 : (algebraMap D.host.F (Ainf D.host.F) q) ⊗ₜ[D.host.F] (1 : D.host.E) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q)` using `(Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes q |>.trans ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes q).symm`. Rewrite using `[TensorProduct.neg_tmul, e0]`. Rewrite using `[e, map_neg, (hθ τ).1]`. Both sides reduce to the same expression. Simplify using `only [htm, Finset.sum_neg_distrib]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_pairA_zero_algebraMap {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  obtain ⟨hchar, ⟨θ, hθ⟩, hall⟩ := hψ
  have hinf := hall θ hθ
  have hsplit : pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q) =
      algebraMap D.host.F (AF D.host.F) q +
        pairA D.host.F (-(algebraMap D.host.F (Ainf D.host.F) q)) 0 := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = algebraMap D.host.F (Ainf D.host.F) q + -(algebraMap D.host.F (Ainf D.host.F) q)
      rw [add_neg_cancel]
    · show algebraMap D.host.F (Af D.host.F) q = algebraMap D.host.F (Af D.host.F) q + 0
      rw [add_zero]
  rw [hsplit, AddChar.map_add_eq_mul, hchar.2.2.1, one_mul]
  have h1 := hinf (-(algebraMap D.host.F (Ainf D.host.F) q))
  simp only [psiInf] at h1
  rw [h1]
  have htm : ∀ τ, θ τ ((-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -tauE D τ (q : D.host.E) := by
    intro τ
    have e : (-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        -((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q)) := by
      have e0 : (algebraMap D.host.F (Ainf D.host.F) q) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q) :=
        (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes q |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F)
            (B := D.host.E)).commutes q).symm
      rw [TensorProduct.neg_tmul, e0]
    rw [e, map_neg, (hθ τ).1]
    rfl
  simp only [htm, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

end GlobalTheory.PsiFinRat
