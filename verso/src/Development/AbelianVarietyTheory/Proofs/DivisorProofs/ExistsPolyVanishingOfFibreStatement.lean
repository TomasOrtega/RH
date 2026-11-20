import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPolyVanishingOfFibre.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_poly_vanishing_of_fiber : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  first | exact @GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | exact GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | (intros; apply GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre <;> assumption)
