import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementDenominatorClearing
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimitiveElementDenominatorClearing.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.primitive_element_denominator_clearing : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (m d : ℕ) (a : Fin m → C) (t : Fin d → C) (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)) (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)), MvPolynomial.aeval t Δ ≠ 0 → (∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) = MvPolynomial.aeval t Δ * a j) → (∀ R : Polynomial (MvPolynomial (Fin d) k), Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ R = 0 → P ∣ R) → ∀ (B : Type) [Field B] [Algebra k B] (t' : Fin d → B) (θ' : B), MvPolynomial.aeval t' Δ ≠ 0 → Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 → ∃ f : Algebra.adjoin k (Set.range a) →ₐ[k] B, ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) = MvPolynomial.aeval t' Δ * f ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ := by
  first | exact @GlobalTheory.specialisation_lift | exact GlobalTheory.specialisation_lift | (intros; apply GlobalTheory.specialisation_lift <;> assumption)
