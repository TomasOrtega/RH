import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZpowMemOfValOne

noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem hasDiv_mul_mul {O : Subring L} {d : List ℤ} {g : GL (Fin n) L} (h : HasDiv O d g) {a b : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) O) (hb : b ∈ GLint (Fin n) O) : HasDiv O d (a * g * b) := by
  obtain ⟨ϖ, hϖ, a', ha', b', hb', e⟩ := h
  refine ⟨ϖ, hϖ, a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  simp only [Units.val_mul, e, Matrix.mul_assoc]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem HasDiv.exists_eq_mul_mul {O : Subring L} (hO : ∀ x : L, Valued.v x ≤ 1 → x ∈ O) {d : List ℤ}
    {g s : GL (Fin n) L} (hg : HasDiv O d g) (hs : HasDiv O d s) :
    ∃ a b : GLint (Fin n) O, g = a * s * b := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetDivisors.main
  | exact _root_.GlobalTheory.DoubleCosetDivisors.main
  | (apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetDivisors.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetDivisors.main ..)

end Local

end GlobalTheory.SphGal

end
