import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupEqTopOfLeMaximal
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.PrimesOverL

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above`. Consider the case `exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above`. Consider the case `(apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)`.
-/
theorem primes_over_l : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  first
  | exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | (apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)

end GlobalTheory.PrimesOverL
