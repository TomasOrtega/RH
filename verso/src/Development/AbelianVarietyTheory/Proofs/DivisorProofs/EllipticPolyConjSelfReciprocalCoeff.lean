import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

/- English proof (translation)
Introduce `E _ _ _ n P hP`. Establish `hdeg : P.natDegree = n` using `hP.2.1`. Take `⟨h0, hid⟩` from `ell_conj_selfRecip E n P hP`. Use `⟨h0, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hc` using `congrArg (fun Q : E[X] => Q.coeff k) hid`.

Simplify using `only [coeff_C_mul, coeff_reverse] at hc`. Establish `hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n`. Rewrite using `[natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]`. Rewrite `hc` using `[hnd, revAt_le hk, coeff_map]`. Establish `hc2` using `congrArg (IsCMField.complexConj E) hc`.

Simplify `hc2` using `[map_mul]`.
-/
theorem ell_coeff_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  intro E _ _ _ n P hP
  have hdeg : P.natDegree = n := hP.2.1
  obtain ⟨h0, hid⟩ := ell_conj_selfRecip E n P hP
  refine ⟨h0, fun k hk => ?_⟩
  have hc := congrArg (fun Q : E[X] => Q.coeff k) hid
  simp only [coeff_C_mul, coeff_reverse] at hc
  have hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]
  rw [hnd, revAt_le hk, coeff_map] at hc
  have hc2 := congrArg (IsCMField.complexConj E) hc
  simpa [map_mul] using hc2

end GlobalTheory.ConjSelfRecip
