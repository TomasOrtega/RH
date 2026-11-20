import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.LocUnr

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r` using `P.valuation_of_algebraMap r`. Rewrite using `[e]`. Establish `hr : r ≠ 0` using `by rintro rfl; exact h2 (Submodule.zero_mem _)`. Establish `a1` using `(P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)`. Establish `a2` using `mt (P.intValuation_le_pow_iff_mem r 2).1 h2`.

Rewrite `a1`, `a2`, the goal using `[← WithZero.exp_log (P.intValuation_ne_zero r hr)]`. Rewrite `a1`, `a2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Move the coercions through the operations in `at a1 a2`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_eq_exp_neg_one (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (h1 : r ∈ P.asIdeal)
    (h2 : r ∉ P.asIdeal ^ 2) : P.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp (-1 : ℤ) := by
  have e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r := P.valuation_of_algebraMap r
  rw [e]
  have hr : r ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have a1 := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)
  have a2 := mt (P.intValuation_le_pow_iff_mem r 2).1 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero r hr)] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  push_cast at a1 a2
  omega

noncomputable def redInt (P : HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* IsLocalRing.ResidueField (P.valuation K).valuationSubring :=
  (IsLocalRing.residue _).comp
    ((algebraMap (𝓞 K) K).codRestrict (P.valuation K).valuationSubring (fun r => P.valuation_le_one r))

end GlobalTheory.LvT.LocUnr
