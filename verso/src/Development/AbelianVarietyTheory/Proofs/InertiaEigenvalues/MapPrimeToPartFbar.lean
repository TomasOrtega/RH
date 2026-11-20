import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapEqProdOfValuationSubring

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Simplify using `[ZMod.val_one_eq_one_mod]`. Use `set q := l ^ n.factorization l with hq_def`.

Use `set m := n / q with hm_def`. Establish `hnqm : q * m = n` using `Nat.ordProj_mul_ordCompl_eq_self n l`. Establish `hm0 : m ≠ 0`. Introduce and unpack `h`. Rewrite `hnqm` using `[h, mul_zero]`.

Use linear arithmetic over natural numbers and integers. Use `haveI : NeZero m := ⟨hm0⟩`. Establish `hcop : Nat.Coprime q m` using `(Nat.coprime_ordCompl hl hpos.ne').pow_left _`. Establish `hym : y ^ m = 1`. Establish `h1 : (y ^ m) ^ q = 1` using `by rw [← pow_mul, mul_comm, hnqm, hy]`.

Establish `h2 : (y ^ m - 1) ^ q = 0`. Rewrite using `[hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]`. Establish `hq0 : q ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Conclude with `sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)`. Establish `hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m]`.

Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val]`. Conclude with `ZMod.coe_mul_inv_eq_one q hcop`. Establish `hdvd : orderOf y ∣ m` using `orderOf_dvd_of_pow_eq_one hym`.

Establish `hmod'` using `hmod.of_dvd hdvd`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.primeToPart`. Rewrite using `[map_pow]`. Conclude with `pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])`.
-/
theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
