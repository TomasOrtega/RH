import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Complex Filter Topology

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6.Chi8

open Formalism.ZF.ComplexPowerDifferenceIntegral

def chi : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

def g (s : ℂ) (n : ℕ) : ℂ :=
  ((8 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 3 : ℝ) : ℂ) ^ (-s)
    - (((8 * (n : ℝ) + 5 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 7 : ℝ) : ℂ) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, g s n

/- English proof (authored)
The complex character is obtained by embedding the values of the integer character modulo 8 into the complex numbers. Evaluating this construction at x gives the formula.
-/
lemma chi_apply (x : ZMod 8) : chi x = ((ZMod.χ₈ x : ℤ) : ℂ) := rfl

/- English proof (authored)
Reducing 8m + r modulo 8 gives the same residue as reducing r. The character therefore has the same value at both.
-/
lemma chi_cast (m r : ℕ) : chi ((m * 8 + r : ℕ) : ZMod 8) = chi ((r : ℕ) : ZMod 8) := by
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := ZMod.natCast_self 8
  rw [Nat.cast_add, Nat.cast_mul, h8, mul_zero, zero_add]

/- English proof (authored)
The residue 0 is even, so the character modulo 8 takes the value zero there.
-/
lemma chi0 : chi ((0 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 by decide]; simp
/- English proof (authored)
The residue 1 is congruent to 1 modulo 8, so the character takes the value one.
-/
lemma chi1 : chi ((1 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 by decide]; simp
/- English proof (authored)
The residue 2 is even, so the character modulo 8 takes the value zero there.
-/
lemma chi2 : chi ((2 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 by decide]; simp
/- English proof (authored)
The residue 3 belongs to the pair of residues ±3 modulo 8, on which the character takes the value minus one.
-/
lemma chi3 : chi ((3 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 by decide]; simp
/- English proof (authored)
The residue 4 is even, so the character modulo 8 takes the value zero there.
-/
lemma chi4 : chi ((4 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 by decide]; simp
/- English proof (authored)
The residue 5 is congruent to −3 modulo 8, so the character takes the value minus one.
-/
lemma chi5 : chi ((5 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 by decide]; simp
/- English proof (authored)
The residue 6 is even, so the character modulo 8 takes the value zero there.
-/
lemma chi6 : chi ((6 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 by decide]; simp
/- English proof (authored)
The residue 7 is congruent to −1 modulo 8, so the character takes the value one.
-/
lemma chi7 : chi ((7 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 by decide]; simp

def tm (s : ℂ) (n : ℕ) : ℂ := LSeries.term (fun n : ℕ => chi (n : ZMod 8)) s n

/- English proof (authored)
The term at index zero is defined to be zero. At a positive index 8m + r, the numerator is the character value at r by periodicity. This value vanishes by hypothesis, so the term is zero in that case as well.
-/
lemma tm_zero (s : ℂ) (m r : ℕ) (h : chi ((r : ℕ) : ZMod 8) = 0) : tm s (m * 8 + r) = 0 := by
  unfold tm
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [chi_cast, h, zero_div]

/- English proof (authored)
Since r is positive, the index 8m + r is positive. Use the defining quotient for the Dirichlet series term and reduce its numerator modulo 8. Dividing by the positive base raised to s is multiplication by the same base raised to −s.
-/
lemma tm_eval (s : ℂ) (m r : ℕ) (hr : 0 < r) :
    tm s (m * 8 + r) = chi ((r : ℕ) : ZMod 8) * ((8 * (m : ℝ) + (r : ℝ) : ℝ) : ℂ) ^ (-s) := by
  unfold tm
  rw [LSeries.term_of_ne_zero (by omega), chi_cast, Complex.cpow_neg, div_eq_mul_inv]
  congr 3
  push_cast
  ring

/- English proof (authored)
Expand the sum over the eight residues. The four even residues contribute zero. The remaining terms are the powers at 8m + 1 and 8m + 7 with positive signs and at 8m + 3 and 8m + 5 with negative signs. This is the defining expression of the block.
-/
lemma block (s : ℂ) (m : ℕ) : ∑ r : Fin 8, tm s (m * 8 + (r : ℕ)) = g s m := by
  rw [Fin.sum_univ_eight]
  change tm s (m * 8 + 0) + tm s (m * 8 + 1) + tm s (m * 8 + 2) + tm s (m * 8 + 3) + tm s (m * 8 + 4)
    + tm s (m * 8 + 5) + tm s (m * 8 + 6) + tm s (m * 8 + 7) = g s m
  rw [tm_zero s m 0 chi0, tm_zero s m 2 chi2, tm_zero s m 4 chi4, tm_zero s m 6 chi6,
    tm_eval s m 1 (by norm_num), tm_eval s m 3 (by norm_num), tm_eval s m 5 (by norm_num),
    tm_eval s m 7 (by norm_num), chi1, chi3, chi5, chi7]
  unfold g
  simp only [Nat.cast_ofNat, Nat.cast_one]
  ring

def gr (σ : ℝ) (n : ℕ) : ℝ :=
  (8 * (n : ℝ) + 1) ^ (-σ) - (8 * (n : ℝ) + 3) ^ (-σ) - ((8 * (n : ℝ) + 5) ^ (-σ) - (8 * (n : ℝ) + 7) ^ (-σ))

end Formalism.LFunctionChainParameters.LChain6.Chi8

namespace Formalism.LFunctionChainParameters.LChain6

end Formalism.LFunctionChainParameters.LChain6
