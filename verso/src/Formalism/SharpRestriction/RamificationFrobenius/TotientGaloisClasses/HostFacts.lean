import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

/- English proof (translation)
Establish `hpo : Odd p` using `Nat.odd_iff.2 hp`. Establish `hro : Odd r` using `Nat.odd_iff.2 (by omega)`. Rewrite using `[jacobiSym.neg _ hpo]`. Break down `(by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h` into its components or cases. Rewrite using `[ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hro h]`.

Rewrite using `[ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hr h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobi_neg_recip {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) :
    jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by
  have hpo : Odd p := Nat.odd_iff.2 hp
  have hro : Odd r := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hpo]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hro h]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hr h]
    ring

/- English proof (translation)
Establish `h : ((x % p : ℕ) : ℤ) = ((y % p : ℕ) : ℤ)` using `congrArg _ hxy`. Move the coercions through the operations in `at h`. Conclude with `jacobiSym.mod_left' h`.
-/
theorem jacobi_congr {x y p : ℕ} (hxy : x ≡ y [MOD p]) : jacobiSym (x : ℤ) p = jacobiSym (y : ℤ) p := by
  have h : ((x % p : ℕ) : ℤ) = ((y % p : ℕ) : ℤ) := congrArg _ hxy
  push_cast at h
  exact jacobiSym.mod_left' h

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
The claim follows from `H.hyp.1`.
-/
theorem q_prime : H.q.Prime := H.hyp.1
/- English proof (translation)
The claim follows from `H.hyp.2.1`.
-/
theorem d_prime : H.d.Prime := H.hyp.2.1
/- English proof (translation)
The claim follows from `H.hyp.2.2.1`.
-/
theorem q_mod_eight : H.q % 8 = 3 := H.hyp.2.2.1
/- English proof (translation)
The claim follows from `H.hyp.2.2.2.1`.
-/
theorem d_mod_sixteen : H.d % 16 = 7 := H.hyp.2.2.2.1
/- English proof (translation)
Use `H.q_mod_eight` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem q_mod_four : H.q % 4 = 3 := by
  have := H.q_mod_eight
  omega
/- English proof (translation)
Use `H.d_mod_sixteen` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem d_mod_four : H.d % 4 = 3 := by
  have := H.d_mod_sixteen
  omega
/- English proof (translation)
Use `H.d_mod_sixteen` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem d_mod_eight : H.d % 8 = 7 := by
  have := H.d_mod_sixteen
  omega
/- English proof (translation)
Introduce `h`. Establish `h1` using `H.q_mod_eight`. Establish `h2` using `H.d_mod_sixteen`. Rewrite `h1` using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem q_ne_d : H.q ≠ H.d := by
  intro h
  have h1 := H.q_mod_eight
  have h2 := H.d_mod_sixteen
  rw [h] at h1
  omega
/- English proof (translation)
Introduce `h`. Establish `h1` using `H.q_mod_eight`. Rewrite `h1` using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem q_ne_two : H.q ≠ 2 := by
  intro h
  have h1 := H.q_mod_eight
  rw [h] at h1
  omega
/- English proof (translation)
Introduce `h`. Establish `h1` using `H.d_mod_sixteen`. Rewrite `h1` using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem d_ne_two : H.d ≠ 2 := by
  intro h
  have h1 := H.d_mod_sixteen
  rw [h] at h1
  omega
/- English proof (translation)
The claim follows from `(Nat.coprime_primes H.q_prime H.d_prime).2 H.q_ne_d`.
-/
theorem coprime_q_d : Nat.Coprime H.q H.d :=
  (Nat.coprime_primes H.q_prime H.d_prime).2 H.q_ne_d
/- English proof (translation)
The claim follows from `Nat.Coprime.coprime_dvd_right (dvd_mul_right H.q H.d) H.QS_coprime`.
-/
theorem coprime_QS_q : Nat.Coprime H.QS H.q :=
  Nat.Coprime.coprime_dvd_right (dvd_mul_right H.q H.d) H.QS_coprime
/- English proof (translation)
The claim follows from `Nat.Coprime.coprime_dvd_right (dvd_mul_left H.d H.q) H.QS_coprime`.
-/
theorem coprime_QS_d : Nat.Coprime H.QS H.d :=
  Nat.Coprime.coprime_dvd_right (dvd_mul_left H.d H.q) H.QS_coprime
/- English proof (translation)
The claim follows from `Nat.Coprime.mul H.coprime_QS_d H.coprime_q_d`.
-/
theorem coprime_QSq_d : Nat.Coprime (H.QS * H.q) H.d :=
  Nat.Coprime.mul H.coprime_QS_d H.coprime_q_d
/- English proof (translation)
The claim follows from `Nat.Coprime.mul H.coprime_QS_q H.coprime_q_d.symm`.
-/
theorem coprime_QSd_q : Nat.Coprime (H.QS * H.d) H.q :=
  Nat.Coprime.mul H.coprime_QS_q H.coprime_q_d.symm
/- English proof (translation)
The claim follows from `H.QS_pos.ne'`.
-/
theorem QS_ne_zero : H.QS ≠ 0 := H.QS_pos.ne'
/- English proof (translation)
The claim follows from `Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.d_prime.ne_zero`.
-/
theorem condN_ne_zero : H.condN ≠ 0 :=
  Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.d_prime.ne_zero

instance neZero_condN : NeZero H.condN := ⟨H.condN_ne_zero⟩

/- English proof (translation)
The claim follows from `dvd_mul_of_dvd_left (dvd_mul_right _ _) _`.
-/
theorem QS_dvd_condN : H.QS ∣ H.condN := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
/- English proof (translation)
The claim follows from `dvd_mul_of_dvd_left (dvd_mul_left _ _) _`.
-/
theorem q_dvd_condN : H.q ∣ H.condN := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
/- English proof (translation)
The claim follows from `dvd_mul_left _ _`.
-/
theorem d_dvd_condN : H.d ∣ H.condN := dvd_mul_left _ _
/- English proof (translation)
The claim follows from `H.tower_dvd.trans H.QS_dvd_condN`.
-/
theorem tower_dvd_condN : 2 ^ (φ.e + 2) ∣ H.condN := H.tower_dvd.trans H.QS_dvd_condN
/- English proof (translation)
The claim follows from `(dvd_pow_self 2 (by omega)).trans H.tower_dvd`.
-/
theorem two_dvd_QS : 2 ∣ H.QS := (dvd_pow_self 2 (by omega)).trans H.tower_dvd
/- English proof (translation)
The claim follows from `(show 2 ^ 4 ∣ 2 ^ (φ.e + 2) from Nat.pow_dvd_pow 2 (by have := H.two_le_e; omega)).trans H.tower_dvd`.
-/
theorem sixteen_dvd_QS : 16 ∣ H.QS :=
  (show 2 ^ 4 ∣ 2 ^ (φ.e + 2) from Nat.pow_dvd_pow 2 (by have := H.two_le_e; omega)).trans H.tower_dvd
/- English proof (translation)
The claim follows from `H.two_dvd_QS.trans H.QS_dvd_condN`.
-/
theorem two_dvd_condN : 2 ∣ H.condN := H.two_dvd_QS.trans H.QS_dvd_condN
/- English proof (translation)
The claim follows from `H.sixteen_dvd_QS.trans H.QS_dvd_condN`.
-/
theorem sixteen_dvd_condN : 16 ∣ H.condN := H.sixteen_dvd_QS.trans H.QS_dvd_condN
/- English proof (translation)
The claim follows from `Nat.le_of_dvd H.QS_pos H.tower_dvd`.
-/
theorem tower_le_QS : 2 ^ (φ.e + 2) ≤ H.QS := Nat.le_of_dvd H.QS_pos H.tower_dvd

/- English proof (translation)
The claim follows from `(Nat.Prime.coprime_iff_not_dvd H.q_prime).1 H.coprime_QS_q.symm`.
-/
theorem q_not_dvd_QS : ¬ H.q ∣ H.QS := (Nat.Prime.coprime_iff_not_dvd H.q_prime).1 H.coprime_QS_q.symm
/- English proof (translation)
The claim follows from `(Nat.Prime.coprime_iff_not_dvd H.d_prime).1 H.coprime_QS_d.symm`.
-/
theorem d_not_dvd_QS : ¬ H.d ∣ H.QS := (Nat.Prime.coprime_iff_not_dvd H.d_prime).1 H.coprime_QS_d.symm
/- English proof (translation)
The claim follows from `(Nat.Prime.coprime_iff_not_dvd H.d_prime).1 H.coprime_QSq_d.symm`.
-/
theorem d_not_dvd_QSq : ¬ H.d ∣ H.QS * H.q :=
  (Nat.Prime.coprime_iff_not_dvd H.d_prime).1 H.coprime_QSq_d.symm

/- English proof (translation)
Unfold `HostRaw.small`. Rewrite using `[Nat.mem_primeFactors]`. Conclude with `⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, H.QS_ne_zero⟩⟩`.
-/
theorem mem_small_iff {p : ℕ} : p ∈ H.small ↔ p.Prime ∧ p ∣ H.QS := by
  unfold HostRaw.small
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, H.QS_ne_zero⟩⟩

/- English proof (translation)
The claim follows from `H.mem_small_iff.2 ⟨Nat.prime_two, H.two_dvd_QS⟩`.
-/
theorem two_mem_small : 2 ∈ H.small := H.mem_small_iff.2 ⟨Nat.prime_two, H.two_dvd_QS⟩
/- English proof (translation)
Introduce `h` and use `H.q_not_dvd_QS (H.mem_small_iff.1 h).2`.
-/
theorem q_notMem_small : H.q ∉ H.small := fun h => H.q_not_dvd_QS (H.mem_small_iff.1 h).2
/- English proof (translation)
Introduce `h` and use `H.d_not_dvd_QS (H.mem_small_iff.1 h).2`.
-/
theorem d_notMem_small : H.d ∉ H.small := fun h => H.d_not_dvd_QS (H.mem_small_iff.1 h).2

/- English proof (translation)
Rewrite using `[hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp H.q_prime]`.
-/
theorem dvd_QSq_iff {p : ℕ} (hp : p.Prime) : p ∣ H.QS * H.q ↔ p ∣ H.QS ∨ p = H.q := by
  rw [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp H.q_prime]

/- English proof (translation)
Use `show p ∣ H.QS * H.q * H.d ↔ _`. Rewrite using `[hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp H.q_prime, Nat.prime_dvd_prime_iff_eq hp H.d_prime, or_assoc]`.
-/
theorem dvd_condN_iff {p : ℕ} (hp : p.Prime) : p ∣ H.condN ↔ p ∣ H.QS ∨ p = H.q ∨ p = H.d := by
  show p ∣ H.QS * H.q * H.d ↔ _
  rw [hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp H.q_prime,
    Nat.prime_dvd_prime_iff_eq hp H.d_prime, or_assoc]

/- English proof (translation)
Rewrite using `[H.dvd_condN_iff hp, H.mem_small_iff, and_iff_right hp]`.
-/
theorem dvd_condN_iff_small {p : ℕ} (hp : p.Prime) : p ∣ H.condN ↔ p ∈ H.small ∨ p = H.q ∨ p = H.d := by
  rw [H.dvd_condN_iff hp, H.mem_small_iff, and_iff_right hp]

/- English proof (translation)
Rewrite using `[H.dvd_condN_iff hp]`. Simplify using `only [not_or, ne_eq]`.
-/
theorem not_dvd_condN_iff {p : ℕ} (hp : p.Prime) : ¬ p ∣ H.condN ↔ ¬ p ∣ H.QS ∧ p ≠ H.q ∧ p ≠ H.d := by
  rw [H.dvd_condN_iff hp]
  simp only [not_or, ne_eq]

variable {H} in
/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h H.two_dvd_condN`.
-/
theorem ne_two_of_not_dvd {p : ℕ} (h : ¬ p ∣ H.condN) : p ≠ 2 := by
  rintro rfl
  exact h H.two_dvd_condN

variable {H} in
/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h H.q_dvd_condN`.
-/
theorem ne_q_of_not_dvd {p : ℕ} (h : ¬ p ∣ H.condN) : p ≠ H.q := by
  rintro rfl
  exact h H.q_dvd_condN

variable {H} in
/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h H.d_dvd_condN`.
-/
theorem ne_d_of_not_dvd {p : ℕ} (h : ¬ p ∣ H.condN) : p ≠ H.d := by
  rintro rfl
  exact h H.d_dvd_condN

variable {H} in
/- English proof (translation)
Introduce `hs` and use `h ((H.mem_small_iff.1 hs).2.trans H.QS_dvd_condN)`.
-/
theorem notMem_small_of_not_dvd {p : ℕ} (h : ¬ p ∣ H.condN) : p ∉ H.small :=
  fun hs => h ((H.mem_small_iff.1 hs).2.trans H.QS_dvd_condN)

/- English proof (translation)
Rewrite using `[H.not_dvd_condN_iff hp]`. Use `⟨fun hd => ?_, fun hq => ?_, fun hd => ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[H.QS_split p hp h2 hd]`. Evaluate the numerical expressions using `at hj`. Substitute `hq` using the available equality.

Rewrite `hj` using `[H.hyp.2.2.2.2]`. Evaluate the numerical expressions using `at hj`. Substitute `hd` using the available equality. Rewrite `hj` using `[jacobiSym.mod_left, show (-(H.d : ℤ)) % (H.d : ℤ) = 0 by simp, jacobiSym.zero_left H.d_prime.one_lt]`. Evaluate the numerical expressions using `at hj`.
-/
theorem not_dvd_condN_of_inert {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hj : jacobiSym (-(H.d : ℤ)) p = -1) :
    ¬ p ∣ H.condN := by
  rw [H.not_dvd_condN_iff hp]
  refine ⟨fun hd => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [H.QS_split p hp h2 hd] at hj
    norm_num at hj
  · subst hq
    rw [H.hyp.2.2.2.2] at hj
    norm_num at hj
  · subst hd
    rw [jacobiSym.mod_left, show (-(H.d : ℤ)) % (H.d : ℤ) = 0 by simp,
      jacobiSym.zero_left H.d_prime.one_lt] at hj
    norm_num at hj

variable {H} in
/- English proof (translation)
The claim follows from `(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 ((show Nat.Coprime H.QS 15 from h).coprime_dvd_right (by norm_num : 3 ∣ 15)).symm`.
-/
theorem CoprimeFifteen.three_not_dvd_QS (h : H.CoprimeFifteen) : ¬ 3 ∣ H.QS :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    ((show Nat.Coprime H.QS 15 from h).coprime_dvd_right (by norm_num : 3 ∣ 15)).symm

variable {H} in
/- English proof (translation)
The claim follows from `(Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 ((show Nat.Coprime H.QS 15 from h).coprime_dvd_right (by norm_num : 5 ∣ 15)).symm`.
-/
theorem CoprimeFifteen.five_not_dvd_QS (h : H.CoprimeFifteen) : ¬ 5 ∣ H.QS :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1
    ((show Nat.Coprime H.QS 15 from h).coprime_dvd_right (by norm_num : 5 ∣ 15)).symm

variable {H} in
/- English proof (translation)
Conclude with `(H.not_dvd_condN_iff Nat.prime_five).2 ⟨h.five_not_dvd_QS, fun e => by have := H.q_mod_eight; omega, fun e => by have := H.d_mod_sixteen; omega⟩`.
-/
theorem CoprimeFifteen.five_not_dvd_condN (h : H.CoprimeFifteen) : ¬ 5 ∣ H.condN := by
  exact (H.not_dvd_condN_iff Nat.prime_five).2 ⟨h.five_not_dvd_QS,
    fun e => by have := H.q_mod_eight; omega, fun e => by have := H.d_mod_sixteen; omega⟩

variable {H} in
/- English proof (translation)
Conclude with `(H.not_dvd_condN_iff Nat.prime_three).2 ⟨h.three_not_dvd_QS, fun e => hq e.symm, fun e => by have := H.d_mod_sixteen; omega⟩`.
-/
theorem CoprimeFifteen.three_not_dvd_condN (h : H.CoprimeFifteen) (hq : H.q ≠ 3) : ¬ 3 ∣ H.condN := by
  exact (H.not_dvd_condN_iff Nat.prime_three).2 ⟨h.three_not_dvd_QS,
    fun e => hq e.symm, fun e => by have := H.d_mod_sixteen; omega⟩

/- English proof (translation)
Unfold `HostRaw.psAt`. Rewrite using `[dif_pos h]`.
-/
theorem psAt_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) :
    H.psAt p = (((H.art (ZMod.unitOfCoprime p h)).1.1 : ℤˣ) : ℤ) := by
  unfold HostRaw.psAt
  rw [dif_pos h]

/- English proof (translation)
Unfold `HostRaw.psAt`. Rewrite using `[dif_neg h]`.
-/
theorem psAt_of_not_coprime {p : ℕ} (h : ¬ Nat.Coprime p H.condN) : H.psAt p = 0 := by
  unfold HostRaw.psAt
  rw [dif_neg h]

/- English proof (translation)
Rewrite using `[H.psAt_of_coprime h]`. Apply the tactic sequence `rcases Int.units_eq_one_or (H.art (ZMod.unitOfCoprime p h)).1.1 with h1 | h1 <;> simp [h1]`.
-/
theorem psAt_eq_one_or {p : ℕ} (h : Nat.Coprime p H.condN) : H.psAt p = 1 ∨ H.psAt p = -1 := by
  rw [H.psAt_of_coprime h]
  rcases Int.units_eq_one_or (H.art (ZMod.unitOfCoprime p h)).1.1 with h1 | h1 <;> simp [h1]

/- English proof (translation)
Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Conclude with `Nat.mod_modEq p _`.
-/
theorem val_unitOfCoprime {p : ℕ} (h : Nat.Coprime p H.condN) :
    ((ZMod.unitOfCoprime p h : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ p [MOD H.condN] := by
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  exact Nat.mod_modEq p _

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `h2p : 2 ∣ p` using `by omega`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.Coprime.coprime_dvd_left h2p h) H.two_dvd_condN`.
-/
theorem odd_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : p % 2 = 1 := by
  by_contra hc
  have h2p : 2 ∣ p := by omega
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.Coprime.coprime_dvd_left h2p h) H.two_dvd_condN

variable {H} in

/- English proof (translation)
Rewrite using `[H.psAt_of_coprime h, hP, jacobi_neg_recip H.q_mod_four (H.odd_of_coprime h)]`. Conclude with `jacobi_congr ((H.val_unitOfCoprime h).of_dvd H.q_dvd_condN)`.
-/
theorem PsQ.psAt_eq (hP : H.PsQ) {p : ℕ} (h : Nat.Coprime p H.condN) : H.psAt p = jacobiSym (-(H.q : ℤ)) p := by
  rw [H.psAt_of_coprime h, hP, jacobi_neg_recip H.q_mod_four (H.odd_of_coprime h)]
  exact jacobi_congr ((H.val_unitOfCoprime h).of_dvd H.q_dvd_condN)

variable {H} in
/- English proof (translation)
The claim follows from `hP.psAt_eq ((Nat.Prime.coprime_iff_not_dvd hp).2 h)`.
-/
theorem PsQ.psAt_prime (hP : H.PsQ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) :
    H.psAt p = jacobiSym (-(H.q : ℤ)) p :=
  hP.psAt_eq ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

/- English proof (translation)
The claim follows from `IntermediateField.mem_adjoin_simple_self ℚ H.sqd`.
-/
theorem sqd_mem_K : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd

/- English proof (translation)
Establish `hint : IsIntegral ℚ H.sqd` using `Algebra.IsIntegral.isIntegral _`. Unfold `HostRaw.K`. Rewrite using `[IntermediateField.adjoin.finrank hint]`. Establish `hp0 : (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) : Polynomial ℚ) ≠ 0` using `Polynomial.X_pow_add_C_ne_zero (by norm_num) _`. Establish `hpa : Polynomial.aeval H.sqd (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ)) = 0`.

Simplify using `[H.sqd_sq]`. Establish `hle : (minpoly ℚ H.sqd).natDegree ≤ 2`. Establish `hd` using `minpoly.degree_le_of_ne_zero ℚ H.sqd hp0 hpa`. Rewrite `hd` using `[Polynomial.degree_X_pow_add_C (by norm_num)]`. Conclude with `Polynomial.natDegree_le_of_degree_le hd`.

Establish `hpos` using `minpoly.natDegree_pos hint`. Establish `hne1 : (minpoly ℚ H.sqd).natDegree ≠ 1`. Introduce `h1`. Take `⟨r, hr⟩` from `minpoly.natDegree_eq_one_iff.1 h1`. Establish `hsq` using `H.sqd_sq`.

Rewrite `hsq` using `[← hr]`. Establish `hr2 : r ^ 2 = -(H.d : ℚ)`. Apply `(algebraMap ℚ H.E).injective` to reduce the goal to its premises. Rewrite using `[map_pow, hsq, map_neg, map_natCast]`. Establish `h0 : (0 : ℚ) ≤ r ^ 2` using `sq_nonneg r`.

Establish `hd : (0 : ℚ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Combine the linear equalities and inequalities to obtain the conclusion. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  have hint : IsIntegral ℚ H.sqd := Algebra.IsIntegral.isIntegral _
  unfold HostRaw.K
  rw [IntermediateField.adjoin.finrank hint]
  have hp0 : (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_add_C_ne_zero (by norm_num) _
  have hpa : Polynomial.aeval H.sqd (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ)) = 0 := by
    simp [H.sqd_sq]
  have hle : (minpoly ℚ H.sqd).natDegree ≤ 2 := by
    have hd := minpoly.degree_le_of_ne_zero ℚ H.sqd hp0 hpa
    rw [Polynomial.degree_X_pow_add_C (by norm_num)] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hpos := minpoly.natDegree_pos hint
  have hne1 : (minpoly ℚ H.sqd).natDegree ≠ 1 := by
    intro h1
    obtain ⟨r, hr⟩ := minpoly.natDegree_eq_one_iff.1 h1
    have hsq := H.sqd_sq
    rw [← hr] at hsq
    have hr2 : r ^ 2 = -(H.d : ℚ) := by
      apply (algebraMap ℚ H.E).injective
      rw [map_pow, hsq, map_neg, map_natCast]
    have h0 : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
    have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
    linarith
  omega

/- English proof (translation)
The claim follows from `SplitK.ram_ncard H.d_prime H.sqd_sq`.
-/
theorem ncard_primesOver_d : (primesOver (span {(H.d : ℤ)}) (𝓞 H.K)).ncard = 1 :=
  SplitK.ram_ncard H.d_prime H.sqd_sq

/- English proof (translation)
The claim follows from `H.gal.injective (by rw [map_mul, map_mul, mul_comm])`.
-/
theorem gal_comm (σ τ : H.E ≃ₐ[ℚ] H.E) : σ * τ = τ * σ :=
  H.gal.injective (by rw [map_mul, map_mul, mul_comm])

/- English proof (translation)
The claim follows from `H.gal.apply_symm_apply φ.cc`.
-/
theorem gal_conj : H.gal H.conj = φ.cc := H.gal.apply_symm_apply φ.cc

/- English proof (translation)
The claim follows from `H.gal.injective (by rw [map_mul, H.gal_conj, map_one]; simp [Frame.cc, c0, Prod.ext_iff])`.
-/
theorem conj_mul_conj : H.conj * H.conj = 1 :=
  H.gal.injective (by rw [map_mul, H.gal_conj, map_one]; simp [Frame.cc, c0, Prod.ext_iff])

/- English proof (translation)
Rewrite using `[← AlgEquiv.mul_apply, H.conj_mul_conj, AlgEquiv.one_apply]`.
-/
theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  rw [← AlgEquiv.mul_apply, H.conj_mul_conj, AlgEquiv.one_apply]

/- English proof (translation)
Introduce `h`. Establish `e` using `H.gal_conj`. Rewrite `e` using `[h, map_one]`. Simplify using `[Frame.cc, c0, Prod.ext_iff] at e`.
-/
theorem conj_ne_one : H.conj ≠ 1 := by
  intro h
  have e := H.gal_conj
  rw [h, map_one] at e
  simp [Frame.cc, c0, Prod.ext_iff] at e

/- English proof (translation)
Rewrite using `[H.gal_sqd, H.gal_conj]`. Simplify using `[Frame.cc, c0]`.
-/
theorem conj_sqd : H.conj H.sqd = -H.sqd := by
  rw [H.gal_sqd, H.gal_conj]
  simp [Frame.cc, c0]

/- English proof (translation)
Use `haveI := H.galois`. Establish `hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => ψ.comp (σ : H.E →+* H.E))`. Introduce `σ τ h`. Use extensionality with `x`. Conclude with `ψ.injective (congrArg (fun g : H.E →+* ℂ => g x) h)`.

Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨hinj, by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, NumberField.Embeddings.card]⟩`.
-/
theorem hostEmb (ψ : H.E →+* ℂ) :
    Function.Bijective (fun σ : H.E ≃ₐ[ℚ] H.E => ψ.comp (σ : H.E →+* H.E)) := by
  haveI := H.galois
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => ψ.comp (σ : H.E →+* H.E)) := by
    intro σ τ h
    ext x
    exact ψ.injective (congrArg (fun g : H.E →+* ℂ => g x) h)
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, NumberField.Embeddings.card]⟩

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

/- English proof (translation)
Establish `h` using `Module.finrank_mul_finrank ℚ H.K H.E`. Rewrite `h` using `[H.finrank_K, H.der.finrank_E]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_EK : Module.finrank H.K H.E = 2 * φ.ord := by
  have h := Module.finrank_mul_finrank ℚ H.K H.E
  rw [H.finrank_K, H.der.finrank_E] at h
  omega

/- English proof (translation)
Take `⟨ha, hb, -⟩` from `(H.der.frob p hp P).2.2.1 σ hσ`. Apply the tactic sequence `rcases Int.units_eq_one_or (H.galE σ).1.1 with h1 | h1 <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or (H.galE σ).1.2 with h2 | h2 <;>`. Simplify using `[Prod.ext_iff, c0, h1, h2, ← ha, ← hb]`.
-/
theorem hostClasses (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    (((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1)) ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
    ((H.galE σ).1 = (1, -1) ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1)) ∧
    ((H.galE σ).1 = c0 ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = -1)) := by
  obtain ⟨ha, hb, -⟩ := (H.der.frob p hp P).2.2.1 σ hσ
  rcases Int.units_eq_one_or (H.galE σ).1.1 with h1 | h1 <;>
    rcases Int.units_eq_one_or (H.galE σ).1.2 with h2 | h2 <;>
    simp [Prod.ext_iff, c0, h1, h2, ← ha, ← hb]

/- English proof (translation)
Establish `h` using `H.hostClasses p hp P σ hσ`. Rewrite `h` using `[hP.psAt_prime Fact.out hp]`. Conclude with `h`.
-/
theorem hostClassesQ (hP : H.PsQ) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    (((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1)) ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
    ((H.galE σ).1 = (1, -1) ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = 1)) ∧
    ((H.galE σ).1 = c0 ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = -1)) := by
  have h := H.hostClasses p hp P σ hσ
  rw [hP.psAt_prime Fact.out hp] at h
  exact h

/- English proof (translation)
The claim follows from `(H.der.frob p ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hp) P).2.1 σ _ (ZMod.coe_unitOfCoprime p hp)`.
-/
theorem frob_iff (p : ℕ) [Fact p.Prime] (hp : Nat.Coprime p H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) :
    IsArithFrobAt ℤ σ P ↔ H.galE σ = H.art (ZMod.unitOfCoprime p hp) :=
  (H.der.frob p ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hp) P).2.1 σ _ (ZMod.coe_unitOfCoprime p hp)

/- English proof (translation)
Establish `h3` using `((H.der.frob p hp P).2.2.1 σ hσ).2.1`. Rewrite using `[Frame.Psi, MonoidHom.mem_ker, ← h3]`. Simplify using `[Frame.chD, Units.val_eq_one]`.
-/
theorem frob_mem_Psi_iff (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.galE σ ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
  have h3 := ((H.der.frob p hp P).2.2.1 σ hσ).2.1
  rw [Frame.Psi, MonoidHom.mem_ker, ← h3]
  simp [Frame.chD, Units.val_eq_one]

/- English proof (translation)
Rewrite using `[H.der.splitK l hl]`. Distinguish the cases in `h2 : l = 2`. Conclude with `Or.inl h2`. Use `right`. Use `⟨h2, ?_⟩` and prove the remaining obligations.

Break down `(H.dvd_QSq_iff hl).1 h with h' | h'` into its components or cases. Conclude with `H.QS_split l hl h2 h'`. Substitute `h'` using the available equality. Conclude with `H.hyp.2.2.2.2`.
-/
theorem splitK_of_dvd {l : ℕ} (hl : l.Prime) (h : l ∣ H.QS * H.q) :
    (primesOver (span {(l : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  rw [H.der.splitK l hl]
  by_cases h2 : l = 2
  · exact Or.inl h2
  right
  refine ⟨h2, ?_⟩
  rcases (H.dvd_QSq_iff hl).1 h with h' | h'
  · exact H.QS_split l hl h2 h'
  · subst h'
    exact H.hyp.2.2.2.2

/- English proof (translation)
Use `⟨H.der.splitK, H.ncard_primesOver_d, H.splitK_of_dvd H.q_prime (dvd_mul_left _ _), ?_⟩` and prove the remaining obligations. Introduce `p _ hp P _ _ σ hσ`. Rewrite using `[H.frob_mem_Psi_iff p hp P σ hσ, H.der.splitK p Fact.out]`. Simplify using `[H.ne_two_of_not_dvd hp]`.
-/
theorem hostSplitK :
    (∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))) ∧
    (primesOver (span {(H.d : ℤ)}) (𝓞 H.K)).ncard = 1 ∧
    (primesOver (span {(H.q : ℤ)}) (𝓞 H.K)).ncard = 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
      (H.galE σ ∈ φ.Psi ↔ (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2) := by
  refine ⟨H.der.splitK, H.ncard_primesOver_d, H.splitK_of_dvd H.q_prime (dvd_mul_left _ _), ?_⟩
  intro p _ hp P _ _ σ hσ
  rw [H.frob_mem_Psi_iff p hp P σ hσ, H.der.splitK p Fact.out]
  simp [H.ne_two_of_not_dvd hp]

/- English proof (translation)
Conclude with `(H.der.eta.2.1 p hp P σ hσ).trans (h2.cc_mem_zpowers_iff _)`.
-/
theorem eta_eq_neg_one_iff (h2 : φ.TwoGroup) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.galE σ = φ.cc := by
  exact (H.der.eta.2.1 p hp P σ hσ).trans (h2.cc_mem_zpowers_iff _)

/- English proof (translation)
Establish `h` using `Orbits.dim_bound k g hg M hM hne`. Rewrite `h` using `[H.der.finrank_E]`. Conclude with `h`.
-/
theorem hostFiniteOrder (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) H.E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ 4 * φ.ord * k := by
  have h := Orbits.dim_bound k g hg M hM hne
  rw [H.der.finrank_E] at h
  exact h

/- English proof (translation)
Rewrite using `[Subgroup.eq_bot_iff_forall]`. Introduce `γ hγ`. Take `⟨m, hm⟩` from `hΓ γ hγ`. Consider the cases of `m with`. Consider the case `zero => simpa using hm`.

Consider the case `succ m`. It suffices to derive a contradiction. Establish `h1` using `orderOf_pow_orderOf_div (x := γ) (n := g) (by rw [hm]; exact pow_ne_zero _ hg.ne_zero) (by rw [hm]; exact dvd_pow_self g (Nat.succ_ne_zero m))`. Establish `hpow` using `pow_orderOf_eq_one (γ ^ (orderOf γ / g))`. Rewrite `hpow` using `[h1]`.

Establish `hMg : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ^ g = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, hpow, Units.val_one]`. Establish `hne : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ≠ 1`. Introduce `h`. Establish `h0 : γ ^ (orderOf γ / g) = 1` using `Units.ext (by rw [Units.val_one]; exact h)`.

Rewrite `h1` using `[h0, orderOf_one]`. Conclude with `hg.one_lt.ne h1`. Use `H.hostFiniteOrder k g hg _ hMg hne` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem hostStab (k g : ℕ) (hg : g.Prime) (hlt : 4 * φ.ord * k < g - 1)
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) H.E)) (hΓ : ∀ γ ∈ Γ, ∃ m : ℕ, orderOf γ = g ^ m) : Γ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  obtain ⟨m, hm⟩ := hΓ γ hγ
  cases m with
  | zero => simpa using hm
  | succ m =>
    exfalso
    have h1 := orderOf_pow_orderOf_div (x := γ) (n := g) (by rw [hm]; exact pow_ne_zero _ hg.ne_zero)
      (by rw [hm]; exact dvd_pow_self g (Nat.succ_ne_zero m))
    have hpow := pow_orderOf_eq_one (γ ^ (orderOf γ / g))
    rw [h1] at hpow
    have hMg : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ^ g = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
    have hne : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ≠ 1 := by
      intro h
      have h0 : γ ^ (orderOf γ / g) = 1 := Units.ext (by rw [Units.val_one]; exact h)
      rw [h0, orderOf_one] at h1
      exact hg.one_lt.ne h1
    have := H.hostFiniteOrder k g hg _ hMg hne
    omega

end HostAx

end Formalism.HC

end
