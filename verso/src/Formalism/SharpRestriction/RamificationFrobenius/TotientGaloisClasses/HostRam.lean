import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

/- English proof (translation)
Assemble the required witnesses or components as `⟨ZMod.unitOfCoprime x hx, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq x N⟩`.
-/
theorem exists_unit_val {N : ℕ} [NeZero N] {x : ℕ} (hx : Nat.Coprime x N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD N] :=
  ⟨ZMod.unitOfCoprime x hx, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq x N⟩

/- English proof (translation)
Take `⟨z, hza, hzb⟩` from `Nat.chineseRemainder hab x y`. Establish `hza' : Nat.Coprime z a` using `Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hza).trans (Nat.coprime_iff_gcd_eq_one.mp hx))`. Establish `hzb' : Nat.Coprime z b` using `Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hzb).trans (Nat.coprime_iff_gcd_eq_one.mp hy))`. Establish `hz : Nat.Coprime z N`. Rewrite using `[hN]`.

Conclude with `Nat.Coprime.mul_right hza' hzb'`. Take `⟨u, hu⟩` from `exists_unit_val hz`. Conclude with `⟨u, (Nat.ModEq.of_dvd ⟨b, hN⟩ hu).trans hza, (Nat.ModEq.of_dvd ⟨a, hN.trans (Nat.mul_comm a b)⟩ hu).trans hzb⟩`.
-/
theorem exists_unit_crt {N a b : ℕ} [NeZero N] (hN : N = a * b) (hab : Nat.Coprime a b) {x y : ℕ}
    (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD a] ∧ (u : ZMod N).val ≡ y [MOD b] := by
  obtain ⟨z, hza, hzb⟩ := Nat.chineseRemainder hab x y
  have hza' : Nat.Coprime z a :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hza).trans (Nat.coprime_iff_gcd_eq_one.mp hx))
  have hzb' : Nat.Coprime z b :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hzb).trans (Nat.coprime_iff_gcd_eq_one.mp hy))
  have hz : Nat.Coprime z N := by
    rw [hN]
    exact Nat.Coprime.mul_right hza' hzb'
  obtain ⟨u, hu⟩ := exists_unit_val hz
  exact ⟨u, (Nat.ModEq.of_dvd ⟨b, hN⟩ hu).trans hza, (Nat.ModEq.of_dvd ⟨a, hN.trans (Nat.mul_comm a b)⟩ hu).trans hzb⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h2 : Nat.gcd (p - 1) p ∣ p - 1 + 1`. Rewrite using `[show p - 1 + 1 = p by omega]`. Conclude with `Nat.gcd_dvd_right _ _`. Conclude with `Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h2)`.

Establish `hodd : Odd p` using `Nat.odd_iff.mpr (by omega)`. Establish `hmod : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ)`. Rewrite using `[Int.emod_eq_emod_iff_emod_sub_eq_zero]`. Move the coercions through the operations in `[Nat.cast_sub (by omega : 1 ≤ p)]`. Simplify using the standard rewrite rules.

Rewrite using `[jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]`.
-/
theorem jacobi_pred {p : ℕ} (hp4 : p % 4 = 3) : Nat.Coprime (p - 1) p ∧ jacobiSym ((p - 1 : ℕ) : ℤ) p = -1 := by
  constructor
  · have h2 : Nat.gcd (p - 1) p ∣ p - 1 + 1 := by
      rw [show p - 1 + 1 = p by omega]
      exact Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h2)
  · have hodd : Odd p := Nat.odd_iff.mpr (by omega)
    have hmod : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]

/- English proof (translation)
Establish `hnd : ¬ l ∣ m` using `(Nat.Prime.coprime_iff_not_dvd hl).mp (Nat.Coprime.symm hm)`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hnd (dvd_zero l)`. Establish `hf : (m * l).factorization l = 1`.

Rewrite using `[Nat.factorization_mul hm0 hl.ne_zero, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd, hl.factorization_self, zero_add]`. Rewrite using `[hf, pow_one, Nat.mul_div_cancel _ hl.pos]`.
-/
theorem ordCompl_mul_prime {m l : ℕ} (hl : l.Prime) (hm : Nat.Coprime m l) : ordCompl[l] (m * l) = m := by
  have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl).mp (Nat.Coprime.symm hm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero l)
  have hf : (m * l).factorization l = 1 := by
    rw [Nat.factorization_mul hm0 hl.ne_zero, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
      hl.factorization_self, zero_add]
  rw [hf, pow_one, Nat.mul_div_cancel _ hl.pos]

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Rewrite using `[HostRaw.condN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem condN_eq_q : H.condN = H.QS * H.d * H.q := by
  rw [HostRaw.condN]
  ring

/- English proof (translation)
Take `⟨hq, -, -, -, -⟩` from `H.hyp`. Rewrite using `[condN_eq_q, Nat.mul_div_cancel _ hq.pos]`.
-/
theorem condN_div_q : H.condN / H.q = H.QS * H.d := by
  obtain ⟨hq, -, -, -, -⟩ := H.hyp
  rw [condN_eq_q, Nat.mul_div_cancel _ hq.pos]

/- English proof (translation)
Take `⟨-, hd, -, -, -⟩` from `H.hyp`. Rewrite using `[HostRaw.condN, Nat.mul_div_cancel _ hd.pos]`.
-/
theorem condN_div_d : H.condN / H.d = H.QS * H.q := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  rw [HostRaw.condN, Nat.mul_div_cancel _ hd.pos]

/- English proof (translation)
Take `⟨hq, hd, hq8, hd16, -⟩` from `H.hyp`. Rewrite using `[condN_eq_q]`. Apply `ordCompl_mul_prime hq` to reduce the goal to its premises. Establish `hqd : Nat.Coprime H.d H.q` using `(Nat.coprime_primes hd hq).mpr (by omega)`. Conclude with `Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd`.
-/
theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  rw [condN_eq_q]
  apply ordCompl_mul_prime hq
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  exact Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd

variable {H}

/- English proof (translation)
Take `⟨hq, hd, hq8, hd16, -⟩` from `H.hyp`. Establish `hq4 : H.q % 4 = 3` using `by omega`. Take `⟨hcop, hj⟩` from `jacobi_pred hq4`. Establish `hqd : Nat.Coprime H.d H.q` using `(Nat.coprime_primes hd hq).mpr (by omega)`. Establish `hc : Nat.Coprime (H.QS * H.d) H.q` using `Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd`.

Use `haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩`. Take `⟨u, hu1, hu2⟩` from `exists_unit_crt (N := H.condN) (condN_eq_q H) hc (Nat.coprime_one_left _) hcop`. Use `⟨u, hu1, ?_⟩` and prove the remaining obligations. Establish `hu2' : (u : ZMod H.condN).val % H.q = (H.q - 1) % H.q` using `hu2`. Establish `h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.q : ℤ) = ((H.q - 1 : ℕ) : ℤ) % (H.q : ℤ)`.

Conclude with `hu2'` after adjusting the coercions. Establish `h3 : (((H.art u).1.1 : ℤˣ) : ℤ) = -1`. Rewrite using `[hP u, jacobiSym.mod_left' h2, hj]`. Conclude with `Units.ext (by simpa using h3)`.
-/
theorem PsQ.exists_q (hP : H.PsQ) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hq4 : H.q % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hq4
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.d) H.q :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (condN_eq_q H) hc (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.q = (H.q - 1) % H.q := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.q : ℤ) = ((H.q - 1 : ℕ) : ℤ) % (H.q : ℤ) := by
    exact_mod_cast hu2'
  have h3 : (((H.art u).1.1 : ℤˣ) : ℤ) = -1 := by
    rw [hP u, jacobiSym.mod_left' h2, hj]
  exact Units.ext (by simpa using h3)

/- English proof (translation)
Introduce `hdvd`. Take `⟨u, hu, hne⟩` from `hE l hl ((dvd_pow_self l (by norm_num)).trans hdvd)`. Take `⟨m, hm⟩` from `hdvd.trans H.QS_dvd_condN`. Establish `hdiv : H.condN / l = l * m` using `by rw [hm, sq, mul_assoc, Nat.mul_div_cancel_left _ hl.pos]`. Rewrite `hu` using `[hdiv]`.

Take `⟨a, ha⟩` from `(Nat.modEq_iff_dvd.1 hu.symm)`. Use `set x : ZMod H.condN := (l : ZMod H.condN) * m * a with hx`. Establish `hN0 : (l : ZMod H.condN) ^ 2 * m = 0`. Use `ZMod.natCast_self H.condN` as an intermediate fact. Use `conv_lhs at this => rw [show ((H.condN : ℕ) : ZMod H.condN) = ((l ^ 2 * m : ℕ) : ZMod H.condN) from congrArg _ hm]`.

Conclude with `this` after adjusting the coercions. Establish `hux : (u : ZMod H.condN) = 1 + x`. Use `congrArg (fun z : ℤ => (z : ZMod H.condN)) ha` as an intermediate fact. Simplify using `only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Nat.cast_one, Int.cast_one, Int.cast_mul, Nat.cast_mul] at this`. Rewrite using `[hx]`.

Take the linear combination `this`. Establish `hxx : x * x = 0` using `by rw [hx]; linear_combination (m * a * a : ZMod H.condN) * hN0`. Establish `hpow : ∀ n : ℕ, (1 + x) ^ n = 1 + n * x`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ih]`. Use `push_cast`. Take the linear combination `(n : ZMod H.condN) * hxx`. Establish `hul : u ^ l = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, hux, hpow, Units.val_one, hx]`. Take the linear combination `(a : ZMod H.condN) * hN0`. Establish `h3 : orderOf (H.art u) ∣ l` using `orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hul, map_one])`. Take `⟨i, hi⟩` from `h2.orderOf_GG (H.art u)`.

Break down `(Nat.dvd_prime hl).1 h3 with h | h` into its components or cases. Conclude with `hne (orderOf_eq_one_iff.1 h)`. Rewrite `h` using `[hi]`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h.symm.dvd))`.
-/
theorem Exact.not_sq_dvd (hE : H.Exact) (h2 : φ.TwoGroup) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) : ¬ l ^ 2 ∣ H.QS := by
  intro hdvd
  obtain ⟨u, hu, hne⟩ := hE l hl ((dvd_pow_self l (by norm_num)).trans hdvd)
  obtain ⟨m, hm⟩ := hdvd.trans H.QS_dvd_condN
  have hdiv : H.condN / l = l * m := by rw [hm, sq, mul_assoc, Nat.mul_div_cancel_left _ hl.pos]
  rw [hdiv] at hu
  obtain ⟨a, ha⟩ := (Nat.modEq_iff_dvd.1 hu.symm)
  set x : ZMod H.condN := (l : ZMod H.condN) * m * a with hx
  have hN0 : (l : ZMod H.condN) ^ 2 * m = 0 := by
    have := ZMod.natCast_self H.condN
    conv_lhs at this => rw [show ((H.condN : ℕ) : ZMod H.condN) = ((l ^ 2 * m : ℕ) : ZMod H.condN) from congrArg _ hm]
    exact_mod_cast this
  have hux : (u : ZMod H.condN) = 1 + x := by
    have := congrArg (fun z : ℤ => (z : ZMod H.condN)) ha
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Nat.cast_one, Int.cast_one, Int.cast_mul,
      Nat.cast_mul] at this
    rw [hx]; linear_combination this
  have hxx : x * x = 0 := by rw [hx]; linear_combination (m * a * a : ZMod H.condN) * hN0
  have hpow : ∀ n : ℕ, (1 + x) ^ n = 1 + n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih]; push_cast; linear_combination (n : ZMod H.condN) * hxx
  have hul : u ^ l = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hux, hpow, Units.val_one, hx]
    linear_combination (a : ZMod H.condN) * hN0
  have h3 : orderOf (H.art u) ∣ l := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hul, map_one])
  obtain ⟨i, hi⟩ := h2.orderOf_GG (H.art u)
  rcases (Nat.dvd_prime hl).1 h3 with h | h
  · exact hne (orderOf_eq_one_iff.1 h)
  · rw [hi] at h
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h.symm.dvd))

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

/- English proof (translation)
Take `⟨hq, hd, hq8, hd16, -⟩` from `H.hyp`. Establish `hd4 : H.d % 4 = 3` using `by omega`. Take `⟨hcop, hj⟩` from `jacobi_pred hd4`. Establish `hqd : Nat.Coprime H.q H.d` using `(Nat.coprime_primes hq hd).mpr (by omega)`. Establish `hc : Nat.Coprime (H.QS * H.q) H.d` using `Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left H.d H.q) H.QS_coprime) hqd`.

Use `haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩`. Take `⟨u, hu1, hu2⟩` from `exists_unit_crt (N := H.condN) (a := H.QS * H.q) (b := H.d) rfl hc (Nat.coprime_one_left _) hcop`. Use `⟨u, hu1, ?_⟩` and prove the remaining obligations. Establish `hu2' : (u : ZMod H.condN).val % H.d = (H.d - 1) % H.d` using `hu2`. Establish `h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.d : ℤ) = ((H.d - 1 : ℕ) : ℤ) % (H.d : ℤ)`.

Conclude with `hu2'` after adjusting the coercions. Establish `h3` using `H.der.art_ch u`. Rewrite `h3` using `[jacobiSym.mod_left' h2, hj]`. Break down `H.art_d u hu1 with h | h` into its components or cases. It suffices to derive a contradiction.

Rewrite `h3` using `[h]`. Simplify using `at h3`. Conclude with `h`.
-/
theorem exists_d : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hd4 : H.d % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hd4
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.q) H.d :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left H.d H.q) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (a := H.QS * H.q) (b := H.d) rfl hc
    (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.d = (H.d - 1) % H.d := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.d : ℤ) = ((H.d - 1 : ℕ) : ℤ) % (H.d : ℤ) := by
    exact_mod_cast hu2'
  have h3 := H.der.art_ch u
  rw [jacobiSym.mod_left' h2, hj] at h3
  rcases H.art_d u hu1 with h | h
  · exfalso
    rw [h] at h3
    simp at h3
  · exact h

/- English proof (translation)
Take `⟨hq, hd, -, -, -⟩` from `H.hyp`. Break down `(Nat.Prime.dvd_mul hl).mp h with h' | h'` into its components or cases. Break down `(Nat.Prime.dvd_mul hl).mp h' with h'' | h''` into its components or cases. Conclude with `hE l hl h''`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hl hq).mp h'', HostRaw.condN_div_q]`.

Take `⟨u, hu1, hu2⟩` from `hP.exists_q`. Use `⟨u, hu1, fun h1 => ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (fun x : ℤˣ => (x : ℤ)) hu2`. Rewrite `h3` using `[h1]`. Simplify using `at h3`.

Rewrite using `[(Nat.prime_dvd_prime_iff_eq hl hd).mp h', HostRaw.condN_div_d]`. Take `⟨u, hu1, hu2⟩` from `exists_d H`. Use `⟨u, hu1, fun h1 => ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) (hu2.symm.trans h1)`. Simplify using `[Frame.iod] at h3`.
-/
theorem exact_all (hP : H.PsQ) (hE : H.Exact) (l : ℕ) (hl : l.Prime) (h : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  obtain ⟨hq, hd, -, -, -⟩ := H.hyp
  rcases (Nat.Prime.dvd_mul hl).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul hl).mp h' with h'' | h''
    · exact hE l hl h''
    · rw [(Nat.prime_dvd_prime_iff_eq hl hq).mp h'', HostRaw.condN_div_q]
      obtain ⟨u, hu1, hu2⟩ := hP.exists_q
      refine ⟨u, hu1, fun h1 => ?_⟩
      have h3 := congrArg (fun x : ℤˣ => (x : ℤ)) hu2
      rw [h1] at h3
      simp at h3
  · rw [(Nat.prime_dvd_prime_iff_eq hl hd).mp h', HostRaw.condN_div_d]
    obtain ⟨u, hu1, hu2⟩ := exists_d H
    refine ⟨u, hu1, fun h1 => ?_⟩
    have h3 := congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) (hu2.symm.trans h1)
    simp [Frame.iod] at h3

/- English proof (translation)
Use `H.galois` as an intermediate fact. Establish `: IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E`. Use `SplitK.span_prime p` as an intermediate fact. Rewrite using `[← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(H.E/ℚ), ← card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(p : ℤ)}) P, Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]`. Both sides reduce to the same expression.
-/
theorem ramificationIdx_eq_one_iff (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.ramificationIdx ℤ = 1 ↔ ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) → σ = 1 := by
  have := H.galois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have := SplitK.span_prime p
  rw [← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(H.E/ℚ),
    ← card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(p : ℤ)}) P, Subgroup.card_eq_one,
    Subgroup.eq_bot_iff_forall]
  rfl

end HostAx

end Formalism.HC

end
