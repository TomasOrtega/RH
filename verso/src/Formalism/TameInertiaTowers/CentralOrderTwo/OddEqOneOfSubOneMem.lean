import Mathlib
import Formalism.TameInertiaTowers.StatementField
import Formalism.TameInertiaTowers.InvLength
import Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral

open NumberField Ideal

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def, Ideal.mem_comap, eq_intCast]`.
-/
theorem odd_intCast_mem_iff {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 L) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

/- English proof (translation)
Rewrite using `[← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]`.
-/
theorem odd_card_under {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]

/- English proof (translation)
Introduce `h`. Establish `h' : ((m : ℤ) : 𝓞 L) ∈ P` using `by exact_mod_cast h`. Rewrite `h'` using `[odd_intCast_mem_iff p P]`. Conclude with `hpm (by exact_mod_cast h')`.
-/
theorem odd_natCast_not_mem {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] (m : ℕ) (hpm : ¬ p ∣ m) :
    (m : 𝓞 L) ∉ P := by
  intro h
  have h' : ((m : ℤ) : 𝓞 L) ∈ P := by exact_mod_cast h
  rw [odd_intCast_mem_iff p P] at h'
  exact hpm (by exact_mod_cast h')

/- English proof (translation)
Introduce `h`. Conclude with `hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))`.
-/
theorem odd_two_pow_not_dvd (r n : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 2 ^ n := by
  intro h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem odd_coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

/- English proof (translation)
Unfold `sgn`. Use `split_ifs with h`. Simplify using `[h]`. Establish `h2 : (σ x) ^ 2 = x ^ 2` using `by rw [← map_pow, hx, map_intCast]`. Establish `: (σ x - x) * (σ x + x) = 0` using `by linear_combination h2`.

Break down `mul_eq_zero.mp this with h' | h'` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h') h`. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]`. Take the linear combination `h'`.
-/
theorem odd_sgn_spec {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = (c : L)) : σ x = (((sgn σ x : ℤˣ) : ℤ) : L) * x := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · have h2 : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have : (σ x - x) * (σ x + x) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      linear_combination h'

/- English proof (translation)
Establish `hint : IsIntegral ℤ x`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hx, ← eq_intCast (algebraMap ℤ L)]`. Conclude with `isIntegral_algebraMap`. Use `⟨⟨x, hint⟩, rfl, ?_⟩` and prove the remaining obligations.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `only [map_intCast]`. Conclude with `hx`.
-/
theorem odd_lift {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) :
    ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = (c : 𝓞 L) := by
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx, ← eq_intCast (algebraMap ℤ L)]
    exact isIntegral_algebraMap
  refine ⟨⟨x, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hx

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show ((σ • X : 𝓞 L) : L) = ((((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X : 𝓞 L)`. Rewrite using `[odd_coe_smul, hX, odd_sgn_spec σ x c hx]`. Simplify using `[hX]`.
-/
theorem odd_smul_lift {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = (c : L)) (X : 𝓞 L) (hX : (X : L) = x) :
    σ • X = (((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X := by
  apply RingOfIntegers.coe_injective
  show ((σ • X : 𝓞 L) : L) = ((((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X : 𝓞 L)
  rw [odd_coe_smul, hX, odd_sgn_spec σ x c hx]
  simp [hX]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hsum : ∑ i ∈ Finset.range m, η ^ i = 0`. Use `geom_sum_mul η m` as an intermediate fact. Rewrite `this` using `[hη, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)`.

Establish `hmem : ∑ i ∈ Finset.range m, (η ^ i - 1) ∈ P` using `Ideal.sum_mem _ fun i _ => by`. Rewrite using `[← geom_sum_mul η i]`. Conclude with `P.mul_mem_left _ h`. Rewrite `hmem` using `[Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_one, zero_sub]`. Conclude with `hm (P.neg_mem_iff.mp hmem)`.
-/
theorem odd_eq_one_of_sub_one_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) {η : S}
    {m : ℕ} (hη : η ^ m = 1) (hm : (m : S) ∉ P) (h : η - 1 ∈ P) : η = 1 := by
  by_contra hne
  have hsum : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hmem : ∑ i ∈ Finset.range m, (η ^ i - 1) ∈ P := Ideal.sum_mem _ fun i _ => by
    rw [← geom_sum_mul η i]
    exact P.mul_mem_left _ h
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_one,
    zero_sub] at hmem
  exact hm (P.neg_mem_iff.mp hmem)

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hmem` using `odd_intCast_mem_iff p P`. Establish `hF : ∀ y : 𝓞 L, σ • y - y ^ p ∈ P`. Introduce `y`. Use `H y` as an intermediate fact.

Rewrite `this` using `[odd_card_under p P]`. Conclude with `this`. Take `⟨A, hAcoe, hA2⟩` from `odd_lift x c hx`. Establish `hσA` using `odd_smul_lift σ x c hx A hAcoe`. Establish `hAnot : A ∉ P`.

Introduce `hA`. Apply `hpc` to reduce the goal to its premises. Rewrite using `[← hmem, ← hA2]`. Conclude with `P.pow_mem_of_mem hA 2 (by norm_num)`. Establish `hodd : p % 2 = 1` using `Nat.odd_iff.mp (hp.odd_of_ne_two hp2)`.

Establish `hpow : A ^ p = A * (c : 𝓞 L) ^ (p / 2)`. Rewrite using `[← hA2, ← pow_mul, ← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hE : (p : ℤ) ∣ c ^ (p / 2) - legendreSym p c`.

Rewrite using `[← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hE' : (c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L) ∈ P`. Use `(hmem _).mpr hE` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hprod : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A ∈ P`. Establish `heq : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A = (σ • A - A ^ p) + A * ((c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L))`. Rewrite using `[hσA, hpow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `P.add_mem (hF A) (P.mul_mem_left A hE')`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym]`.

Establish `hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n`. Introduce and unpack `n (rfl | rfl) h`. Use `Int.le_of_dvd (by norm_num) h` as an intermediate fact. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)` as an intermediate fact. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Break down `(inferInstance : P.IsPrime).mem_or_mem hprod with h | h` into its components or cases. Rewrite `h` using `[hmem]`.

Establish `hL` using `legendreSym.eq_one_or_neg_one p (a := c) (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpc)`. Apply the tactic sequence `rcases Int.units_eq_one_or (sgn σ x) with h1 | h1 <;>`. Apply the tactic sequence `simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>`. Apply the tactic sequence `rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>`. Apply the tactic sequence `first | rfl | exact absurd h (hbad _ (by norm_num))`.

Conclude with `absurd h hAnot`.
-/
theorem odd_frob_sgn {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) (hpc : ¬ (p : ℤ) ∣ c) :
    ((sgn σ x : ℤˣ) : ℤ) = jacobiSym c p := by
  have hp : p.Prime := Fact.out
  have hmem := odd_intCast_mem_iff p P
  have hF : ∀ y : 𝓞 L, σ • y - y ^ p ∈ P := by
    intro y
    have := H y
    rw [odd_card_under p P] at this
    exact this
  obtain ⟨A, hAcoe, hA2⟩ := odd_lift x c hx
  have hσA := odd_smul_lift σ x c hx A hAcoe
  have hAnot : A ∉ P := by
    intro hA
    apply hpc
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpow : A ^ p = A * (c : 𝓞 L) ^ (p / 2) := by
    rw [← hA2, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have hE : (p : ℤ) ∣ c ^ (p / 2) - legendreSym p c := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
    push_cast
    rfl
  have hE' : (c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L) ∈ P := by
    have := (hmem _).mpr hE
    push_cast at this
    exact this
  have hprod : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A ∈ P := by
    have heq : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A =
        (σ • A - A ^ p) + A * ((c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L)) := by
      rw [hσA, hpow]
      push_cast
      ring
    rw [heq]
    exact P.add_mem (hF A) (P.mul_mem_left A hE')
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n := by
    rintro n (rfl | rfl) h
    · have := Int.le_of_dvd (by norm_num) h
      have := hp.two_le
      omega
    · have := Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)
      have := hp.two_le
      omega
  rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h | h
  · rw [hmem] at h
    have hL := legendreSym.eq_one_or_neg_one p (a := c)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpc)
    rcases Int.units_eq_one_or (sgn σ x) with h1 | h1 <;>
      simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
      rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
      first | rfl | exact absurd h (hbad _ (by norm_num))
  · exact absurd h hAnot

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[map_pow]`. Conclude with `(hζ.autToPow_spec ℚ σ).symm`.
-/
theorem odd_autToPow_smul {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    σ • hζ.toInteger = hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val := by
  apply RingOfIntegers.coe_injective
  rw [map_pow]
  exact (hζ.autToPow_spec ℚ σ).symm

/- English proof (translation)
Use `set Z := hζ.toInteger with hZdef`. Establish `hZ : IsPrimitiveRoot Z (2 ^ n)` using `hζ.toInteger_isPrimitiveRoot`. Use `set e := ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val with he`. Establish `h1 : Z ^ e - Z ∈ P` using `by rw [← odd_autToPow_smul hζ σ]; exact hσ Z`. Establish `hm1 : 1 ≤ 2 ^ n` using `Nat.one_le_two_pow`.

Establish `hZm : Z ^ (2 ^ n - 1) * Z = 1`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hm1, hZ.pow_eq_one]`. Establish `hη : (Z ^ e * Z ^ (2 ^ n - 1)) ^ (2 ^ n) = 1`. Rewrite using `[← pow_add, ← pow_mul, mul_comm, pow_mul, hZ.pow_eq_one, one_pow]`. Establish `hsub : Z ^ e * Z ^ (2 ^ n - 1) - 1 ∈ P`.

Establish `: Z ^ e * Z ^ (2 ^ n - 1) - 1 = (Z ^ e - Z) * Z ^ (2 ^ n - 1)`. Take the linear combination `hZm`. Rewrite using `[this]`. Conclude with `P.mul_mem_right _ h1`. Establish `hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P` using `odd_natCast_not_mem r P _ (odd_two_pow_not_dvd r n hr hr2)`.

Establish `hone` using `odd_eq_one_of_sub_one_mem P hη hm hsub`. Rewrite `hone` using `[← pow_add, hZ.pow_eq_one_iff_dvd]`. Establish `h2 : e + (2 ^ n - 1) ≡ 1 + (2 ^ n - 1) [MOD 2 ^ n]`. Rewrite using `[Nat.add_sub_cancel' hm1]`. Conclude with `(Nat.modEq_zero_iff_dvd.mpr hone).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm`.

Establish `h3 : e ≡ 1 [MOD 2 ^ n]` using `Nat.ModEq.add_right_cancel' _ h2`. Establish `h4 : (e : ZMod (2 ^ n)) = ((1 : ℕ) : ZMod (2 ^ n))` using `(ZMod.natCast_eq_natCast_iff _ _ _).mpr h3`. Rewrite `h4` using `[he, ZMod.natCast_zmod_val, Nat.cast_one]`. Conclude with `Units.ext (by rw [h4, Units.val_one])`.
-/
theorem odd_cyc_inertia {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L, σ • x - x ∈ P) : hζ.autToPow ℚ σ = 1 := by
  set Z := hζ.toInteger with hZdef
  have hZ : IsPrimitiveRoot Z (2 ^ n) := hζ.toInteger_isPrimitiveRoot
  set e := ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val with he
  have h1 : Z ^ e - Z ∈ P := by rw [← odd_autToPow_smul hζ σ]; exact hσ Z
  have hm1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hZm : Z ^ (2 ^ n - 1) * Z = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm1, hZ.pow_eq_one]
  have hη : (Z ^ e * Z ^ (2 ^ n - 1)) ^ (2 ^ n) = 1 := by
    rw [← pow_add, ← pow_mul, mul_comm, pow_mul, hZ.pow_eq_one, one_pow]
  have hsub : Z ^ e * Z ^ (2 ^ n - 1) - 1 ∈ P := by
    have : Z ^ e * Z ^ (2 ^ n - 1) - 1 = (Z ^ e - Z) * Z ^ (2 ^ n - 1) := by
      linear_combination hZm
    rw [this]
    exact P.mul_mem_right _ h1
  have hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P := odd_natCast_not_mem r P _ (odd_two_pow_not_dvd r n hr hr2)
  have hone := odd_eq_one_of_sub_one_mem P hη hm hsub
  rw [← pow_add, hZ.pow_eq_one_iff_dvd] at hone
  have h2 : e + (2 ^ n - 1) ≡ 1 + (2 ^ n - 1) [MOD 2 ^ n] := by
    rw [Nat.add_sub_cancel' hm1]
    exact (Nat.modEq_zero_iff_dvd.mpr hone).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  have h3 : e ≡ 1 [MOD 2 ^ n] := Nat.ModEq.add_right_cancel' _ h2
  have h4 : (e : ZMod (2 ^ n)) = ((1 : ℕ) : ZMod (2 ^ n)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
  rw [he, ZMod.natCast_zmod_val, Nat.cast_one] at h4
  exact Units.ext (by rw [h4, Units.val_one])

/- English proof (translation)
Establish `hZ : IsPrimitiveRoot hζ.toInteger (2 ^ n)` using `hζ.toInteger_isPrimitiveRoot`. Establish `hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P` using `odd_natCast_not_mem p P _ (odd_two_pow_not_dvd p n Fact.out hp2)`. Establish `h₁` using `AlgHom.IsArithFrobAt.apply_of_pow_eq_one H hZ.pow_eq_one hm`. Rewrite `h₁` using `[odd_card_under p P]`. Establish `h₃ : hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val = hζ.toInteger ^ p`.

Rewrite using `[← odd_autToPow_smul hζ σ]`. Conclude with `h₁`. Rewrite `h₃` using `[(hZ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hZ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val]`. Conclude with `h₃`.
-/
theorem odd_cyc_frob {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) :
    ((hζ.autToPow ℚ σ : ZMod (2 ^ n))) = (p : ZMod (2 ^ n)) := by
  have hZ : IsPrimitiveRoot hζ.toInteger (2 ^ n) := hζ.toInteger_isPrimitiveRoot
  have hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P :=
    odd_natCast_not_mem p P _ (odd_two_pow_not_dvd p n Fact.out hp2)
  have h₁ := AlgHom.IsArithFrobAt.apply_of_pow_eq_one H hZ.pow_eq_one hm
  rw [odd_card_under p P] at h₁
  have h₃ : hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val = hζ.toInteger ^ p := by
    rw [← odd_autToPow_smul hζ σ]; exact h₁
  rw [(hZ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hZ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h₃
  exact h₃

/- English proof (translation)
Break down `Int.units_eq_one_or (sgn σ y) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Take `⟨Y, hYc, hY2⟩` from `odd_lift y _ hy`. Establish `hσY` using `odd_smul_lift σ y _ hy Y hYc`.

Rewrite `hσY` using `[h]`. Establish `h2Y : (2 : 𝓞 L) * Y ∈ P`. Use `P.neg_mem_iff.mpr (hσ Y)` as an intermediate fact. Rewrite `this` using `[hσY]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (2 : 𝓞 L) ∉ P`. Use `odd_natCast_not_mem r P 2 (fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd))` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hYP : Y ∈ P` using `((inferInstance : P.IsPrime).mem_or_mem h2Y).resolve_left h2`. Establish `hsP : ((-(s : ℤ) : ℤ) : 𝓞 L) ∈ P`. Rewrite using `[← hY2]`. Conclude with `P.pow_mem_of_mem hYP 2 (by norm_num)`. Rewrite `hsP` using `[odd_intCast_mem_iff r P, dvd_neg]`.

Conclude with `hrs (by exact_mod_cast hsP)`.
-/
theorem odd_sgn_inertia {L : Type} [Field L] [NumberField L] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L, σ • x - x ∈ P) (y : L) (s : ℕ)
    (hy : y ^ 2 = ((-(s : ℤ) : ℤ) : L)) (hrs : ¬ r ∣ s) : sgn σ y = 1 := by
  rcases Int.units_eq_one_or (sgn σ y) with h | h
  · exact h
  · exfalso
    obtain ⟨Y, hYc, hY2⟩ := odd_lift y _ hy
    have hσY := odd_smul_lift σ y _ hy Y hYc
    rw [h] at hσY
    have h2Y : (2 : 𝓞 L) * Y ∈ P := by
      have := P.neg_mem_iff.mpr (hσ Y)
      rw [hσY] at this
      convert this using 1
      push_cast
      ring
    have h2 : (2 : 𝓞 L) ∉ P := by
      have := odd_natCast_not_mem r P 2
        (fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd))
      exact_mod_cast this
    have hYP : Y ∈ P := ((inferInstance : P.IsPrime).mem_or_mem h2Y).resolve_left h2
    have hsP : ((-(s : ℤ) : ℤ) : 𝓞 L) ∈ P := by
      rw [← hY2]
      exact P.pow_mem_of_mem hYP 2 (by norm_num)
    rw [odd_intCast_mem_iff r P, dvd_neg] at hsP
    exact hrs (by exact_mod_cast hsP)

/- English proof (translation)
Establish `: IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ L`. Establish `: (span {(r : ℤ)}).IsPrime`. Rewrite using `[Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : r.Prime).ne_zero)]`. Conclude with `Nat.prime_iff_prime_int.mp Fact.out`. Rewrite using `[card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(r : ℤ)}) P, ramificationIdxIn_eq_ramificationIdx (span {(r : ℤ)}) P Gal(L/ℚ)]`.
-/
theorem odd_card (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (r : ℕ) [Fact r.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] :
    Nat.card (P.inertia Gal(L/ℚ)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : r.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(r : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(r : ℤ)}) P Gal(L/ℚ)]

/- English proof (translation)
Rewrite using `[← Ideal.ramificationIdx'_eq_ramificationIdx (span {(r : ℤ)}) P (by simpa using hr.ne_zero)]`. Establish `hmemq : ((r : ℤ) : 𝓞 L) ∈ P` using `(odd_intCast_mem_iff r P _).mpr dvd_rfl`. Establish `hmap : map (algebraMap ℤ (𝓞 L)) (span {(r : ℤ)}) = span {((r : ℤ) : 𝓞 L)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, eq_intCast]`. Rewrite using `[Ideal.ramificationIdx'_ne_one_iff (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq), hmap, Ideal.span_le, Set.singleton_subset_iff]`.

Take `⟨A, -, hA2⟩` from `odd_lift x _ hx`. Establish `hA2P : A ^ 2 ∈ P`. Rewrite using `[hA2, Int.cast_neg]`. Conclude with `P.neg_mem_iff.mpr hmemq`. Establish `hAP : A ∈ P` using `(inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P`.

Establish `: ((r : ℤ) : 𝓞 L) = -(A * A)`. Rewrite using `[← pow_two, hA2, Int.cast_neg, neg_neg]`. Use `show ((r : ℤ) : 𝓞 L) ∈ P ^ 2`. Rewrite using `[this, pow_two]`. Conclude with `(P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)`.
-/
theorem odd_ram_ne_one {L : Type} [Field L] [NumberField L] (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] (x : L)
    (hx : x ^ 2 = ((-(r : ℤ) : ℤ) : L)) :
    P.ramificationIdx ℤ ≠ 1 := by
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(r : ℤ)}) P (by simpa using hr.ne_zero)]
  have hmemq : ((r : ℤ) : 𝓞 L) ∈ P := (odd_intCast_mem_iff r P _).mpr dvd_rfl
  have hmap : map (algebraMap ℤ (𝓞 L)) (span {(r : ℤ)}) = span {((r : ℤ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [Ideal.ramificationIdx'_ne_one_iff
      (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq),
    hmap, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨A, -, hA2⟩ := odd_lift x _ hx
  have hA2P : A ^ 2 ∈ P := by
    rw [hA2, Int.cast_neg]
    exact P.neg_mem_iff.mpr hmemq
  have hAP : A ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P
  have : ((r : ℤ) : 𝓞 L) = -(A * A) := by
    rw [← pow_two, hA2, Int.cast_neg, neg_neg]
  show ((r : ℤ) : 𝓞 L) ∈ P ^ 2
  rw [this, pow_two]
  exact (P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `hbot : P.inertia Gal(L/ℚ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `τ hτ`. Rewrite using `[Subgroup.mem_bot]`.

Break down `hfwd τ hτ with h' | h'` into its components or cases. Conclude with `hinj (h'.trans h1.symm)`. Use `hinj (h'.trans hσ.symm)` as an intermediate fact. Substitute `this` using the available equality. Conclude with `absurd hτ hn`.

Establish `hc` using `odd_card L r P`. Rewrite `hc` using `[hbot, Subgroup.card_bot]`. Conclude with `hram hc.symm`.
-/
theorem odd_inertia_back {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {G : Type*} [One G]
    (f : Gal(L/ℚ) → G) (hinj : Function.Injective f) (h1 : f 1 = 1) (t : G)
    (r : ℕ) [Fact r.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) → f τ = 1 ∨ f τ = t)
    (hram : P.ramificationIdx ℤ ≠ 1) (σ : Gal(L/ℚ)) (hσ : f σ = t) :
    ∀ x : 𝓞 L, σ • x - x ∈ P := by
  by_contra hn
  have hbot : P.inertia Gal(L/ℚ) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    rcases hfwd τ hτ with h' | h'
    · exact hinj (h'.trans h1.symm)
    · have := hinj (h'.trans hσ.symm)
      subst this
      exact absurd hτ hn
  have hc := odd_card L r P
  rw [hbot, Subgroup.card_bot] at hc
  exact hram hc.symm

/- English proof (translation)
Unfold `Iq`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hg`. Break down `Int.units_eq_one_or ((((1, -1, 1) : GalL n) ^ k).2.1) with h | h` into its components or cases.

Use the proof step `left; exact Prod.ext (by simp) (Prod.ext h (by simp))`. Use the proof step `right; exact Prod.ext (by simp) (Prod.ext h (by simp))`. Introduce and unpack `(rfl | rfl)`. Conclude with `one_mem _`. Conclude with `Subgroup.mem_zpowers _`.
-/
theorem odd_mem_Iq (n : ℕ) (g : GalL n) : g ∈ Iq n ↔ g = 1 ∨ g = (1, -1, 1) := by
  unfold Iq
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.units_eq_one_or ((((1, -1, 1) : GalL n) ^ k).2.1) with h | h
    · left; exact Prod.ext (by simp) (Prod.ext h (by simp))
    · right; exact Prod.ext (by simp) (Prod.ext h (by simp))
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

/- English proof (translation)
Unfold `Id`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hg`. Break down `Int.units_eq_one_or ((((1, 1, -1) : GalL n) ^ k).2.2) with h | h` into its components or cases.

Use the proof step `left; exact Prod.ext (by simp) (Prod.ext (by simp) h)`. Use the proof step `right; exact Prod.ext (by simp) (Prod.ext (by simp) h)`. Introduce and unpack `(rfl | rfl)`. Conclude with `one_mem _`. Conclude with `Subgroup.mem_zpowers _`.
-/
theorem odd_mem_Id (n : ℕ) (g : GalL n) : g ∈ Id n ↔ g = 1 ∨ g = (1, 1, -1) := by
  unfold Id
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.units_eq_one_or ((((1, 1, -1) : GalL n) ^ k).2.2) with h | h
    · left; exact Prod.ext (by simp) (Prod.ext (by simp) h)
    · right; exact Prod.ext (by simp) (Prod.ext (by simp) h)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

/- English proof (translation)
Introduce `n q d hn hqd L _ _ ζ a b h`. Take `⟨hq, hd, hqd', hq2, hd2⟩` from `hqd`. Take `⟨hGal, -, -, hbij⟩` from `hG n q d hn ⟨hq, hd, hqd', hq2, hd2⟩ L ζ a b h`. Establish `: IsGalois ℚ L` using `hGal`. Establish `ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L)` using `by rw [h.2.1]; push_cast; rfl`.

Establish `hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L)` using `by rw [h.2.2.1]; push_cast; rfl`. Establish `h1 : galMap h.1 a b 1 = 1` using `by simp [galMap, sgn]`. Use `⟨fun P _ _ σ => ?_, fun P _ _ σ => ?_⟩` and prove the remaining obligations. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) → galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, -1, 1)`.

Introduce `τ hτ`. Establish `c1` using `odd_cyc_inertia h.1 q hq hq2 P τ hτ`. Establish `c3` using `odd_sgn_inertia q hq hq2 P τ hτ b d hb (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv))`. Break down `Int.units_eq_one_or (sgn τ a) with c2 | c2` into its components or cases. Use `left`.

Simplify using `only [galMap, c1, c2, c3]`. Both sides reduce to the same expression. Use `right`. Simplify using `only [galMap, c1, c2, c3]`. Rewrite using `[odd_mem_Iq]`.

Use `⟨hfwd σ, fun hσ => ?_⟩` and prove the remaining obligations. Break down `hσ with hσ | hσ` into its components or cases. Establish `: σ = 1` using `hbij.1 (hσ.trans h1.symm)`. Substitute `this` using the available equality. Introduce `x`.

Simplify using the standard rewrite rules. Conclude with `odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ q P hfwd (odd_ram_ne_one q hq P a ha) σ hσ`. Establish `: Fact d.Prime` using `⟨hd⟩`. Establish `hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) → galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, 1, -1)`. Introduce `τ hτ`.

Establish `c1` using `odd_cyc_inertia h.1 d hd hd2 P τ hτ`. Establish `c2` using `odd_sgn_inertia d hd hd2 P τ hτ a q ha (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm)`. Break down `Int.units_eq_one_or (sgn τ b) with c3 | c3` into its components or cases. Use `left`. Simplify using `only [galMap, c1, c2, c3]`.

Both sides reduce to the same expression. Use `right`. Simplify using `only [galMap, c1, c2, c3]`. Rewrite using `[odd_mem_Id]`. Use `⟨hfwd σ, fun hσ => ?_⟩` and prove the remaining obligations.

Break down `hσ with hσ | hσ` into its components or cases. Establish `: σ = 1` using `hbij.1 (hσ.trans h1.symm)`. Substitute `this` using the available equality. Introduce `x`. Simplify using the standard rewrite rules.

Conclude with `odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ d P hfwd (odd_ram_ne_one d hd P b hb) σ hσ`.
-/
theorem layerInertiaTame_of (hG : LayerGalois) : LayerInertiaTame := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hq, hd, hqd', hq2, hd2⟩ := hqd
  obtain ⟨hGal, -, -, hbij⟩ := hG n q d hn ⟨hq, hd, hqd', hq2, hd2⟩ L ζ a b h
  have : IsGalois ℚ L := hGal
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have h1 : galMap h.1 a b 1 = 1 := by simp [galMap, sgn]
  refine ⟨fun P _ _ σ => ?_, fun P _ _ σ => ?_⟩
  · have : Fact q.Prime := ⟨hq⟩
    have hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) →
        galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, -1, 1) := by
      intro τ hτ
      have c1 := odd_cyc_inertia h.1 q hq hq2 P τ hτ
      have c3 := odd_sgn_inertia q hq hq2 P τ hτ b d hb
        (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv))
      rcases Int.units_eq_one_or (sgn τ a) with c2 | c2
      · left; simp only [galMap, c1, c2, c3]; rfl
      · right; simp only [galMap, c1, c2, c3]
    rw [odd_mem_Iq]
    refine ⟨hfwd σ, fun hσ => ?_⟩
    rcases hσ with hσ | hσ
    · have : σ = 1 := hbij.1 (hσ.trans h1.symm)
      subst this
      intro x
      simp
    · exact odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ q P hfwd
        (odd_ram_ne_one q hq P a ha) σ hσ
  · have : Fact d.Prime := ⟨hd⟩
    have hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) →
        galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, 1, -1) := by
      intro τ hτ
      have c1 := odd_cyc_inertia h.1 d hd hd2 P τ hτ
      have c2 := odd_sgn_inertia d hd hd2 P τ hτ a q ha
        (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm)
      rcases Int.units_eq_one_or (sgn τ b) with c3 | c3
      · left; simp only [galMap, c1, c2, c3]; rfl
      · right; simp only [galMap, c1, c2, c3]
    rw [odd_mem_Id]
    refine ⟨hfwd σ, fun hσ => ?_⟩
    rcases hσ with hσ | hσ
    · have : σ = 1 := hbij.1 (hσ.trans h1.symm)
      subst this
      intro x
      simp
    · exact odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ d P hfwd
        (odd_ram_ne_one d hd P b hb) σ hσ

/- English proof (translation)
Introduce `n q d hn hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _`. Take `⟨hGal, -, -, hbij⟩` from `hG n q d hn hqd L ζ a b h`. Establish `: IsGalois ℚ L` using `hGal`. Establish `hp : p.Prime` using `Fact.out`. Establish `ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L)` using `by rw [h.2.1]; push_cast; rfl`.

Establish `hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L)` using `by rw [h.2.2.1]; push_cast; rfl`. Establish `hnq : ¬ (p : ℤ) ∣ -(q : ℤ)`. Rewrite using `[dvd_neg]`. Introduce `hd'`. Conclude with `hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))`.

Establish `hnd : ¬ (p : ℤ) ∣ -(d : ℤ)`. Rewrite using `[dvd_neg]`. Introduce `hd'`. Conclude with `hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))`. Establish `hval : ∀ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P → (((galMap h.1 a b σ).1 : ZMod (2 ^ n)) = (p : ZMod (2 ^ n)) ∧ (((galMap h.1 a b σ).2.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧ (((galMap h.1 a b σ).2.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p)` using `fun σ H => ⟨odd_cyc_frob h.1 p hp2 P σ H, odd_frob_sgn p hp2 P σ H a _ ha hnq, odd_frob_sgn p hp2 P σ H b _ hb hnd⟩`.

Establish `: Finite (𝓞 L ⧸ P)`. Establish `hpb : span {(p : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Conclude with `Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)`.

Take `⟨τ, hτ⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) P`. Use `⟨⟨τ, hτ⟩, fun σ => ⟨hval σ, fun hσ => ?_⟩⟩` and prove the remaining obligations. Establish `hτv` using `hval τ hτ`. Establish `: σ = τ` using `hbij.1 (Prod.ext (Units.ext (hσ.1.trans hτv.1.symm)) (Prod.ext (Units.ext (hσ.2.1.trans hτv.2.1.symm)) (Units.ext (hσ.2.2.trans hτv.2.2.symm))))`. Substitute `this` using the available equality.

Conclude with `hτ`.
-/
theorem layerFrob_of (hG : LayerGalois) : LayerFrob := by
  intro n q d hn hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _
  obtain ⟨hGal, -, -, hbij⟩ := hG n q d hn hqd L ζ a b h
  have : IsGalois ℚ L := hGal
  have hp : p.Prime := Fact.out
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hnq : ¬ (p : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]; intro hd'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))
  have hnd : ¬ (p : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg]; intro hd'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))
  have hval : ∀ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P →
      (((galMap h.1 a b σ).1 : ZMod (2 ^ n)) = (p : ZMod (2 ^ n)) ∧
        (((galMap h.1 a b σ).2.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galMap h.1 a b σ).2.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p) := fun σ H =>
    ⟨odd_cyc_frob h.1 p hp2 P σ H, odd_frob_sgn p hp2 P σ H a _ ha hnq,
      odd_frob_sgn p hp2 P σ H b _ hb hnd⟩
  have : Finite (𝓞 L ⧸ P) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) P
  refine ⟨⟨τ, hτ⟩, fun σ => ⟨hval σ, fun hσ => ?_⟩⟩
  have hτv := hval τ hτ
  have : σ = τ := hbij.1 (Prod.ext (Units.ext (hσ.1.trans hτv.1.symm))
    (Prod.ext (Units.ext (hσ.2.1.trans hτv.2.1.symm)) (Units.ext (hσ.2.2.trans hτv.2.2.symm))))
  subst this
  exact hτ

/- English proof (translation)
Introduce `N u hu1`. Use `set k := (u - 1).natAbs with hkdef`. Establish `hk : k ≠ 0`. Rewrite using `[hkdef]`. Introduce `h`.

Apply `hu1` to reduce the goal to its premises. Use `Int.natAbs_eq_zero.mp h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN : (2 ^ N : ℕ) ≠ 0` using `by positivity`. Establish `: NeZero (2 ^ N)` using `⟨hN⟩`.

Use `set c : ZMod (2 ^ N) := ((u - 1 : ℤ) : ZMod (2 ^ N)) with hc`. Set `f : ZMod (2 ^ N) →+ ZMod (2 ^ N)` to `AddMonoidHom.mulLeft c`. Establish `hcard : Nat.card {x : ZMod (2 ^ N) // c * x = 0} = Nat.card f.ker` using `Nat.card_congr (Equiv.subtypeEquivRight (fun x => (AddMonoidHom.mem_ker (f := f)).symm))`. Establish `hrange : f.range = AddSubgroup.zmultiples c`. Use extensionality with `y`.

Simplify using `only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Use `⟨(x.val : ℤ), ?_⟩` and prove the remaining obligations. Simplify using `only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨n, rfl⟩`. Use `⟨(n : ZMod (2 ^ N)), ?_⟩` and prove the remaining obligations. Simplify using `only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hord : addOrderOf c = 2 ^ N / Nat.gcd (2 ^ N) k`. Establish `: c = (k : ZMod (2 ^ N)) ∨ c = -(k : ZMod (2 ^ N))`. Break down `Int.natAbs_eq (u - 1) with h | h` into its components or cases. Use `left`. Rewrite using `[hc, h]`.

Simplify using `[hkdef]`. Use `right`. Rewrite using `[hc, h]`. Simplify using `[hkdef]`. Break down `this with h | h` into its components or cases.

Rewrite using `[h, ZMod.addOrderOf_coe _ hN]`. Rewrite using `[h, addOrderOf_neg, ZMod.addOrderOf_coe _ hN]`. Establish `hmul` using `AddSubgroup.card_mul_index f.ker`. Rewrite `hmul` using `[AddSubgroup.index_ker, hrange, Nat.card_zmultiples, hord, Nat.card_zmod]`. Establish `hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N` using `Nat.gcd_dvd_left _ _`.

Establish `hgpos : 0 < Nat.gcd (2 ^ N) k` using `Nat.gcd_pos_of_pos_left _ (by positivity)`. Establish `hd : Nat.gcd (2 ^ N) k * (2 ^ N / Nat.gcd (2 ^ N) k) = 2 ^ N` using `Nat.mul_div_cancel' hg`. Establish `hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k` using `Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos`. Establish `hker : Nat.card f.ker = Nat.gcd (2 ^ N) k` using `Nat.eq_of_mul_eq_mul_right hdpos (hmul.trans hd.symm)`. Rewrite using `[hcard, hker, gcd_two_pow N k hk]`.

Both sides reduce to the same expression.
-/
theorem invLength : InvLength := by
  intro N u hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have : NeZero (2 ^ N) := ⟨hN⟩
  set c : ZMod (2 ^ N) := ((u - 1 : ℤ) : ZMod (2 ^ N)) with hc
  let f : ZMod (2 ^ N) →+ ZMod (2 ^ N) := AddMonoidHom.mulLeft c
  have hcard : Nat.card {x : ZMod (2 ^ N) // c * x = 0} = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (AddMonoidHom.mem_ker (f := f)).symm))
  have hrange : f.range = AddSubgroup.zmultiples c := by
    ext y
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      simp only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      ring
    · rintro ⟨n, rfl⟩
      refine ⟨(n : ZMod (2 ^ N)), ?_⟩
      simp only [f, AddMonoidHom.coe_mulLeft, zsmul_eq_mul]
      ring
  have hord : addOrderOf c = 2 ^ N / Nat.gcd (2 ^ N) k := by
    have : c = (k : ZMod (2 ^ N)) ∨ c = -(k : ZMod (2 ^ N)) := by
      rcases Int.natAbs_eq (u - 1) with h | h
      · left; rw [hc, h]; simp [hkdef]
      · right; rw [hc, h]; simp [hkdef]
    rcases this with h | h
    · rw [h, ZMod.addOrderOf_coe _ hN]
    · rw [h, addOrderOf_neg, ZMod.addOrderOf_coe _ hN]
  have hmul := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, hrange, Nat.card_zmultiples, hord, Nat.card_zmod] at hmul
  have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hd : Nat.gcd (2 ^ N) k * (2 ^ N / Nat.gcd (2 ^ N) k) = 2 ^ N := Nat.mul_div_cancel' hg
  have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
  have hker : Nat.card f.ker = Nat.gcd (2 ^ N) k :=
    Nat.eq_of_mul_eq_mul_right hdpos (hmul.trans hd.symm)
  rw [hcard, hker, gcd_two_pow N k hk]
  rfl

end Formalism.TwoAdicCyclotomicDecomposition
