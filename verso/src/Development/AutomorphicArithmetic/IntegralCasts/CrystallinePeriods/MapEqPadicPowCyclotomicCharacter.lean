import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace Tilt

variable (p R) in

def seqEquiv : Perfection R p ≃* Tilt p R := Perfection.quotientMulEquiv p (span {(p : R)})

def seq (n : ℕ) : Tilt p R →* R :=
  (Perfection.coeffMonoidHom R p n).comp (seqEquiv p R).symm.toMonoidHom

def ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) : Tilt p R := seqEquiv p R ⟨x, h⟩

/- English proof (translation)
Conclude with `congrArg (Perfection.coeffMonoidHom R p n) ((seqEquiv p R).symm_apply_apply ⟨x, h⟩)`.
-/
@[simp] theorem seq_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) (n : ℕ) :
    seq n (ofSeq x h : Tilt p R) = x n := by
  exact congrArg (Perfection.coeffMonoidHom R p n) ((seqEquiv p R).symm_apply_apply ⟨x, h⟩)

/- English proof (translation)
The claim follows from `Perfection.coeff_zero_symm_quotientMulEquiv y`.
-/
theorem seq_zero (y : Tilt p R) : seq 0 y = PreTilt.untilt y :=
  Perfection.coeff_zero_symm_quotientMulEquiv y

/- English proof (translation)
Rewrite using `[← seq_zero, seq_ofSeq]`.
-/
@[simp] theorem untilt_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) :
    PreTilt.untilt (ofSeq x h : Tilt p R) = x 0 := by
  rw [← seq_zero, seq_ofSeq]

/- English proof (translation)
The claim follows from `Perfection.coeffMonoidHom_pow_p' ((seqEquiv p R).symm y) n`.
-/
theorem seq_succ_pow (y : Tilt p R) (n : ℕ) : seq (n + 1) y ^ p = seq n y :=
  Perfection.coeffMonoidHom_pow_p' ((seqEquiv p R).symm y) n

/- English proof (translation)
The claim follows from `Perfection.coeffMonoidHom_pow_p_pow' ((seqEquiv p R).symm y) m n`.
-/
theorem seq_add_pow (y : Tilt p R) (m n : ℕ) : seq (m + n) y ^ p ^ n = seq m y :=
  Perfection.coeffMonoidHom_pow_p_pow' ((seqEquiv p R).symm y) m n

/- English proof (translation)
Rewrite using `[← seq_zero, ← seq_add_pow y 0 n, zero_add]`.
-/
theorem seq_pow_self (y : Tilt p R) (n : ℕ) : seq n y ^ p ^ n = PreTilt.untilt y := by
  rw [← seq_zero, ← seq_add_pow y 0 n, zero_add]

/- English proof (translation)
The claim follows from `(seqEquiv p R).symm.injective (Perfection.extMonoid h)`.
-/
theorem ext_seq {x y : Tilt p R} (h : ∀ n, seq n x = seq n y) : x = y :=
  (seqEquiv p R).symm.injective (Perfection.extMonoid h)

/- English proof (translation)
The claim follows from `ext_seq fun n => seq_ofSeq _ _ n`.
-/
theorem ofSeq_seq (y : Tilt p R) : ofSeq (fun n => seq n y) (seq_succ_pow y) = y :=
  ext_seq fun n => seq_ofSeq _ _ n

/- English proof (translation)
Take `⟨z, rfl⟩` from `(seqEquiv p R).surjective y`. Simplify using `only [seq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem mk_seq (y : Tilt p R) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : R)}) (seq n y) = PreTilt.coeff n y := by
  obtain ⟨z, rfl⟩ := (seqEquiv p R).surjective y
  simp only [seq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Use `conv_rhs => rw [← frobeniusEquiv_symm_pow_p (Tilt p R) p y, map_pow, seq_succ_pow]`.
-/
theorem seq_frobeniusEquiv_symm (y : Tilt p R) (n : ℕ) :
    seq n ((frobeniusEquiv (Tilt p R) p).symm y) = seq (n + 1) y := by
  conv_rhs => rw [← frobeniusEquiv_symm_pow_p (Tilt p R) p y, map_pow, seq_succ_pow]

/- English proof (translation)
Proceed by induction on `n generalizing y with`. Consider the case `zero => exact seq_zero y`. Consider the case `succ n ih => rw [Function.iterate_succ_apply, ← ih, seq_frobeniusEquiv_symm]`.
-/
theorem seq_eq_untilt (y : Tilt p R) (n : ℕ) :
    seq n y = PreTilt.untilt (((frobeniusEquiv (Tilt p R) p).symm)^[n] y) := by
  induction n generalizing y with
  | zero => exact seq_zero y
  | succ n ih => rw [Function.iterate_succ_apply, ← ih, seq_frobeniusEquiv_symm]

/- English proof (translation)
Establish `: map p f y = ofSeq (fun n => f (seq n y)) (fun n => by rw [← map_pow, seq_succ_pow])`. Use `ext fun n => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, ← mk_seq, ← mk_seq, seq_ofSeq]`. Both sides reduce to the same expression. Rewrite using `[this, seq_ofSeq]`.
-/
theorem seq_map (f : R →+* S) (y : Tilt p R) (n : ℕ) : seq n (map p f y) = f (seq n y) := by
  have : map p f y = ofSeq (fun n => f (seq n y)) (fun n => by rw [← map_pow, seq_succ_pow]) := by
    refine ext fun n => ?_
    rw [coeff_map, ← mk_seq, ← mk_seq, seq_ofSeq]
    rfl
  rw [this, seq_ofSeq]

end Tilt

namespace tateModule

open Tilt

/- English proof (translation)
The claim follows from `η.2`.
-/
theorem untilt_eq_one (η : tateModule p R) : PreTilt.untilt η.1 = 1 := η.2

/- English proof (translation)
Rewrite using `[seq_pow_self, untilt_eq_one]`.
-/
theorem seq_pow_eq_one (η : tateModule p R) (n : ℕ) : seq n η.1 ^ p ^ n = 1 := by
  rw [seq_pow_self, untilt_eq_one]

/- English proof (translation)
The claim follows from `Subtype.ext (Tilt.ext_seq h)`.
-/
theorem ext_seq {x y : tateModule p R} (h : ∀ n, seq n x.1 = seq n y.1) : x = y :=
  Subtype.ext (Tilt.ext_seq h)

/- English proof (translation)
The claim follows from `pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (seq_pow_eq_one η n)`.
-/
theorem seq_pow_congr (η : tateModule p R) {n a b : ℕ} (h : (a : ZMod (p ^ n)) = b) :
    seq n η.1 ^ a = seq n η.1 ^ b :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (seq_pow_eq_one η n)

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
/- English proof (translation)
The claim follows from `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩ ZMod.natCast_zmod_val _`.
-/
theorem cast_val_toZModPow (a : ℤ_[p]) (n : ℕ) :
    (((PadicInt.toZModPow n a).val : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n a :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _

def padicPow (η : tateModule p R) (a : ℤ_[p]) : tateModule p R :=
  ⟨ofSeq (fun n => seq n η.1 ^ (PadicInt.toZModPow n a).val) (fun n => by
    rw [← pow_mul, mul_comm, pow_mul, seq_succ_pow]
    apply seq_pow_congr
    haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [cast_val_toZModPow, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ n.le_succ]), by
    change PreTilt.untilt _ = 1
    rw [untilt_ofSeq, seq_zero, untilt_eq_one, one_pow]⟩

/- English proof (translation)
The claim follows from `seq_ofSeq _ _ n`.
-/
theorem seq_padicPow (η : tateModule p R) (a : ℤ_[p]) (n : ℕ) :
    seq n (padicPow η a).1 = seq n η.1 ^ (PadicInt.toZModPow n a).val := seq_ofSeq _ _ n

/- English proof (translation)
Rewrite using `[seq_padicPow]`. Conclude with `seq_pow_congr η (by rw [cast_val_toZModPow, h])`.
-/
theorem seq_padicPow_of_eq (η : tateModule p R) {a : ℤ_[p]} {n m : ℕ}
    (h : PadicInt.toZModPow n a = m) : seq n (padicPow η a).1 = seq n η.1 ^ m := by
  rw [seq_padicPow]
  exact seq_pow_congr η (by rw [cast_val_toZModPow, h])

/- English proof (translation)
The claim follows from `ext_seq fun n => by rw [seq_padicPow_of_eq η (map_natCast _ m), SubmonoidClass.coe_pow, map_pow]`.
-/
@[simp] theorem padicPow_natCast (η : tateModule p R) (m : ℕ) : padicPow η m = η ^ m :=
  ext_seq fun n => by
    rw [seq_padicPow_of_eq η (map_natCast _ m), SubmonoidClass.coe_pow, map_pow]

/- English proof (translation)
Simplify using `using padicPow_natCast η 0`.
-/
@[simp] theorem padicPow_zero (η : tateModule p R) : padicPow η 0 = 1 := by
  simpa using padicPow_natCast η 0

/- English proof (translation)
Simplify using `using padicPow_natCast η 1`.
-/
@[simp] theorem padicPow_one (η : tateModule p R) : padicPow η 1 = η := by
  simpa using padicPow_natCast η 1

/- English proof (translation)
The claim follows from `ext_seq fun n => by rw [Submonoid.coe_mul, map_mul, seq_padicPow η a, seq_padicPow η b, ← pow_add] apply seq_padicPow_of_eq rw [Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow, map_add]`.
-/
theorem padicPow_add (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a + b) = padicPow η a * padicPow η b :=
  ext_seq fun n => by
    rw [Submonoid.coe_mul, map_mul, seq_padicPow η a, seq_padicPow η b, ← pow_add]
    apply seq_padicPow_of_eq
    rw [Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow, map_add]

/- English proof (translation)
The claim follows from `ext_seq fun n => by rw [seq_padicPow _ b, seq_padicPow η a, ← pow_mul] apply seq_padicPow_of_eq rw [Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow, map_mul]`.
-/
theorem padicPow_mul (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a * b) = padicPow (padicPow η a) b :=
  ext_seq fun n => by
    rw [seq_padicPow _ b, seq_padicPow η a, ← pow_mul]
    apply seq_padicPow_of_eq
    rw [Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow, map_mul]

/- English proof (translation)
The claim follows from `ext_seq fun n => by simp only [Submonoid.coe_mul, map_mul, seq_padicPow, mul_pow]`.
-/
theorem mul_padicPow (η η' : tateModule p R) (a : ℤ_[p]) :
    padicPow (η * η') a = padicPow η a * padicPow η' a :=
  ext_seq fun n => by
    simp only [Submonoid.coe_mul, map_mul, seq_padicPow, mul_pow]

/- English proof (translation)
The claim follows from `ext_seq fun n => by simp [seq_padicPow]`.
-/
@[simp] theorem one_padicPow (a : ℤ_[p]) : padicPow (1 : tateModule p R) a = 1 :=
  ext_seq fun n => by simp [seq_padicPow]

instance : CommGroup (tateModule p R) :=
  { (inferInstance : CommMonoid (tateModule p R)) with
    inv := fun η => padicPow η (-1)
    inv_mul_cancel := fun η => by
      conv_lhs => rw [← padicPow_one η, ← padicPow_mul, ← padicPow_add]
      simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inv_eq_padicPow (η : tateModule p R) : η⁻¹ = padicPow η (-1) := rfl

instance : Module ℤ_[p] (Additive (tateModule p R)) where
  smul a η := Additive.ofMul (padicPow η.toMul a)
  one_smul η := padicPow_one _
  mul_smul a b η := by
    change Additive.ofMul (padicPow η.toMul (a * b)) = _
    rw [mul_comm, padicPow_mul]; rfl
  smul_zero a := one_padicPow a
  smul_add a η η' := mul_padicPow _ _ a
  add_smul a b η := padicPow_add _ a b
  zero_smul η := padicPow_zero _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_ofMul (a : ℤ_[p]) (η : tateModule p R) :
    a • Additive.ofMul η = Additive.ofMul (padicPow η a) := rfl

/- English proof (translation)
Take `⟨b, hb⟩` from `h`. Use `⟨padicPow η b, ?_⟩` and prove the remaining obligations. Rewrite using `[← padicPow_natCast, ← padicPow_natCast, ← padicPow_mul, ← padicPow_add]`. Use `congr 1`. Use `push_cast`.

Take the linear combination `hb`.
-/
theorem exists_padicPow_eq (η : tateModule p R) {a : ℤ_[p]} {m k : ℕ}
    (h : (p : ℤ_[p]) ^ k ∣ a - m) : ∃ η' : tateModule p R, padicPow η a = η ^ m * η' ^ p ^ k := by
  obtain ⟨b, hb⟩ := h
  refine ⟨padicPow η b, ?_⟩
  rw [← padicPow_natCast, ← padicPow_natCast, ← padicPow_mul, ← padicPow_add]
  congr 1
  push_cast
  linear_combination hb

/- English proof (translation)
The claim follows from `Tilt.ext_seq fun n => by rw [seq_map, seq_padicPow, seq_padicPow, map_pow, ← seq_map, h]`.
-/
theorem map_padicPow (f : R →+* S) (η : tateModule p R) (η' : tateModule p S)
    (h : Tilt.map p f η.1 = η'.1) (a : ℤ_[p]) :
    Tilt.map p f (padicPow η a).1 = (padicPow η' a).1 :=
  Tilt.ext_seq fun n => by rw [seq_map, seq_padicPow, seq_padicPow, map_pow, ← seq_map, h]

end tateModule

open Tilt tateModule

/- English proof (translation)
Rewrite using `[IsPrimitive, ← seq_zero, seq_frobeniusEquiv_symm]`.
-/
theorem isPrimitive_iff (ε : tateModule p R) : IsPrimitive ε ↔ seq 1 ε.1 ≠ 1 := by
  rw [IsPrimitive, ← seq_zero, seq_frobeniusEquiv_symm]

/- English proof (translation)
Break down `n with _ | n` into its components or cases. Rewrite using `[seq_zero, untilt_eq_one, pow_zero]`. Conclude with `IsPrimitiveRoot.one`. Rewrite using `[← orderOf_eq_prime_pow (x := seq (n + 1) ε.1) _ (seq_pow_eq_one ε _)]`. Conclude with `IsPrimitiveRoot.orderOf _`.

Rewrite using `[add_comm, seq_add_pow]`. Conclude with `(isPrimitive_iff ε).1 hε`.
-/
theorem IsPrimitive.isPrimitiveRoot {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    IsPrimitiveRoot (seq n ε.1) (p ^ n) := by
  rcases n with _ | n
  · rw [seq_zero, untilt_eq_one, pow_zero]; exact IsPrimitiveRoot.one
  · rw [← orderOf_eq_prime_pow (x := seq (n + 1) ε.1) _ (seq_pow_eq_one ε _)]
    · exact IsPrimitiveRoot.orderOf _
    · rw [add_comm, seq_add_pow]; exact (isPrimitive_iff ε).1 hε

/- English proof (translation)
Introduce `a b h`. Use `PadicInt.ext_of_toZModPow.1 fun n => ?_` and prove the remaining obligations. Use `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Apply `ZMod.val_injective` to reduce the goal to its premises. Apply `(hε.isPrimitiveRoot n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)` to reduce the goal to its premises.

Rewrite using `[← seq_padicPow, ← seq_padicPow, h]`.
-/
theorem IsPrimitive.padicPow_injective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Injective (padicPow ε) := by
  intro a b h
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply ZMod.val_injective
  apply (hε.isPrimitiveRoot n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← seq_padicPow, ← seq_padicPow, h]

/- English proof (translation)
Use `haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Rewrite using `[isPrimitive_iff, seq_padicPow, Ne, (hε.isPrimitiveRoot 1).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, cast_val_toZModPow, ← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`.
-/
theorem IsPrimitive.padicPow_iff {ε : tateModule p R} (hε : IsPrimitive ε) (a : ℤ_[p]) :
    IsPrimitive (padicPow ε a) ↔ IsUnit a := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [isPrimitive_iff, seq_padicPow, Ne, (hε.isPrimitiveRoot 1).pow_eq_one_iff_dvd,
    ← ZMod.natCast_eq_zero_iff, cast_val_toZModPow, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

section Domain

variable [IsDomain R]

/- English proof (translation)
Introduce `η`. Establish `h : ∀ n, ∃ i : ℕ, seq n ε.1 ^ i = seq n η.1` using `fun n => by haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩`. Take `⟨i, -, hi⟩` from `(hε.isPrimitiveRoot n).eq_pow_of_pow_eq_one (seq_pow_eq_one η n)`. Conclude with `⟨i, hi⟩`. Use `choose i hi using h`.

Establish `hd : ∀ n, (p : ℤ) ^ n ∣ (i (n + 1) : ℤ) - i n` using `fun n => by`. Establish `h1 : seq n ε.1 ^ i n = seq n ε.1 ^ i (n + 1)`. Rewrite using `[hi, ← seq_succ_pow η.1, ← hi, ← seq_succ_pow ε.1 n, ← pow_mul, ← pow_mul, mul_comm]`. Establish `hf : IsOfFinOrder (seq n ε.1)` using `(hε.isPrimitiveRoot n).isOfFinOrder (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)`. Rewrite `h1` using `[hf.pow_eq_pow_iff_modEq, ← (hε.isPrimitiveRoot n).eq_orderOf]`.

Conclude with `h1.dvd` after adjusting the coercions. Use `⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (i n : ℤ)) p hd), tateModule.ext_seq fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← hi]`. Apply `seq_padicPow_of_eq` to reduce the goal to its premises. Rewrite using `[PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hd]`.

Simplify using the standard rewrite rules.
-/
theorem IsPrimitive.padicPow_surjective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Surjective (padicPow ε) := by
  intro η
  have h : ∀ n, ∃ i : ℕ, seq n ε.1 ^ i = seq n η.1 := fun n => by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := (hε.isPrimitiveRoot n).eq_pow_of_pow_eq_one (seq_pow_eq_one η n)
    exact ⟨i, hi⟩
  choose i hi using h
  have hd : ∀ n, (p : ℤ) ^ n ∣ (i (n + 1) : ℤ) - i n := fun n => by
    have h1 : seq n ε.1 ^ i n = seq n ε.1 ^ i (n + 1) := by
      rw [hi, ← seq_succ_pow η.1, ← hi, ← seq_succ_pow ε.1 n, ← pow_mul, ← pow_mul, mul_comm]
    have hf : IsOfFinOrder (seq n ε.1) :=
      (hε.isPrimitiveRoot n).isOfFinOrder (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hε.isPrimitiveRoot n).eq_orderOf] at h1
    exact_mod_cast h1.dvd
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => (i n : ℤ)) p hd), tateModule.ext_seq fun n => ?_⟩
  rw [← hi]
  apply seq_padicPow_of_eq
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hd]
  simp

def IsPrimitive.padicPowEquiv {ε : tateModule p R} (hε : IsPrimitive ε) :
    Multiplicative ℤ_[p] ≃* tateModule p R :=
  MulEquiv.ofBijective
    ({ toFun := fun a => padicPow ε a.toAdd
       map_one' := padicPow_zero ε
       map_mul' := fun a b => padicPow_add ε a.toAdd b.toAdd } :
      Multiplicative ℤ_[p] →* tateModule p R)
    ⟨fun _ _ h => hε.padicPow_injective h, fun η => hε.padicPow_surjective η⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem IsPrimitive.padicPowEquiv_apply {ε : tateModule p R} (hε : IsPrimitive ε)
    (a : ℤ_[p]) : hε.padicPowEquiv (Multiplicative.ofAdd a) = padicPow ε a := rfl

def IsPrimitive.linearEquiv {ε : tateModule p R} (hε : IsPrimitive ε) :
    ℤ_[p] ≃ₗ[ℤ_[p]] Additive (tateModule p R) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ (Additive.ofMul ε))
    ⟨fun _ _ h => hε.padicPow_injective h, fun η => hε.padicPow_surjective η.toMul⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hε.padicPow_surjective ε'`. Take `⟨a, rfl⟩` from `(hε.padicPow_iff a).1 hε'`. Conclude with `⟨a, rfl⟩`.
-/
theorem IsPrimitive.exists_unit {ε ε' : tateModule p R} (hε : IsPrimitive ε)
    (hε' : IsPrimitive ε') : ∃ a : ℤ_[p]ˣ, ε' = padicPow ε a := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective ε'
  obtain ⟨a, rfl⟩ := (hε.padicPow_iff a).1 hε'
  exact ⟨a, rfl⟩

/- English proof (translation)
The claim follows from `haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩ ⟨⟨_, hε.isPrimitiveRoot n⟩, rootsOfUnity.isCyclic _ _⟩`.
-/
theorem IsPrimitive.hasEnoughRootsOfUnity {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    HasEnoughRootsOfUnity R (p ^ n) :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ⟨⟨_, hε.isPrimitiveRoot n⟩, rootsOfUnity.isCyclic _ _⟩

end Domain

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
/- English proof (translation)
Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) x) hn`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn (x := z) (by rw [hz]; exact isIntegral_algebraMap)`. Conclude with `⟨y, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩`.
-/
theorem exists_pow_eq (x : R) {n : ℕ} (hn : 0 < n) : ∃ y : R, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) x) hn
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (x := z) (by rw [hz]; exact isIntegral_algebraMap)
  exact ⟨y, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩

/- English proof (translation)
Establish `h0 : ∀ x : R, ∃ y : Tilt p R, seq 0 y = x` using `fun x => by choose r hr using fun z : R => exists_pow_eq z (Fact.out : p.Prime).pos`. Conclude with `⟨ofSeq (fun n => r^[n] x) (fun n => by rw [Function.iterate_succ_apply', hr]), seq_ofSeq _ _ 0⟩`. Introduce `x`. Take `⟨y, hy⟩` from `h0 x`. Conclude with `⟨y ^ p ^ n, by rw [map_pow, ← hy, ← seq_add_pow y 0 n, zero_add]⟩`.
-/
theorem Tilt.seq_surjective (n : ℕ) : Function.Surjective (seq n : Tilt p R → R) := by
  have h0 : ∀ x : R, ∃ y : Tilt p R, seq 0 y = x := fun x => by
    choose r hr using fun z : R => exists_pow_eq z (Fact.out : p.Prime).pos
    exact ⟨ofSeq (fun n => r^[n] x) (fun n => by rw [Function.iterate_succ_apply', hr]),
      seq_ofSeq _ _ 0⟩
  intro x
  obtain ⟨y, hy⟩ := h0 x
  exact ⟨y ^ p ^ n, by rw [map_pow, ← hy, ← seq_add_pow y 0 n, zero_add]⟩

/- English proof (translation)
Introduce `x` and use `by obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 0 x exact ⟨y, by rw [← seq_zero, hy]⟩`.
-/
theorem Tilt.untilt_surjective_of_isAlgClosed : Function.Surjective (PreTilt.untilt : Tilt p R → R) := fun x => by
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 0 x
  exact ⟨y, by rw [← seq_zero, hy]⟩

instance : Nonempty (PFlat p R) :=
  let ⟨y, hy⟩ := Tilt.untilt_surjective_of_isAlgClosed (p := p) (p : R)
  ⟨⟨y, hy⟩⟩

variable (p R) in

def pflat : PFlat p R := Classical.arbitrary _

variable [CharZero R]

variable (p R) in
/- English proof (translation)
Use `haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R`. Use `haveI : NeZero (p : FractionRing R) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing R) p`. Take `⟨z, rfl⟩` from `IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (Fact.out : p.Prime).pos (x := ζ) (by rw [hζ.pow_eq_one]; exact isIntegral_one)`. Establish `hz` using `hζ.of_map_of_injective (IsFractionRing.injective R (FractionRing R))`.

Take `⟨y, hy⟩` from `Tilt.seq_surjective (p := p) 1 z`. Use `⟨⟨y, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.untilt y = 1`. Rewrite using `[← seq_zero, ← seq_succ_pow, zero_add, hy, hz.pow_eq_one]`. Rewrite using `[isPrimitive_iff]`.

Express the relevant statement in the definitionally equal form `seq 1 y ≠ 1`. Rewrite using `[hy]`. Conclude with `hz.ne_one (Fact.out : p.Prime).one_lt`.
-/
theorem exists_isPrimitive : ∃ ε : tateModule p R, IsPrimitive ε := by
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : NeZero (p : FractionRing R) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing R) p
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (Fact.out : p.Prime).pos (x := ζ) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hz := hζ.of_map_of_injective (IsFractionRing.injective R (FractionRing R))
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 1 z
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change PreTilt.untilt y = 1
    rw [← seq_zero, ← seq_succ_pow, zero_add, hy, hz.pow_eq_one]
  · rw [isPrimitive_iff]
    change seq 1 y ≠ 1
    rw [hy]
    exact hz.ne_one (Fact.out : p.Prime).one_lt

variable (p R) in

def eps : tateModule p R := (exists_isPrimitive p R).choose

variable (p R) in
/- English proof (translation)
The claim follows from `(exists_isPrimitive p R).choose_spec`.
-/
theorem isPrimitive_eps : IsPrimitive (eps p R) := (exists_isPrimitive p R).choose_spec

/- English proof (translation)
Use `haveI := (isPrimitive_eps p R).hasEnoughRootsOfUnity`. Use `Tilt.ext_seq fun n => ?_` and prove the remaining obligations. Rewrite using `[seq_map, seq_padicPow]`. Conclude with `cyclotomicCharacter.spec p e _ (seq_pow_eq_one η n)`.
-/
theorem tateModule.map_eq_padicPow_cyclotomicCharacter (e : R ≃+* R) (η : tateModule p R) :
    Tilt.map p (e : R →+* R) η.1 = (padicPow η (cyclotomicCharacter R p e)).1 := by
  haveI := (isPrimitive_eps p R).hasEnoughRootsOfUnity
  refine Tilt.ext_seq fun n => ?_
  rw [seq_map, seq_padicPow]
  exact cyclotomicCharacter.spec p e _ (seq_pow_eq_one η n)

end Good

namespace PFlat

/- English proof (translation)
The claim follows from `Subtype.ext h`.
-/
theorem ext {ϖ ϖ' : PFlat p R} (h : ϖ.1 = ϖ'.1) : ϖ = ϖ' := Subtype.ext h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem twist_val (η : tateModule p R) (ϖ : PFlat p R) : (ϖ.twist η).1 = η.1 * ϖ.1 := rfl

/- English proof (translation)
The claim follows from `ext (one_mul _)`.
-/
@[simp] theorem twist_one (ϖ : PFlat p R) : ϖ.twist 1 = ϖ := ext (one_mul _)

/- English proof (translation)
The claim follows from `ext (mul_assoc _ _ _).symm`.
-/
theorem twist_twist (η η' : tateModule p R) (ϖ : PFlat p R) :
    (ϖ.twist η').twist η = ϖ.twist (η * η') := ext (mul_assoc _ _ _).symm

/- English proof (translation)
Rewrite using `[seq_pow_self, ϖ.2]`.
-/
theorem seq_pow (ϖ : PFlat p R) (n : ℕ) : seq n ϖ.1 ^ p ^ n = (p : R) := by
  rw [seq_pow_self, ϖ.2]

variable [IsDomain R] [CharZero R]

/- English proof (translation)
Introduce `h` and use `by have := seq_pow ϖ n rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this.symm)`.
-/
theorem seq_ne_zero (ϖ : PFlat p R) (n : ℕ) : seq n ϖ.1 ≠ 0 := fun h => by
  have := seq_pow ϖ n
  rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this.symm)

/- English proof (translation)
Introduce `η η' h`. Use `tateModule.ext_seq fun n => mul_right_cancel₀ (seq_ne_zero ϖ n) ?_` and prove the remaining obligations. Establish `h1 : η.1 * ϖ.1 = η'.1 * ϖ.1`. Rewrite using `[← twist_val, ← twist_val]`. Conclude with `congrArg Subtype.val h`.

Rewrite using `[← map_mul, ← map_mul, h1]`.
-/
theorem twist_injective (ϖ : PFlat p R) : Function.Injective fun η => ϖ.twist η := by
  intro η η' h
  refine tateModule.ext_seq fun n => mul_right_cancel₀ (seq_ne_zero ϖ n) ?_
  have h1 : η.1 * ϖ.1 = η'.1 * ϖ.1 := by
    rw [← twist_val, ← twist_val]
    exact congrArg Subtype.val h
  rw [← map_mul, ← map_mul, h1]

variable [ValuationRing R]

/- English proof (translation)
Introduce `ϖ'`. Establish `hd : ∀ n, seq n ϖ.1 ∣ seq n ϖ'.1` using `fun n => by`. Rewrite using `[← IsIntegrallyClosed.pow_dvd_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero), seq_pow, seq_pow]`. Use `choose c hc using hd`. Establish `hp : ∀ n, c (n + 1) ^ p = c n` using `fun n => by`.

Apply `mul_left_cancel₀ (seq_ne_zero ϖ n)` to reduce the goal to its premises. Rewrite using `[← hc, ← seq_succ_pow ϖ.1, ← mul_pow, ← hc, seq_succ_pow]`. Use `⟨⟨ofSeq c hp, ?_⟩, ext (Tilt.ext_seq fun n => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.untilt _ = 1`. Rewrite using `[untilt_ofSeq]`.

Apply `mul_left_cancel₀ (seq_ne_zero ϖ 0)` to reduce the goal to its premises. Rewrite using `[← hc, mul_one, seq_zero, seq_zero, ϖ.2, ϖ'.2]`. Express the relevant statement in the definitionally equal form `seq n (ofSeq c hp * ϖ.1) = _`. Rewrite using `[map_mul, seq_ofSeq, hc, mul_comm]`.
-/
theorem twist_surjective (ϖ : PFlat p R) : Function.Surjective fun η => ϖ.twist η := by
  intro ϖ'
  have hd : ∀ n, seq n ϖ.1 ∣ seq n ϖ'.1 := fun n => by
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero),
      seq_pow, seq_pow]
  choose c hc using hd
  have hp : ∀ n, c (n + 1) ^ p = c n := fun n => by
    apply mul_left_cancel₀ (seq_ne_zero ϖ n)
    rw [← hc, ← seq_succ_pow ϖ.1, ← mul_pow, ← hc, seq_succ_pow]
  refine ⟨⟨ofSeq c hp, ?_⟩, ext (Tilt.ext_seq fun n => ?_)⟩
  · change PreTilt.untilt _ = 1
    rw [untilt_ofSeq]
    apply mul_left_cancel₀ (seq_ne_zero ϖ 0)
    rw [← hc, mul_one, seq_zero, seq_zero, ϖ.2, ϖ'.2]
  · change seq n (ofSeq c hp * ϖ.1) = _
    rw [map_mul, seq_ofSeq, hc, mul_comm]

/- English proof (translation)
Take `⟨η, hη⟩` from `twist_surjective ϖ ϖ'`. Conclude with `⟨η, hη.symm, fun η' h => twist_injective ϖ (h.symm.trans hη.symm)⟩`.
-/
theorem existsUnique_twist (ϖ ϖ' : PFlat p R) : ∃! η : tateModule p R, ϖ' = ϖ.twist η := by
  obtain ⟨η, hη⟩ := twist_surjective ϖ ϖ'
  exact ⟨η, hη.symm, fun η' h => twist_injective ϖ (h.symm.trans hη.symm)⟩

def div (ϖ' ϖ : PFlat p R) : tateModule p R := (twist_surjective ϖ ϖ').choose

/- English proof (translation)
The claim follows from `(twist_surjective ϖ ϖ').choose_spec`.
-/
@[simp] theorem twist_div (ϖ' ϖ : PFlat p R) : ϖ.twist (ϖ'.div ϖ) = ϖ' :=
  (twist_surjective ϖ ϖ').choose_spec

/- English proof (translation)
The claim follows from `twist_injective ϖ (twist_div _ _)`.
-/
@[simp] theorem twist_div_self (η : tateModule p R) (ϖ : PFlat p R) : (ϖ.twist η).div ϖ = η :=
  twist_injective ϖ (twist_div _ _)

/- English proof (translation)
Simplify using `using twist_div_self 1 ϖ`.
-/
@[simp] theorem div_self (ϖ : PFlat p R) : ϖ.div ϖ = 1 := by
  simpa using twist_div_self 1 ϖ

/- English proof (translation)
Use `conv_lhs => rw [← twist_div ϖ' ϖ, twist_twist, twist_div_self]`.
-/
theorem twist_div_eq (η : tateModule p R) (ϖ' ϖ : PFlat p R) :
    (ϖ'.twist η).div ϖ = η * ϖ'.div ϖ := by
  conv_lhs => rw [← twist_div ϖ' ϖ, twist_twist, twist_div_self]

end PFlat

end Reformulated.AutPerF
