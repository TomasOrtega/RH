import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

section Adic

variable {A : Type u} [CommRing A]

/- English proof (translation)
Establish `hfg : I.FG` using `hI ▸ Submodule.fg_span_singleton a`. Establish `h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]`.

Introduce `h`. Rewrite using `[← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]`. Rewrite using `[h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]`. Establish `h2 : I ^ n = span {a ^ n}` using `by rw [hI, Ideal.span_singleton_pow]`. Rewrite using `[h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, by rw [Algebra.smul_def, map_pow]⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩`.
-/
theorem evalₐ_eq_zero_iff_dvd_of_eq_span {I : Ideal A} {a : A} (hI : I = span {a}) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ algebraMap A (AdicCompletion I A) a ^ n ∣ x := by
  have hfg : I.FG := hI ▸ Submodule.fg_span_singleton a
  have h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
    constructor
    · intro h
      rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
    · intro h
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]
  rw [h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  have h2 : I ^ n = span {a ^ n} := by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩

/- English proof (translation)
Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)`. Establish `h1` using `congrArg (AdicCompletion.evalₐ I (n + 1)) h`. Rewrite `h1` using `[map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h2 : ∀ m, I ^ m = span {a ^ m}` using `fun m => by rw [hI, Ideal.span_singleton_pow]`.

Rewrite `h1` using `[h2, mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha]`. Rewrite using `[← factorPow_evalₐ I n.le_succ, ← hy, map_zero]`. Simplify using `only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[h2, mem_span_singleton]`. Conclude with `h1`.
-/
theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain A] {I : Ideal A} {a : A} (hI : I = span {a})
    (ha : a ≠ 0) {x : AdicCompletion I A} (h : algebraMap A (AdicCompletion I A) a * x = 0) :
    x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : ∀ m, I ^ m = span {a ^ m} := fun m => by rw [hI, Ideal.span_singleton_pow]
  rw [h2, mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h1
  rw [← factorPow_evalₐ I n.le_succ, ← hy, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [h2, mem_span_singleton]
  exact h1

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

omit [Fact ¬IsUnit (p : R)] [CharZero R] [Fact p.Prime] in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hx (eq_zero_of_forall_pow_dvd (p : R) fun n => (ValuationRing.dvd_total x _).resolve_left (h n))`.
-/
theorem exists_dvd_p_pow {x : R} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (p : R) ^ n := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_forall_pow_dvd (p : R) fun n =>
    (ValuationRing.dvd_total x _).resolve_left (h n))

instance isFractionRing_away : IsFractionRing R (Localization.Away (p : R)) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, c, hc⟩ := exists_dvd_p_pow (p := p) (nonZeroDivisors.ne_zero hx)
      exact ⟨c, n, by simp [hc, mul_comm]⟩)

variable (p R) in
omit [Fact ¬IsUnit (p : R)] in
/- English proof (translation)
The claim follows from `(IsFractionRing.toField R (K := Localization.Away (p : R))).toIsField`.
-/
theorem isField_away : IsField (Localization.Away (p : R)) :=
  (IsFractionRing.toField R (K := Localization.Away (p : R))).toIsField

namespace BdRPlus

omit [IsDomain R] [ValuationRing R] [CharZero R] in

def xi (ϖ : PFlat p R) : BdRPlus p R := algebraMap (Ainf p R) _ (Ainf.xi ϖ)

omit [IsDomain R] [ValuationRing R] [CharZero R] in
/- English proof (translation)
The claim follows from `AinfInv.theta_algebraMap x`.
-/
@[simp] theorem theta_algebraMap_ainf (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) :=
  AinfInv.theta_algebraMap x

/- English proof (translation)
The claim follows from `evalₐ_eq_zero_iff_dvd_of_eq_span (AinfInv.kerTheta_eq ϖ) n x`.
-/
theorem eval_eq_zero_iff (ϖ : PFlat p R) (n : ℕ) (x : BdRPlus p R) :
    eval p R n x = 0 ↔ xi ϖ ^ n ∣ x :=
  evalₐ_eq_zero_iff_dvd_of_eq_span (AinfInv.kerTheta_eq ϖ) n x

/- English proof (translation)
Rewrite using `[← pow_one (xi ϖ), ← eval_eq_zero_iff, theta_eq_zero_iff]`. Use `Iff.trans (Eq.congr_left (AdicCompletion.factorₐ_evalₐ_one _ _).symm) (map_eq_zero_iff _ ?_)` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Rewrite `hy` using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `hy`.
-/
theorem theta_eq_zero_iff_dvd (ϖ : PFlat p R) (x : BdRPlus p R) :
    theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← pow_one (xi ϖ), ← eval_eq_zero_iff, theta_eq_zero_iff]
  refine Iff.trans (Eq.congr_left (AdicCompletion.factorₐ_evalₐ_one _ _).symm)
    (map_eq_zero_iff _ ?_)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hy

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, theta_eq_zero_iff_dvd ϖ, mem_span_singleton]`.
-/
theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  ext x
  rw [RingHom.mem_ker, theta_eq_zero_iff_dvd ϖ, mem_span_singleton]

/- English proof (translation)
Rewrite using `[fil, ker_theta ϖ, Ideal.span_singleton_pow]`.
-/
theorem fil_eq_span (ϖ : PFlat p R) (n : ℕ) : fil p R n = span {xi ϖ ^ n} := by
  rw [fil, ker_theta ϖ, Ideal.span_singleton_pow]

/- English proof (translation)
The claim follows from `eq_zero_of_algebraMap_mul_eq_zero (AinfInv.kerTheta_eq ϖ) ((map_ne_zero_iff _ AinfInv.algebraMap_injective).2 (Ainf.xi_ne_zero ϖ)) h`.
-/
theorem eq_zero_of_xi_mul_eq_zero (ϖ : PFlat p R) {x : BdRPlus p R} (h : xi ϖ * x = 0) : x = 0 :=
  eq_zero_of_algebraMap_mul_eq_zero (AinfInv.kerTheta_eq ϖ)
    ((map_ne_zero_iff _ AinfInv.algebraMap_injective).2 (Ainf.xi_ne_zero ϖ)) h

/- English proof (translation)
The claim follows from `ext_eval fun n => by rw [map_zero, eval_eq_zero_iff ϖ]; exact h n`.
-/
theorem eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : BdRPlus p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [map_zero, eval_eq_zero_iff ϖ]; exact h n

variable [IsAlgClosed (FractionRing R)]

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, eval_eq_zero_iff ϖ, fil_eq_span ϖ, mem_span_singleton]`.
-/
theorem ker_eval (n : ℕ) : RingHom.ker (eval p R n) = fil p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  ext x
  rw [RingHom.mem_ker, eval_eq_zero_iff ϖ, fil_eq_span ϖ, mem_span_singleton]

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Establish `h` using `congrArg (Ideal.map (algebraMap (AinfInv p R) (BdRPlus p R))) (AinfInv.kerTheta_eq ϖ)`. Rewrite using `[ker_theta ϖ, h, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression.
-/
theorem ker_theta_eq_map : RingHom.ker (theta p R) =
    (AinfInv.kerTheta p R).map (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := congrArg (Ideal.map (algebraMap (AinfInv p R) (BdRPlus p R))) (AinfInv.kerTheta_eq ϖ)
  rw [ker_theta ϖ, h, Ideal.map_span, Set.image_singleton]
  rfl

instance isAdicComplete_ker_theta : IsAdicComplete (RingHom.ker (theta p R)) (BdRPlus p R) := by
  rw [ker_theta_eq_map]
  exact AdicCompletion.isAdicComplete_self _ AinfInv.kerTheta_fg

instance isAdicComplete_fil_one : IsAdicComplete (fil p R 1) (BdRPlus p R) := by
  rw [fil, pow_one]
  infer_instance

omit [CharZero R] in

/- English proof (translation)
Introduce `y` and use `let ⟨x, hx⟩ := AinfInv.theta_surjective (p := p) y ⟨algebraMap _ _ x, hx⟩`.
-/
theorem theta_surjective : Function.Surjective (theta p R) := fun y =>
  let ⟨x, hx⟩ := AinfInv.theta_surjective (p := p) y
  ⟨algebraMap _ _ x, hx⟩

/- English proof (translation)
Use `(isField_away p R).nontrivial` as an intermediate fact. Use `⟨fun h => (h.map _).ne_zero, fun h => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `(isField_away p R).mul_inv_cancel h`. Take `⟨y, rfl⟩` from `theta_surjective (p := p) z`. Establish `h1 : x * y - 1 ∈ RingHom.ker (theta p R)`.

Rewrite using `[RingHom.mem_ker, map_sub, map_mul, hz, map_one, sub_self]`. Establish `h2` using `Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1`. Rewrite `h2` using `[mul_one, sub_add_cancel]`. Conclude with `isUnit_of_mul_isUnit_left h2`.
-/
theorem isUnit_iff_theta_ne_zero (x : BdRPlus p R) : IsUnit x ↔ theta p R x ≠ 0 := by
  have := (isField_away p R).nontrivial
  refine ⟨fun h => (h.map _).ne_zero, fun h => ?_⟩
  obtain ⟨z, hz⟩ := (isField_away p R).mul_inv_cancel h
  obtain ⟨y, rfl⟩ := theta_surjective (p := p) z
  have h1 : x * y - 1 ∈ RingHom.ker (theta p R) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hz, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

/- English proof (translation)
Establish `h : ∃ n : ℕ, ¬xi ϖ ^ (n + 1) ∣ x`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hx (eq_zero_of_forall_xi_pow_dvd ϖ fun n => (pow_dvd_pow _ n.le_succ).trans (h n))`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : xi ϖ ^ Nat.find h ∣ x := by`.

Break down `e : Nat.find h with _ | m` into its components or cases. Simplify using the standard rewrite rules. Conclude with `not_not.1 (Nat.find_min h (by omega))`. Establish `hu' : IsUnit u`. Rewrite using `[isUnit_iff_theta_ne_zero, Ne, theta_eq_zero_iff_dvd ϖ]`.

Introduce `hd`. Apply `Nat.find_spec h` to reduce the goal to its premises. Take `⟨v, rfl⟩` from `hd`. Conclude with `⟨v, hu.trans (by ring)⟩`. Conclude with `⟨_, hu'.unit, hu.symm⟩`.
-/
theorem exists_associated_xi_pow (ϖ : PFlat p R) {x : BdRPlus p R} (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (xi ϖ ^ n) x := by
  classical
  have h : ∃ n : ℕ, ¬xi ϖ ^ (n + 1) ∣ x := by
    by_contra h
    push Not at h
    exact hx (eq_zero_of_forall_xi_pow_dvd ϖ fun n => (pow_dvd_pow _ n.le_succ).trans (h n))
  obtain ⟨u, hu⟩ : xi ϖ ^ Nat.find h ∣ x := by
    rcases e : Nat.find h with _ | m
    · simp
    · exact not_not.1 (Nat.find_min h (by omega))
  have hu' : IsUnit u := by
    rw [isUnit_iff_theta_ne_zero, Ne, theta_eq_zero_iff_dvd ϖ]
    intro hd
    apply Nat.find_spec h
    obtain ⟨v, rfl⟩ := hd
    exact ⟨v, hu.trans (by ring)⟩
  exact ⟨_, hu'.unit, hu.symm⟩

instance nontrivial : Nontrivial (BdRPlus p R) :=
  have := (isField_away p R).nontrivial
  (theta p R).domain_nontrivial

instance isDomain : IsDomain (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have key : ∀ (n : ℕ) (y : BdRPlus p R), xi ϖ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      exact ih y (eq_zero_of_xi_mul_eq_zero ϖ (by rw [← mul_assoc, ← pow_succ', hy]))
  have : NoZeroDivisors (BdRPlus p R) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, rfl⟩ := exists_associated_xi_pow ϖ ha
    exact Or.inr ((Units.mul_right_eq_zero u).1 (key n _ (by rw [← mul_assoc, h])))⟩
  exact NoZeroDivisors.to_isDomain _

/- English proof (translation)
Introduce `h` and use `one_ne_zero (eq_zero_of_xi_mul_eq_zero ϖ (x := 1) (by rw [h, zero_mul]))`.
-/
theorem xi_ne_zero (ϖ : PFlat p R) : xi ϖ ≠ 0 := fun h =>
  one_ne_zero (eq_zero_of_xi_mul_eq_zero ϖ (x := 1) (by rw [h, zero_mul]))

/- English proof (translation)
Use `(isField_away p R).isDomain` as an intermediate fact. Rewrite using `[← Ideal.span_singleton_prime (xi_ne_zero ϖ), ← ker_theta]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem prime_xi (ϖ : PFlat p R) : Prime (xi ϖ) := by
  have := (isField_away p R).isDomain
  rw [← Ideal.span_singleton_prime (xi_ne_zero ϖ), ← ker_theta]
  exact RingHom.ker_isPrime _

instance isDiscreteValuationRing : IsDiscreteValuationRing (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨xi ϖ, (prime_xi ϖ).irreducible, exists_associated_xi_pow ϖ⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_theta_ne_zero, not_not, RingHom.mem_ker]`.
-/
theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (BdRPlus p R) = RingHom.ker (theta p R) := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_theta_ne_zero, not_not,
    RingHom.mem_ker]

/- English proof (translation)
Rewrite using `[fil, maximalIdeal_eq]`.
-/
theorem fil_eq_maximalIdeal_pow (n : ℕ) :
    fil p R n = IsLocalRing.maximalIdeal (BdRPlus p R) ^ n := by rw [fil, maximalIdeal_eq]

instance isAdicComplete_maximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal (BdRPlus p R)) (BdRPlus p R) := by
  rw [maximalIdeal_eq]
  infer_instance

/- English proof (translation)
Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer, maximalIdeal_eq]`.
-/
theorem irreducible_iff (π : BdRPlus p R) : Irreducible π ↔ RingHom.ker (theta p R) = span {π} := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maximalIdeal_eq]

variable (p R) in

def residueFieldEquiv : IsLocalRing.ResidueField (BdRPlus p R) ≃+* Localization.Away (p : R) :=
  (Ideal.quotEquivOfEq maximalIdeal_eq).trans (RingHom.quotientKerEquivOfSurjective theta_surjective)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem residueFieldEquiv_residue (x : BdRPlus p R) :
    residueFieldEquiv p R (IsLocalRing.residue _ x) = theta p R x := rfl

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `AinfInv.eq_zero_of_forall_mem_kerTheta_pow ϖ fun n => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← eval_algebraMap, hx, map_zero]`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine AinfInv.eq_zero_of_forall_mem_kerTheta_pow ϖ fun n => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_algebraMap, hx, map_zero]

/- English proof (translation)
The claim follows from `algebraMap_injective.comp AinfInv.algebraMap_injective`.
-/
theorem algebraMap_ainf_injective : Function.Injective (algebraMap (Ainf p R) (BdRPlus p R)) :=
  algebraMap_injective.comp AinfInv.algebraMap_injective

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Take `⟨b, hb, hb0⟩` from `Ainf.exists_teich_sub_one_eq ϖ hε`. Establish `hu : IsUnit (algebraMap (Ainf p R) (BdRPlus p R) b)`. Rewrite using `[isUnit_iff_theta_ne_zero, theta_algebraMap_ainf]`. Conclude with `(map_ne_zero_iff _ AinfInv.algebraMap_away_injective).2 hb0`.

Rewrite using `[ker_theta ϖ, hb, map_mul, Ideal.span_singleton_mul_right_unit hu]`. Both sides reduce to the same expression.
-/
theorem ker_theta_eq_span_teich_sub_one {ε : tateModule p R} (hε : IsPrimitive ε) :
    RingHom.ker (theta p R) = span {algebraMap (Ainf p R) (BdRPlus p R) (Ainf.teich p ε.1 - 1)} := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨b, hb, hb0⟩ := Ainf.exists_teich_sub_one_eq ϖ hε
  have hu : IsUnit (algebraMap (Ainf p R) (BdRPlus p R) b) := by
    rw [isUnit_iff_theta_ne_zero, theta_algebraMap_ainf]
    exact (map_ne_zero_iff _ AinfInv.algebraMap_away_injective).2 hb0
  rw [ker_theta ϖ, hb, map_mul, Ideal.span_singleton_mul_right_unit hu]
  rfl

end BdRPlus

namespace BdR

variable [IsAlgClosed (FractionRing R)]

instance field : Field (BdR p R) := IsFractionRing.toField (BdRPlus p R)

/- English proof (translation)
The claim follows from `IsFractionRing.injective _ _`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) :=
  IsFractionRing.injective _ _

section Uniformizer

variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ algebraMap_injective).2 ((BdRPlus.irreducible_iff π).2 hπ).ne_zero`.
-/
theorem algebraMap_ne_zero : algebraMap (BdRPlus p R) (BdR p R) π ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_injective).2 ((BdRPlus.irreducible_iff π).2 hπ).ne_zero

/- English proof (translation)
Rewrite using `[filNat, BdRPlus.fil, hπ, Ideal.span_singleton_pow, ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton, Algebra.linearMap_apply, map_pow]`.
-/
theorem filNat_eq_span (n : ℕ) :
    filNat p R n = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ n} := by
  rw [filNat, BdRPlus.fil, hπ, Ideal.span_singleton_pow, ← Ideal.submodule_span_eq,
    Submodule.map_span, Set.image_singleton, Algebra.linearMap_apply, map_pow]

/- English proof (translation)
Establish `h0` using `algebraMap_ne_zero hπ`. Use `set t := algebraMap (BdRPlus p R) (BdR p R) π`. Establish `hi : t ^ i * t ^ (-i).toNat = t ^ i.toNat`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Use extensionality with `x`. Rewrite using `[fil, filNat_eq_span hπ, filNat_eq_span hπ, Submodule.mem_div_iff_forall_mul_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 (h _ (Submodule.mem_span_singleton_self _))`. Use `Submodule.mem_span_singleton.2 ⟨c, mul_right_cancel₀ (pow_ne_zero (-i).toNat h0) ?_⟩` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, hi, hc]`. Introduce `h y hy`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 h`.

Take `⟨d, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Conclude with `Submodule.mem_span_singleton.2 ⟨c * d, by rw [smul_mul_smul_comm, hi]⟩`.
-/
theorem fil_eq_span (i : ℤ) :
    fil p R i = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ i} := by
  have h0 := algebraMap_ne_zero hπ
  set t := algebraMap (BdRPlus p R) (BdR p R) π
  have hi : t ^ i * t ^ (-i).toNat = t ^ i.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  ext x
  rw [fil, filNat_eq_span hπ, filNat_eq_span hπ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h _ (Submodule.mem_span_singleton_self _))
    refine Submodule.mem_span_singleton.2 ⟨c, mul_right_cancel₀ (pow_ne_zero (-i).toNat h0) ?_⟩
    rw [smul_mul_assoc, hi, hc]
  · intro h y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact Submodule.mem_span_singleton.2 ⟨c * d, by rw [smul_mul_smul_comm, hi]⟩

/- English proof (translation)
Rewrite using `[fil_eq_span hπ, Submodule.mem_span_singleton]`. Simplify using `only [Algebra.smul_def, mul_comm, eq_comm]`.
-/
theorem mem_fil_iff (i : ℤ) (x : BdR p R) : x ∈ fil p R i ↔ ∃ c : BdRPlus p R,
    x = algebraMap (BdRPlus p R) (BdR p R) π ^ i * algebraMap (BdRPlus p R) (BdR p R) c := by
  rw [fil_eq_span hπ, Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, mul_comm, eq_comm]

/- English proof (translation)
Establish `hirr` using `(BdRPlus.irreducible_iff π).2 hπ`. Use `IsLocalization.Away.mk π (algebraMap_ne_zero hπ).isUnit ?_ ?_` and prove the remaining obligations. Introduce `z`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (BdRPlus p R) z`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hirr`.

Use `⟨n, a * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `h0` using `algebraMap_ne_zero hπ`. Establish `hu : algebraMap (BdRPlus p R) (BdR p R) u ≠ 0` using `(u.isUnit.map _).ne_zero`. Rewrite using `[map_mul, map_mul, map_pow, map_units_inv]`. Clear the denominators using the available nonvanishing facts.

Introduce `a b h`. Conclude with `⟨0, by rw [algebraMap_injective h]⟩`.
-/
theorem isLocalization_away : IsLocalization.Away π (BdR p R) := by
  have hirr := (BdRPlus.irreducible_iff π).2 hπ
  refine IsLocalization.Away.mk π (algebraMap_ne_zero hπ).isUnit ?_ ?_
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (BdRPlus p R) z
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hirr
    refine ⟨n, a * ↑u⁻¹, ?_⟩
    have h0 := algebraMap_ne_zero hπ
    have hu : algebraMap (BdRPlus p R) (BdR p R) u ≠ 0 := (u.isUnit.map _).ne_zero
    rw [map_mul, map_mul, map_pow, map_units_inv]
    field_simp
  · intro a b h
    exact ⟨0, by rw [algebraMap_injective h]⟩

end Uniformizer

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Rewrite using `[fil_eq_span (BdRPlus.ker_theta ϖ), filNat_eq_span (BdRPlus.ker_theta ϖ), zpow_natCast]`.
-/
theorem fil_natCast (n : ℕ) : fil p R n = filNat p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), filNat_eq_span (BdRPlus.ker_theta ϖ), zpow_natCast]

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Rewrite using `[fil_eq_span (BdRPlus.ker_theta ϖ), zpow_zero, Submodule.one_eq_span]`.
-/
theorem fil_zero : fil p R 0 = 1 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), zpow_zero, Submodule.one_eq_span]

/- English proof (translation)
Rewrite using `[fil_zero, Submodule.mem_one]`.
-/
theorem mem_fil_zero_iff (x : BdR p R) :
    x ∈ fil p R 0 ↔ ∃ c : BdRPlus p R, algebraMap _ _ c = x := by
  rw [fil_zero, Submodule.mem_one]

/- English proof (translation)
Rewrite using `[fil_natCast, filNat, Submodule.mem_map]`. Conclude with `⟨fun ⟨y, hy, e⟩ => algebraMap_injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩`.
-/
theorem algebraMap_mem_fil_iff (n : ℕ) (x : BdRPlus p R) :
    algebraMap _ (BdR p R) x ∈ fil p R n ↔ x ∈ BdRPlus.fil p R n := by
  rw [fil_natCast, filNat, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => algebraMap_injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Establish `h` using `BdRPlus.ker_theta ϖ`. Rewrite using `[fil_eq_span h, fil_eq_span h, fil_eq_span h, Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ (algebraMap_ne_zero h)]`.
-/
theorem fil_mul_fil (i j : ℤ) : fil p R i * fil p R j = fil p R (i + j) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  rw [fil_eq_span h, fil_eq_span h, fil_eq_span h, Submodule.span_mul_span,
    Set.singleton_mul_singleton, zpow_add₀ (algebraMap_ne_zero h)]

/- English proof (translation)
The claim follows from `fil_mul_fil (p := p) (R := R) i j ▸ Submodule.mul_mem_mul hx hy`.
-/
theorem mul_mem_fil {i j : ℤ} {x y : BdR p R} (hx : x ∈ fil p R i) (hy : y ∈ fil p R j) :
    x * y ∈ fil p R (i + j) := fil_mul_fil (p := p) (R := R) i j ▸ Submodule.mul_mem_mul hx hy

instance gradedMonoid : SetLike.GradedMonoid (fil p R) where
  one_mem := (mem_fil_zero_iff _).2 ⟨1, map_one _⟩
  mul_mem _ _ _ _ := mul_mem_fil

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Establish `h` using `BdRPlus.ker_theta ϖ`. Introduce `i j hij x hx`. Take `⟨n, rfl⟩` from `Int.le.dest hij`. Take `⟨c, rfl⟩` from `(mem_fil_iff h _ _).1 hx`.

Conclude with `(mem_fil_iff h _ _).2 ⟨BdRPlus.xi ϖ ^ n * c, by`. Rewrite using `[zpow_add₀ (algebraMap_ne_zero h), map_mul, map_pow, zpow_natCast, mul_assoc]⟩`.
-/
theorem fil_antitone : Antitone (fil p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  intro i j hij x hx
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  obtain ⟨c, rfl⟩ := (mem_fil_iff h _ _).1 hx
  exact (mem_fil_iff h _ _).2 ⟨BdRPlus.xi ϖ ^ n * c, by
    rw [zpow_add₀ (algebraMap_ne_zero h), map_mul, map_pow, zpow_natCast, mul_assoc]⟩

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Establish `h` using `BdRPlus.ker_theta ϖ`. Use `isLocalization_away h` as an intermediate fact. Take `⟨n, a, e⟩` from `IsLocalization.Away.surj (BdRPlus.xi ϖ) x`. Use `⟨-n, (mem_fil_iff h _ _).2 ⟨a, ?_⟩⟩` and prove the remaining obligations.

Establish `h0` using `algebraMap_ne_zero h`. Rewrite using `[← e, zpow_neg, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_mem_fil (x : BdR p R) : ∃ i, x ∈ fil p R i := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  have := isLocalization_away h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj (BdRPlus.xi ϖ) x
  refine ⟨-n, (mem_fil_iff h _ _).2 ⟨a, ?_⟩⟩
  have h0 := algebraMap_ne_zero h
  rw [← e, zpow_neg, zpow_natCast]
  field_simp

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun x _ => let ⟨i, hi⟩ := exists_mem_fil x; Submodule.mem_iSup_of_mem i hi`.
-/
theorem iSup_fil : ⨆ i, fil p R i = ⊤ :=
  eq_top_iff.2 fun x _ => let ⟨i, hi⟩ := exists_mem_fil x; Submodule.mem_iSup_of_mem i hi

/- English proof (translation)
Take `⟨ϖ⟩ : Nonempty (PFlat p R)` from `inferInstance`. Take `⟨c, rfl⟩` from `(mem_fil_zero_iff x).1 (h 0)`. Rewrite using `[BdRPlus.eq_zero_of_forall_xi_pow_dvd ϖ (x := c) fun n => ?_, map_zero]`. Rewrite using `[← mem_span_singleton, ← BdRPlus.fil_eq_span, ← algebraMap_mem_fil_iff]`. Conclude with `h n`.
-/
theorem eq_zero_of_forall_mem_fil {x : BdR p R} (h : ∀ i, x ∈ fil p R i) : x = 0 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨c, rfl⟩ := (mem_fil_zero_iff x).1 (h 0)
  rw [BdRPlus.eq_zero_of_forall_xi_pow_dvd ϖ (x := c) fun n => ?_, map_zero]
  rw [← mem_span_singleton, ← BdRPlus.fil_eq_span, ← algebraMap_mem_fil_iff]
  exact h n

/- English proof (translation)
The claim follows from `eq_bot_iff.2 fun _ hx => eq_zero_of_forall_mem_fil fun i => (Submodule.mem_iInf _).1 hx i`.
-/
theorem iInf_fil : ⨅ i, fil p R i = ⊥ :=
  eq_bot_iff.2 fun _ hx => eq_zero_of_forall_mem_fil fun i => (Submodule.mem_iInf _).1 hx i

instance charZero : CharZero (BdR p R) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (BdR p R)).injective

end BdR

end Reformulated.AutPerF
