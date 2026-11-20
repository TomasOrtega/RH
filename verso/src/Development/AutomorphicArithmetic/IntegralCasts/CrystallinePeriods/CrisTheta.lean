import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]

namespace AinfInv

/- English proof (translation)
The claim follows from `IsUnit.natCast_factorial_of_algebra ℚ n`.
-/
theorem isUnit_factorial (n : ℕ) : IsUnit (n ! : AinfInv p R) :=
  IsUnit.natCast_factorial_of_algebra ℚ n

open Classical in
/- English proof (translation)
The claim follows from `eq_gamma (DividedPowers.factorial_mul_dpow_eq_pow _ Submodule.mem_top)`.
-/
theorem gamma_eq_dpow (n : ℕ) (x : AinfInv p R) :
    gamma n x = (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (AinfInv p R))).dpow n x :=
  eq_gamma (DividedPowers.factorial_mul_dpow_eq_pow _ Submodule.mem_top)

/- English proof (translation)
Simplify using `[gamma]`.
-/
@[simp] theorem gamma_zero (x : AinfInv p R) : gamma 0 x = 1 := by simp [gamma]

/- English proof (translation)
Simplify using `[gamma]`.
-/
@[simp] theorem gamma_one (x : AinfInv p R) : gamma 1 x = x := by simp [gamma]

/- English proof (translation)
Simplify using `only [gamma_eq_dpow]`. Conclude with `DividedPowers.dpow_add _ Submodule.mem_top Submodule.mem_top`.
-/
theorem gamma_add (n : ℕ) (x y : AinfInv p R) :
    gamma n (x + y) = ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, gamma k.1 x * gamma k.2 y := by
  simp only [gamma_eq_dpow]
  exact DividedPowers.dpow_add _ Submodule.mem_top Submodule.mem_top

/- English proof (translation)
Simplify using `only [gamma_eq_dpow]`. Conclude with `DividedPowers.dpow_mul _ Submodule.mem_top`.
-/
theorem gamma_mul (n : ℕ) (a x : AinfInv p R) : gamma n (a * x) = a ^ n * gamma n x := by
  simp only [gamma_eq_dpow]
  exact DividedPowers.dpow_mul _ Submodule.mem_top

/- English proof (translation)
Simplify using `only [gamma_eq_dpow]`. Conclude with `DividedPowers.mul_dpow _ Submodule.mem_top`.
-/
theorem gamma_mul_gamma (m n : ℕ) (x : AinfInv p R) :
    gamma m x * gamma n x = (m + n).choose m * gamma (m + n) x := by
  simp only [gamma_eq_dpow]
  exact DividedPowers.mul_dpow _ Submodule.mem_top

/- English proof (translation)
Simplify using `only [gamma_eq_dpow]`. Conclude with `DividedPowers.dpow_comp _ hn Submodule.mem_top`.
-/
theorem gamma_gamma (m : ℕ) {n : ℕ} (hn : n ≠ 0) (x : AinfInv p R) :
    gamma m (gamma n x) = Nat.uniformBell m n * gamma (m * n) x := by
  simp only [gamma_eq_dpow]
  exact DividedPowers.dpow_comp _ hn Submodule.mem_top

end AinfInv

variable [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

/- English proof (translation)
Establish `h` using `congrArg (AinfInv.theta p R) (AinfInv.factorial_mul_gamma n x)`. Rewrite `h` using `[map_mul, map_pow, hx, zero_pow hn]`. Conclude with `(((AinfInv.isUnit_factorial n).map (AinfInv.theta p R)).mul_right_eq_zero).1 h`.
-/
theorem AinfInv.theta_gamma {n : ℕ} (hn : n ≠ 0) {x : AinfInv p R} (hx : AinfInv.theta p R x = 0) :
    AinfInv.theta p R (AinfInv.gamma n x) = 0 := by
  have h := congrArg (AinfInv.theta p R) (AinfInv.factorial_mul_gamma n x)
  rw [map_mul, map_pow, hx, zero_pow hn] at h
  exact (((AinfInv.isUnit_factorial n).map (AinfInv.theta p R)).mul_right_eq_zero).1 h

namespace AcrisZero

variable (p R) in

def pdIdeal : Ideal (AcrisZero p R) :=
  span {y | ∃ (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0), n ≠ 0 ∧ y = gamma n x hx}

/- English proof (translation)
The claim follows from `subset_span ⟨n, x, hx, hn, rfl⟩`.
-/
theorem gamma_mem_pdIdeal {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    gamma n x hx ∈ pdIdeal p R := subset_span ⟨n, x, hx, hn, rfl⟩

/- English proof (translation)
Establish `: algebraMap _ _ x = gamma 1 x hx` using `Subtype.ext (AinfInv.gamma_one _).symm`. Rewrite using `[this]`. Conclude with `gamma_mem_pdIdeal one_ne_zero x hx`.
-/
theorem algebraMap_mem_pdIdeal (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap _ _ x ∈ pdIdeal p R := by
  have : algebraMap _ _ x = gamma 1 x hx := Subtype.ext (AinfInv.gamma_one _).symm
  rw [this]
  exact gamma_mem_pdIdeal one_ne_zero x hx

/- English proof (translation)
Take `⟨y, hy⟩` from `y`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨n, x, hx, rfl⟩` from `hy`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases.

Use `⟨1, ?_⟩` and prove the remaining obligations. Use `(pdIdeal p R).zero_mem` and compare the differences between its conclusion and the goal. Rewrite using `[sub_eq_zero, map_one]`. Conclude with `Subtype.ext (AinfInv.gamma_zero _)`. Conclude with `⟨0, by rw [map_zero, sub_zero]; exact gamma_mem_pdIdeal hn x hx⟩`.

Consider the case `algebraMap r`. Use `⟨r, ?_⟩` and prove the remaining obligations. Use `(pdIdeal p R).zero_mem` and compare the differences between its conclusion and the goal. Rewrite using `[sub_eq_zero]`. Both sides reduce to the same expression.

Consider the case `add x y hx' hy' hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Use `add_mem ha hb using 1` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `(⟨x, hx'⟩ + ⟨y, hy'⟩ : AcrisZero p R) - _ = _`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y hx' hy' hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Use `add_mem (Ideal.mul_mem_right ⟨y, hy'⟩ _ ha) (Ideal.mul_mem_left _ (algebraMap _ _ a) hb) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(⟨x, hx'⟩ * ⟨y, hy'⟩ : AcrisZero p R) - _ = _`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sub_mem_pdIdeal (y : AcrisZero p R) :
    ∃ a : Ainf p R, y - algebraMap _ _ a ∈ pdIdeal p R := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨1, ?_⟩
      convert (pdIdeal p R).zero_mem
      rw [sub_eq_zero, map_one]
      exact Subtype.ext (AinfInv.gamma_zero _)
    · exact ⟨0, by rw [map_zero, sub_zero]; exact gamma_mem_pdIdeal hn x hx⟩
  | algebraMap r =>
    refine ⟨r, ?_⟩
    convert (pdIdeal p R).zero_mem
    rw [sub_eq_zero]
    rfl
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    change (⟨x, hx'⟩ + ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_add]; ring
  | mul x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    convert add_mem (Ideal.mul_mem_right ⟨y, hy'⟩ _ ha)
      (Ideal.mul_mem_left _ (algebraMap _ _ a) hb) using 1
    change (⟨x, hx'⟩ * ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_mul]; ring

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨n, x, hx, hn, rfl⟩` from `hy`. Conclude with `AinfInv.theta_gamma hn (by rw [AinfInv.theta_algebraMap, hx, map_zero])`. Consider the case `zero => exact map_zero _`.

Consider the case `add x y _ _ hx hy => rw [AddMemClass.coe_add, map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, hx, mul_zero]`.
-/
theorem theta_eq_zero_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) :
    AinfInv.theta p R y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, hn, rfl⟩ := hy
    exact AinfInv.theta_gamma hn (by rw [AinfInv.theta_algebraMap, hx, map_zero])
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [AddMemClass.coe_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, hx, mul_zero]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction generalizing n with`. Consider the case `mem y hy`. Take `⟨m, x, hx, hm, rfl⟩` from `hy`. Rewrite using `[coe_gamma, AinfInv.gamma_gamma n hm]`. Conclude with `mul_mem (natCast_mem _ _) (gamma _ x hx).2`.

Consider the case `zero`. Use `(gamma n (0 : Ainf p R) (map_zero _)).2` as an intermediate fact. Rewrite `this` using `[coe_gamma, map_zero]`. Then use the resulting hypothesis. Consider the case `add x y _ _ hx hy`. Rewrite using `[AddMemClass.coe_add, AinfInv.gamma_add]`.

Conclude with `sum_mem fun k _ => mul_mem (hx _) (hy _)`. Consider the case `smul a x _ hx`. Rewrite using `[smul_eq_mul, MulMemClass.coe_mul, AinfInv.gamma_mul]`. Conclude with `mul_mem (pow_mem a.2 _) (hx _)`.
-/
theorem gamma_mem_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) (n : ℕ) :
    AinfInv.gamma n (y : AinfInv p R) ∈ acrisZero p R := by
  induction hy using Submodule.span_induction generalizing n with
  | mem y hy =>
    obtain ⟨m, x, hx, hm, rfl⟩ := hy
    rw [coe_gamma, AinfInv.gamma_gamma n hm]
    exact mul_mem (natCast_mem _ _) (gamma _ x hx).2
  | zero =>
    have := (gamma n (0 : Ainf p R) (map_zero _)).2
    rwa [coe_gamma, map_zero] at this
  | add x y _ _ hx hy =>
    rw [AddMemClass.coe_add, AinfInv.gamma_add]
    exact sum_mem fun k _ => mul_mem (hx _) (hy _)
  | smul a x _ hx =>
    rw [smul_eq_mul, MulMemClass.coe_mul, AinfInv.gamma_mul]
    exact mul_mem (pow_mem a.2 _) (hx _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_, gamma_mem_of_mem_pdIdeal hy n⟩, Subtype.ext (by simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] exact (AinfInv.factorial_mul_gamma n _).symm)⟩`.
-/
theorem factorial_dvd_pow_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) (n : ℕ) :
    (n ! : AcrisZero p R) ∣ y ^ n :=
  ⟨⟨_, gamma_mem_of_mem_pdIdeal hy n⟩, Subtype.ext (by
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    exact (AinfInv.factorial_mul_gamma n _).symm)⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_sub_mem_pdIdeal y`. Establish `h` using `theta_eq_zero_of_mem_pdIdeal ha`. Rewrite `h` using `[AddSubgroupClass.coe_sub, map_sub, sub_eq_zero, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap]`. Conclude with `⟨_, h.symm⟩`.
-/
theorem exists_theta_eq (y : AcrisZero p R) :
    ∃ r : R, algebraMap R (Localization.Away (p : R)) r = AinfInv.theta p R y := by
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h := theta_eq_zero_of_mem_pdIdeal ha
  rw [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero, Subalgebra.coe_algebraMap,
    AinfInv.theta_algebraMap] at h
  exact ⟨_, h.symm⟩

end AcrisZero

variable [IsDomain R] [CharZero R] [IsDomain S] [CharZero S]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
/- English proof (translation)
The claim follows from `IsLocalization.injective (M := Submonoid.powers (p : R)) _ (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))`.
-/
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective (M := Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

namespace AcrisZero

variable (p R) in

def theta : AcrisZero p R →+* R where
  toFun y := (exists_theta_eq y).choose
  map_one' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_mul' x y := algebraMap_away_injective (p := p) (by
    rw [map_mul, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)
  map_zero' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_add' x y := algebraMap_away_injective (p := p) (by
    rw [map_add, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)

/- English proof (translation)
The claim follows from `(exists_theta_eq y).choose_spec`.
-/
theorem algebraMap_theta (y : AcrisZero p R) :
    algebraMap R (Localization.Away (p : R)) (theta p R y) = AinfInv.theta p R y :=
  (exists_theta_eq y).choose_spec

/- English proof (translation)
The claim follows from `algebraMap_away_injective (p := p) (by rw [algebraMap_theta, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap])`.
-/
@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x :=
  algebraMap_away_injective (p := p) (by
    rw [algebraMap_theta, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap])

/- English proof (translation)
The claim follows from `algebraMap_away_injective (p := p) (by rw [algebraMap_theta, coe_map, AinfInv.theta_map, ← algebraMap_theta, awayMap_algebraMap])`.
-/
theorem theta_map (f : R →+* S) (y : AcrisZero p R) : theta p S (map p f y) = f (theta p R y) :=
  algebraMap_away_injective (p := p) (by
    rw [algebraMap_theta, coe_map, AinfInv.theta_map, ← algebraMap_theta, awayMap_algebraMap])

/- English proof (translation)
Establish `key : ∀ y ∈ pdIdeal p R, theta p R y = 0` using `fun y hy => algebraMap_away_injective (p := p) (by`. Rewrite using `[algebraMap_theta, theta_eq_zero_of_mem_pdIdeal hy, map_zero])`. Use `⟨fun h => ?_, key y⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_sub_mem_pdIdeal y`. Establish `h1` using `key _ ha`.

Rewrite `h1` using `[map_sub, h, theta_algebraMap, zero_sub, neg_eq_zero]`. Simplify using `using add_mem ha (algebraMap_mem_pdIdeal a h1)`.
-/
theorem theta_eq_zero_iff (y : AcrisZero p R) : theta p R y = 0 ↔ y ∈ pdIdeal p R := by
  have key : ∀ y ∈ pdIdeal p R, theta p R y = 0 := fun y hy =>
    algebraMap_away_injective (p := p) (by
      rw [algebraMap_theta, theta_eq_zero_of_mem_pdIdeal hy, map_zero])
  refine ⟨fun h => ?_, key y⟩
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h1 := key _ ha
  rw [map_sub, h, theta_algebraMap, zero_sub, neg_eq_zero] at h1
  simpa using add_mem ha (algebraMap_mem_pdIdeal a h1)

/- English proof (translation)
The claim follows from `Ideal.ext theta_eq_zero_iff`.
-/
theorem ker_theta : RingHom.ker (theta p R) = pdIdeal p R :=
  Ideal.ext theta_eq_zero_iff

/- English proof (translation)
The claim follows from `(theta_eq_zero_iff _).2 (gamma_mem_pdIdeal hn x hx)`.
-/
@[simp] theorem theta_gamma {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    theta p R (gamma n x hx) = 0 :=
  (theta_eq_zero_iff _).2 (gamma_mem_pdIdeal hn x hx)

end AcrisZero

namespace Acris

variable (p R) in

def theta : Acris p R →+* R :=
  ((AdicCompletion.ofAlgEquiv (span {(p : R)})).symm : _ →+* R).comp
    (adicMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _))

/- English proof (translation)
Establish `h` using `adicMap_algebraMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _) a`. Use `(congrArg (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm h).trans ?_` and prove the remaining obligations. Conclude with `AdicCompletion.ofAlgEquiv_symm_of _ _`.
-/
@[simp] theorem theta_algebraMap_zero (a : AcrisZero p R) :
    theta p R (algebraMap _ _ a) = AcrisZero.theta p R a := by
  have h := adicMap_algebraMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _) a
  refine (congrArg (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm h).trans ?_
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), theta_algebraMap_zero, AcrisZero.theta_algebraMap]`.
-/
@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), theta_algebraMap_zero,
    AcrisZero.theta_algebraMap]

/- English proof (translation)
The claim follows from `RingHom.congr_fun (hom_ext (f := (theta p S).comp (map p f)) (g := f.comp (theta p R)) (by simp [AcrisZero.theta_map])) x`.
-/
theorem theta_map (f : R →+* S) (x : Acris p R) : theta p S (map p f x) = f (theta p R x) :=
  RingHom.congr_fun (hom_ext (f := (theta p S).comp (map p f)) (g := f.comp (theta p R))
    (by simp [AcrisZero.theta_map])) x

/- English proof (translation)
Introduce `r` and use `by obtain ⟨a, rfl⟩ := hθ r exact ⟨_, theta_algebraMap a⟩`.
-/
theorem theta_surjective (hθ : Function.Surjective (Ainf.theta p R)) :
    Function.Surjective (theta p R) := fun r => by
  obtain ⟨a, rfl⟩ := hθ r
  exact ⟨_, theta_algebraMap a⟩

/- English proof (translation)
Use `IsHausdorff.haus (I := span {(p : R)}) inferInstance _ fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `(eval_eq_zero_iff n (log u hu - algebraMap _ _ (logPartial (p ^ n) u hu))).1 (by rw [map_sub, eval_log u hu le_rfl, eval_algebraMap, sub_self])`. Establish `h0 : AcrisZero.theta p R (logPartial (p ^ n) u hu) = 0`. Rewrite using `[logPartial, map_sum]`. Conclude with `Finset.sum_eq_zero fun k _ => by`.

Rewrite using `[map_mul, AcrisZero.theta_gamma (Nat.succ_ne_zero k), mul_zero]`. Establish `h` using `congrArg (theta p R) hy`. Rewrite `h` using `[map_sub, theta_algebraMap_zero, h0, sub_zero, map_mul, map_pow, map_natCast]`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `⟨_, h⟩`.
-/
@[simp] theorem theta_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) : theta p R (log u hu) = 0 := by
  refine IsHausdorff.haus (I := span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (log u hu - algebraMap _ _ (logPartial (p ^ n) u hu))).1
    (by rw [map_sub, eval_log u hu le_rfl, eval_algebraMap, sub_self])
  have h0 : AcrisZero.theta p R (logPartial (p ^ n) u hu) = 0 := by
    rw [logPartial, map_sum]
    exact Finset.sum_eq_zero fun k _ => by
      rw [map_mul, AcrisZero.theta_gamma (Nat.succ_ne_zero k), mul_zero]
  have h := congrArg (theta p R) hy
  rw [map_sub, theta_algebraMap_zero, h0, sub_zero, map_mul, map_pow, map_natCast] at h
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨_, h⟩

/- English proof (translation)
The claim follows from `theta_log _ _`.
-/
@[simp] theorem theta_logTeich (η : tateModule p R) : theta p R (logTeich η) = 0 := theta_log _ _

omit [IsDomain R] [CharZero R] in
/- English proof (translation)
Take `⟨a, ha⟩` from `exists_factorial_mul_eq_pow p n`. Use `congrArg (algebraMap ℤ_[p] (Acris p R)) ha` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_natCast, map_natCast]`. Conclude with `⟨_, this.symm⟩`.
-/
theorem factorial_dvd_p_pow (n : ℕ) : (n ! : Acris p R) ∣ (p : Acris p R) ^ n := by
  obtain ⟨a, ha⟩ := exists_factorial_mul_eq_pow p n
  have := congrArg (algebraMap ℤ_[p] (Acris p R)) ha
  rw [map_mul, map_pow, map_natCast, map_natCast] at this
  exact ⟨_, this.symm⟩

/- English proof (translation)
Take `⟨a, z, rfl⟩` from `exists_eq_add n x`. Take `⟨c, hc⟩` from `hθ (theta p R z)`. Establish `h1 : AcrisZero.theta p R (a + p ^ n * algebraMap _ _ c) = 0`. Simplify `hx` using `[hc]`. Establish `h2` using `map_dvd (algebraMap (AcrisZero p R) (Acris p R)) (AcrisZero.factorial_dvd_pow_of_mem_pdIdeal ((AcrisZero.theta_eq_zero_iff _).1 h1) n)`.

Rewrite `h2` using `[map_natCast, map_pow, map_add, map_mul, map_pow, map_natCast]`. Rewrite using `[← dvd_sub_left h2]`. Use `((factorial_dvd_p_pow n).trans ?_).trans (sub_dvd_pow_sub_pow _ _ n)` and prove the remaining obligations. Conclude with `⟨z - algebraMap _ _ (algebraMap (Ainf p R) (AcrisZero p R) c), by ring⟩`.
-/
theorem factorial_dvd_pow (hθ : Function.Surjective (Ainf.theta p R)) {x : Acris p R}
    (hx : theta p R x = 0) (n : ℕ) : (n ! : Acris p R) ∣ x ^ n := by
  obtain ⟨a, z, rfl⟩ := exists_eq_add n x
  obtain ⟨c, hc⟩ := hθ (theta p R z)
  have h1 : AcrisZero.theta p R (a + p ^ n * algebraMap _ _ c) = 0 := by
    simpa [hc] using hx
  have h2 := map_dvd (algebraMap (AcrisZero p R) (Acris p R))
    (AcrisZero.factorial_dvd_pow_of_mem_pdIdeal ((AcrisZero.theta_eq_zero_iff _).1 h1) n)
  rw [map_natCast, map_pow, map_add, map_mul, map_pow, map_natCast] at h2
  rw [← dvd_sub_left h2]
  refine ((factorial_dvd_p_pow n).trans ?_).trans (sub_dvd_pow_sub_pow _ _ n)
  exact ⟨z - algebraMap _ _ (algebraMap (Ainf p R) (AcrisZero p R) c), by ring⟩

/- English proof (translation)
Take `⟨y, hy⟩` from `factorial_dvd_pow hθ hx n`. Use `⟨y, fun hn => ?_, hy.symm⟩` and prove the remaining obligations. Establish `h` using `congrArg (theta p R) hy`. Rewrite `h` using `[map_pow, hx, zero_pow hn, map_mul, map_natCast]`. Conclude with `(mul_eq_zero.1 h.symm).resolve_left (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))`.
-/
theorem exists_dpow (hθ : Function.Surjective (Ainf.theta p R)) {x : Acris p R}
    (hx : theta p R x = 0) (n : ℕ) :
    ∃ y : Acris p R, (n ≠ 0 → theta p R y = 0) ∧ (n ! : Acris p R) * y = x ^ n := by
  obtain ⟨y, hy⟩ := factorial_dvd_pow hθ hx n
  refine ⟨y, fun hn => ?_, hy.symm⟩
  have h := congrArg (theta p R) hy
  rw [map_pow, hx, zero_pow hn, map_mul, map_natCast] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))

open Classical in

def dividedPowers (hθ : Function.Surjective (Ainf.theta p R)) :
    DividedPowers (RingHom.ker (theta p R)) :=
  letI : Algebra ℚ (BcrisPlus p R) :=
    ((algebraMap ℚ_[p] (BcrisPlus p R)).comp (algebraMap ℚ ℚ_[p])).toAlgebra
  DividedPowers.ofInjective _ _ (algebraMap (Acris p R) (BcrisPlus p R))
    BcrisPlus.algebraMap_injective (DividedPowers.RatAlgebra.dividedPowers _) rfl (by
      intro n x hx
      obtain ⟨y, hy, hy'⟩ := exists_dpow hθ hx n
      refine ⟨y, hy, (IsUnit.natCast_factorial_of_algebra ℚ n).mul_left_cancel ?_⟩
      rw [DividedPowers.factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem _ hx), ← map_pow, ← hy',
        map_mul, map_natCast])

/- English proof (translation)
The claim follows from `DividedPowers.factorial_mul_dpow_eq_pow _ hx`.
-/
theorem factorial_mul_dpow (hθ : Function.Surjective (Ainf.theta p R)) (n : ℕ) {x : Acris p R}
    (hx : theta p R x = 0) : (n ! : Acris p R) * (dividedPowers hθ).dpow n x = x ^ n :=
  DividedPowers.factorial_mul_dpow_eq_pow _ hx

end Acris

namespace BcrisPlus

variable (p R) in

def theta : BcrisPlus p R →+* Localization.Away (p : R) :=
  lift ((algebraMap R _).comp (Acris.theta p R))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : R)) (p : R))

/- English proof (translation)
The claim follows from `lift_algebraMap _ _ x`.
-/
@[simp] theorem theta_algebraMap (x : Acris p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Acris.theta p R x) := lift_algebraMap _ _ x

/- English proof (translation)
The claim follows from `RingHom.congr_fun (hom_ext (f := (theta p S).comp (map p f)) (g := (awayMap p f).comp (theta p R)) (by simp [Acris.theta_map])) x`.
-/
theorem theta_map (f : R →+* S) (x : BcrisPlus p R) :
    theta p S (map p f x) = awayMap p f (theta p R x) :=
  RingHom.congr_fun (hom_ext (f := (theta p S).comp (map p f)) (g := (awayMap p f).comp (theta p R))
    (by simp [Acris.theta_map])) x

end BcrisPlus

end Reformulated.AutPerF
