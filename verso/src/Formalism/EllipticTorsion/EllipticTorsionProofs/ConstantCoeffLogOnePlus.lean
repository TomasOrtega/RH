import Formalism.EllipticTorsion.Statement

noncomputable section

namespace Formalism.ELL.EulerSeries

open Formalism.G Formalism.ELL

variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]

def eulFun (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => (d.degree : K) * MvPowerSeries.coeff d F

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_eulFun (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (eulFun F) = (d.degree : K) * MvPowerSeries.coeff d F := rfl

def eulLin : MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun := eulFun
  map_add' F G := by
    ext d
    simp only [coeff_eulFun, map_add, mul_add]
  map_smul' c F := by
    ext d
    simp only [coeff_eulFun, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[smul_eq_mul, smul_eq_mul, mul_comm G, map_add, coeff_eulFun, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[coeff_eulFun, coeff_eulFun, ← hp, map_add, Nat.cast_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eulFun_mul (F G : MvPowerSeries σ K) :
    eulFun (F * G) = F • eulFun G + G • eulFun F := by
  ext d
  rw [smul_eq_mul, smul_eq_mul, mul_comm G, map_add, coeff_eulFun, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_eulFun, coeff_eulFun, ← hp, map_add, Nat.cast_add]
  ring

def eul : Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K) :=
  Derivation.mk' eulLin fun a b => eulFun_mul a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eul_apply (F : MvPowerSeries σ K) : eul F = eulFun F := rfl

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[map_zero]`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Conclude with `h0`. Establish `h1` using `congrArg (MvPowerSeries.coeff d) h`. Rewrite `h1` using `[coeff_eulFun, map_zero]`. Establish `hdeg : ((d.degree : ℕ) : K) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`.

Conclude with `fun h' => hd ((Finsupp.degree_eq_zero_iff d).mp h')`. Conclude with `(mul_eq_zero.mp h1).resolve_left hdeg`.
-/
theorem eq_zero_of_eulFun (F : MvPowerSeries σ K) (h0 : MvPowerSeries.constantCoeff F = 0)
    (h : eulFun F = 0) : F = 0 := by
  ext d
  rw [map_zero]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h1 := congrArg (MvPowerSeries.coeff d) h
    rw [coeff_eulFun, map_zero] at h1
    have hdeg : ((d.degree : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact fun h' => hd ((Finsupp.degree_eq_zero_iff d).mp h')
    exact (mul_eq_zero.mp h1).resolve_left hdeg

def Agree (N : ℕ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d F = MvPowerSeries.coeff d G

/- English proof (translation)
Introduce `d hd`. Rewrite using `[MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hdeg` using `congrArg Finsupp.degree hp`.

Rewrite `hdeg` using `[map_add]`. Rewrite using `[h p.1 (by omega)]`.
-/
theorem Agree.mul_right {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G)
    (H : MvPowerSeries σ K) : Agree N (F * H) (G * H) := by
  intro d hd
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add] at hdeg
  rw [h p.1 (by omega)]

/- English proof (translation)
Introduce `d hd`. Rewrite using `[coeff_eulFun, coeff_eulFun, h d hd]`.
-/
theorem Agree.eulFun {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G) :
    Agree N (eulFun F) (eulFun G) := by
  intro d hd
  rw [coeff_eulFun, coeff_eulFun, h d hd]

/- English proof (translation)
The claim follows from `| 0, d, hd => absurd hd (Nat.not_lt_zero _) | n + 1, d, hd => by rw [pow_succ', MvPowerSeries.coeff_mul] refine Finset.sum_eq_zero fun p hp => ?_ rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp have hdeg := congrArg Finsupp.degree hp rw [map_add] at hdeg by_cases h1 : p.1 = 0 …`.
-/
theorem coeff_pow_eq_zero {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree < n → MvPowerSeries.coeff d (f ^ n) = 0
  | 0, d, hd => absurd hd (Nat.not_lt_zero _)
  | n + 1, d, hd => by
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg := congrArg Finsupp.degree hp
    rw [map_add] at hdeg
    by_cases h1 : p.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · have : 0 < p.1.degree :=
        Nat.pos_of_ne_zero (fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h))
      rw [coeff_pow_eq_zero hf n p.2 (by omega), mul_zero]

def truncLog (N : ℕ) (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  ∑ n ∈ Finset.range N, PowerSeries.coeff n (PowerSeries.log K) • f ^ n

/- English proof (translation)
Introduce `d hd`. Rewrite using `[logOnePlus, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), truncLog, map_sum]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Introduce `n hn`. Rewrite `hn` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[coeff_pow_eq_zero hf n d (by omega), smul_zero]`.
-/
theorem agree_truncLog {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) : Agree N (logOnePlus f) (truncLog N f) := by
  intro d hd
  rw [logOnePlus, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    truncLog, map_sum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    rw [coeff_pow_eq_zero hf n d (by omega), smul_zero]

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k)]`. Simplify using `only [map_div₀, map_pow, map_neg, map_one, map_natCast]`. Establish `: ((k + 1 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_log_succ_mul (k : ℕ) :
    PowerSeries.coeff (k + 1) (PowerSeries.log K) * ((k + 1 : ℕ) : K) = (-1) ^ k := by
  rw [PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k)]
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  have : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp
  ring

/- English proof (translation)
Establish `h0 : PowerSeries.coeff 0 (PowerSeries.log K) = 0` using `by simp`. Rewrite using `[← eul_apply, truncLog, map_sum, Finset.sum_range_succ', h0, zero_smul, map_zero, add_zero, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, Algebra.smul_def, nsmul_eq_mul, smul_eq_mul, eul_apply, neg_pow]`. Establish `h1 : algebraMap K (MvPowerSeries σ K) (PowerSeries.coeff (k + 1) (PowerSeries.log K)) * ((k + 1 : ℕ) : MvPowerSeries σ K) = (-1) ^ k`.

Rewrite using `[← map_natCast (algebraMap K (MvPowerSeries σ K)), ← map_mul, coeff_log_succ_mul, map_pow, map_neg, map_one]`. Take the linear combination `(f ^ k * eulFun f) * h1`.
-/
theorem eul_truncLog (f : MvPowerSeries σ K) (M : ℕ) :
    eulFun (truncLog (M + 1) f) = (∑ k ∈ Finset.range M, (-f) ^ k) * eulFun f := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.log K) = 0 := by simp
  rw [← eul_apply, truncLog, map_sum, Finset.sum_range_succ', h0, zero_smul, map_zero,
    add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, Algebra.smul_def,
    nsmul_eq_mul, smul_eq_mul, eul_apply, neg_pow]
  have h1 : algebraMap K (MvPowerSeries σ K) (PowerSeries.coeff (k + 1) (PowerSeries.log K)) *
      ((k + 1 : ℕ) : MvPowerSeries σ K) = (-1) ^ k := by
    rw [← map_natCast (algebraMap K (MvPowerSeries σ K)), ← map_mul, coeff_log_succ_mul,
      map_pow, map_neg, map_one]
  linear_combination (f ^ k * eulFun f) * h1

/- English proof (translation)
Use extensionality with `d`. Establish `hA` using `((agree_truncLog hf (d.degree + 2)).eulFun).mul_right (1 + f) d (by omega)`. Rewrite using `[hA, show d.degree + 2 = (d.degree + 1) + 1 from rfl, eul_truncLog]`. Establish `hg` using `geom_sum_mul (-f) (d.degree + 1)`. Establish `hE : (∑ k ∈ Finset.range (d.degree + 1), (-f) ^ k) * eulFun f * (1 + f) = eulFun f - (-f) ^ (d.degree + 1) * eulFun f`.

Take the linear combination `(-(eulFun f)) * hg`. Rewrite using `[hE, map_sub]`. Establish `hz : Agree (d.degree + 1) ((-f) ^ (d.degree + 1)) 0`. Introduce `e he`. Rewrite using `[map_zero]`.

Conclude with `coeff_pow_eq_zero (by rw [map_neg, hf, neg_zero]) _ e he`. Use `hz.mul_right (eulFun f) d (by omega)` as an intermediate fact. Rewrite using `[this, zero_mul, map_zero, sub_zero]`.
-/
theorem eul_log_mul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    eulFun (logOnePlus f) * (1 + f) = eulFun f := by
  ext d
  have hA := ((agree_truncLog hf (d.degree + 2)).eulFun).mul_right (1 + f) d (by omega)
  rw [hA, show d.degree + 2 = (d.degree + 1) + 1 from rfl, eul_truncLog]
  have hg := geom_sum_mul (-f) (d.degree + 1)
  have hE : (∑ k ∈ Finset.range (d.degree + 1), (-f) ^ k) * eulFun f * (1 + f) =
      eulFun f - (-f) ^ (d.degree + 1) * eulFun f := by
    linear_combination (-(eulFun f)) * hg
  rw [hE, map_sub]
  have hz : Agree (d.degree + 1) ((-f) ^ (d.degree + 1)) 0 := by
    intro e he
    rw [map_zero]
    exact coeff_pow_eq_zero (by rw [map_neg, hf, neg_zero]) _ e he
  have := hz.mul_right (eulFun f) d (by omega)
  rw [this, zero_mul, map_zero, sub_zero]

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero hf _ PowerSeries.constantCoeff_log`.
-/
theorem constantCoeff_logOnePlus {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (logOnePlus f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hf _ PowerSeries.constantCoeff_log

/- English proof (translation)
Apply `eq_zero_of_eulFun _ (constantCoeff_logOnePlus (map_zero _))` to reduce the goal to its premises. Use `eul_log_mul (map_zero (MvPowerSeries.constantCoeff (σ := σ) (R := K)))` as an intermediate fact. Rewrite `this` using `[add_zero, mul_one, ← eul_apply 0, map_zero]`. Then use the resulting hypothesis.
-/
theorem log_zero : logOnePlus (0 : MvPowerSeries σ K) = 0 := by
  apply eq_zero_of_eulFun _ (constantCoeff_logOnePlus (map_zero _))
  have := eul_log_mul (map_zero (MvPowerSeries.constantCoeff (σ := σ) (R := K)))
  rwa [add_zero, mul_one, ← eul_apply 0, map_zero] at this

/- English proof (translation)
Establish `hh : MvPowerSeries.constantCoeff (f + g + f * g) = 0`. Simplify using `only [map_add, map_mul, hf, hg, add_zero, mul_zero]`. Establish `hu : IsUnit (1 + (f + g + f * g))`. Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, map_add, hh, map_one, add_zero]`. Conclude with `isUnit_one`.

Establish `e1` using `eul_log_mul hf`. Establish `e2` using `eul_log_mul hg`. Establish `e3` using `eul_log_mul hh`. Establish `hD : eulFun (f + g + f * g) = eulFun f + eulFun g + (f * eulFun g + g * eulFun f)` using `by show eul (f + g + f * g) = eul f + eul g + (f * eul g + g * eul f)`. Rewrite using `[map_add, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Establish `key : eulFun (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) = 0`. Rewrite using `[← hu.mul_left_inj, zero_mul]`. Use `show eul (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) * _ = 0`. Rewrite using `[map_sub, map_add, eul_apply, eul_apply, eul_apply]`. Take the linear combination `(1 + g) * e1 + (1 + f) * e2 - e3 - hD`.

Use `eq_zero_of_eulFun _ (by` as an intermediate fact. Rewrite using `[map_sub, map_add, constantCoeff_logOnePlus hf, constantCoeff_logOnePlus hg, constantCoeff_logOnePlus hh, add_zero, sub_zero]) key`. Conclude with `sub_eq_zero.mp this`.
-/
theorem log_add {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    logOnePlus f + logOnePlus g = logOnePlus (f + g + f * g) := by
  have hh : MvPowerSeries.constantCoeff (f + g + f * g) = 0 := by
    simp only [map_add, map_mul, hf, hg, add_zero, mul_zero]
  have hu : IsUnit (1 + (f + g + f * g)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hh, map_one, add_zero]
    exact isUnit_one
  have e1 := eul_log_mul hf
  have e2 := eul_log_mul hg
  have e3 := eul_log_mul hh
  have hD : eulFun (f + g + f * g) = eulFun f + eulFun g + (f * eulFun g + g * eulFun f) := by
    show eul (f + g + f * g) = eul f + eul g + (f * eul g + g * eul f)
    rw [map_add, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have key : eulFun (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) = 0 := by
    rw [← hu.mul_left_inj, zero_mul]
    show eul (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) * _ = 0
    rw [map_sub, map_add, eul_apply, eul_apply, eul_apply]
    linear_combination (1 + g) * e1 + (1 + f) * e2 - e3 - hD
  have := eq_zero_of_eulFun _ (by
    rw [map_sub, map_add, constantCoeff_logOnePlus hf, constantCoeff_logOnePlus hg,
      constantCoeff_logOnePlus hh, add_zero, sub_zero]) key
  exact sub_eq_zero.mp this

variable [IsUltrametricDist K]

/- English proof (translation)
Introduce `d` and use `by rw [MvPowerSeries.coeff_map] exact (MvPowerSeries.coeff d F).2`.
-/
theorem integral_map (F : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype F) := fun d => by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d F).2

/- English proof (translation)
Establish `hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K` using `fun n => hf n`. Establish `hg' : ∀ n, MvPowerSeries.coeff n g ∈ unitBall K` using `fun n => hg n`. Use `integral_map (f.toSubring _ hf' + g.toSubring _ hg' + f.toSubring _ hf' * g.toSubring _ hg')` as an intermediate fact. Simplify `this` using `only [map_add, map_mul, MvPowerSeries.map_toSubring]`.
-/
theorem integral_add_mul {f g : MvPowerSeries σ K} (hf : IntegralMv f) (hg : IntegralMv g) :
    IntegralMv (f + g + f * g) := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  have hg' : ∀ n, MvPowerSeries.coeff n g ∈ unitBall K := fun n => hg n
  have := integral_map (f.toSubring _ hf' + g.toSubring _ hg' +
    f.toSubring _ hf' * g.toSubring _ hg')
  simpa only [map_add, map_mul, MvPowerSeries.map_toSubring] using this

/- English proof (translation)
Establish `hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K` using `fun n => hf n`. Use `set f' := f.toSubring _ hf' with hf'def`. Establish `hc : MvPowerSeries.constantCoeff f' = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hf'def, MvPowerSeries.constantCoeff_toSubring, hf0]`.

Both sides reduce to the same expression. Establish `hu : IsUnit (1 + f')`. Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, map_add, hc, map_one, add_zero]`. Conclude with `isUnit_one`. Take `⟨v, hv⟩` from `hu.exists_right_inv`.

Use `⟨MvPowerSeries.map (unitBall K).subtype (v - 1), ?_, integral_map _, ?_⟩` and prove the remaining obligations. Establish `hprod` using `congrArg (MvPowerSeries.map (unitBall K).subtype) hv`. Rewrite `hprod` using `[map_mul, map_add, map_one, MvPowerSeries.map_toSubring]`. Establish `h2` using `congrArg MvPowerSeries.constantCoeff hprod`. Simplify using `only [map_mul, map_add, map_one, hf0, add_zero, one_mul] at h2`.

Simplify using `only [map_sub, h2, map_one, sub_self]`. Establish `hprod` using `congrArg (MvPowerSeries.map (unitBall K).subtype) hv`. Rewrite `hprod` using `[map_mul, map_add, map_one, MvPowerSeries.map_toSubring]`. Rewrite using `[map_sub, map_one]`. Take the linear combination `hprod`.
-/
theorem exists_inv {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : IntegralMv f) :
    ∃ h : MvPowerSeries σ K, MvPowerSeries.constantCoeff h = 0 ∧ IntegralMv h ∧
      f + h + f * h = 0 := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  set f' := f.toSubring _ hf' with hf'def
  have hc : MvPowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [hf'def, MvPowerSeries.constantCoeff_toSubring, hf0]
    rfl
  have hu : IsUnit (1 + f') := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hc, map_one, add_zero]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨MvPowerSeries.map (unitBall K).subtype (v - 1), ?_, integral_map _, ?_⟩
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    have h2 := congrArg MvPowerSeries.constantCoeff hprod
    simp only [map_mul, map_add, map_one, hf0, add_zero, one_mul] at h2
    simp only [map_sub, h2, map_one, sub_self]
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    rw [map_sub, map_one]
    linear_combination hprod

end Formalism.ELL.EulerSeries

namespace Formalism.ELL

/- English proof (translation)
Introduce `K _ _ _ σ`. Use `⟨⟨0, map_zero _, fun d => by simp, EulerSeries.log_zero.symm⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `G H ⟨f, hf0, hfi, rfl⟩ ⟨g, hg0, hgi, rfl⟩`. Conclude with `⟨f + g + f * g, by simp only [map_add, map_mul, hf0, hg0, add_zero, mul_zero], EulerSeries.integral_add_mul hfi hgi, EulerSeries.log_add hf0 hg0⟩`. Introduce and unpack `G ⟨f, hf0, hfi, rfl⟩`.

Take `⟨h, hh0, hhi, hfh⟩` from `EulerSeries.exists_inv hf0 hfi`. Use `⟨h, hh0, hhi, ?_⟩` and prove the remaining obligations. Use `EulerSeries.log_add hf0 hh0` as an intermediate fact. Rewrite `this` using `[hfh, EulerSeries.log_zero]`. Take the linear combination `-this`.
-/
theorem N_additive_subgroup : Formalism.ELL.NAddSubgroup := by
  intro K _ _ _ σ
  classical
  refine ⟨⟨0, map_zero _, fun d => by simp, EulerSeries.log_zero.symm⟩, ?_, ?_⟩
  · rintro G H ⟨f, hf0, hfi, rfl⟩ ⟨g, hg0, hgi, rfl⟩
    exact ⟨f + g + f * g, by simp only [map_add, map_mul, hf0, hg0, add_zero, mul_zero],
      EulerSeries.integral_add_mul hfi hgi, EulerSeries.log_add hf0 hg0⟩
  · rintro G ⟨f, hf0, hfi, rfl⟩
    obtain ⟨h, hh0, hhi, hfh⟩ := EulerSeries.exists_inv hf0 hfi
    refine ⟨h, hh0, hhi, ?_⟩
    have := EulerSeries.log_add hf0 hh0
    rw [hfh, EulerSeries.log_zero] at this
    linear_combination -this

end Formalism.ELL
