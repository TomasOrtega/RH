import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.SlopePhiModule
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def piB : T.Bˣ := (IsLocalization.Away.algebraMap_isUnit T.π).unit

/- English proof (translation)
The claim follows from `IsUnit.unit_spec _`.
-/
theorem piB_val : (T.piB : T.B) = algebraMap Γ T.B T.π := IsUnit.unit_spec _

/- English proof (translation)
Establish `hex : ∃ n, T.coeff x n ≠ 0`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Conclude with `hx (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))`. Use `set j := Nat.find hex`.

Establish `hj : T.coeff x j ≠ 0` using `Nat.find_spec hex`. Establish `hlt : ∀ i < j, T.coeff x i = 0` using `fun i hi => by`. Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hex hi h`. Establish `hps : T.partialSum x j = 0`.

Rewrite using `[partialSum, T.finSum_congr (b := 0) hlt]`. Simplify using `[finSum]`. Use `⟨j, T.tail^[j] x, ?_, ?_⟩` and prove the remaining obligations. Use `T.sub_partialSum x j` as an intermediate fact. Rewrite `this` using `[hps, sub_zero]`. Then use the resulting hypothesis.

Rewrite using `[← coeff_zero, coeff_tail_iterate, zero_add]`. Conclude with `hj`.
-/
theorem exists_pi_pow_mul_red_ne {x : Γ} (hx : x ≠ 0) :
    ∃ (j : ℕ) (y : Γ), x = T.π ^ j * y ∧ T.red y ≠ 0 := by
  classical
  have hex : ∃ n, T.coeff x n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))
  set j := Nat.find hex
  have hj : T.coeff x j ≠ 0 := Nat.find_spec hex
  have hlt : ∀ i < j, T.coeff x i = 0 := fun i hi => by
    by_contra h; exact Nat.find_min hex hi h
  have hps : T.partialSum x j = 0 := by
    rw [partialSum, T.finSum_congr (b := 0) hlt]; simp [finSum]
  refine ⟨j, T.tail^[j] x, ?_, ?_⟩
  · have := T.sub_partialSum x j
    rwa [hps, sub_zero] at this
  · rw [← coeff_zero, coeff_tail_iterate, zero_add]; exact hj

/- English proof (translation)
Break down `k with m | m` into its components or cases. Rewrite using `[Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, piB_val, ← map_pow, ← map_mul, coeffB_algebraMap]`. Use `T.zcoeff_π_pow_mul m y (n - m)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hb : ((T.piB ^ Int.negSucc m : T.Bˣ) : T.B) * algebraMap Γ T.B y * algebraMap Γ T.B T.π ^ (m + 1) = algebraMap Γ T.B y`.

Rewrite using `[zpow_negSucc, ← piB_val, ← Units.val_pow_eq_pow_val, mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`. Rewrite using `[T.coeffB_eq hb]`. Use `congr 1`.
-/
theorem coeffB_piB_zpow_mul (k : ℤ) (y : Γ) (n : ℤ) :
    T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n = T.zcoeff y (n - k) := by
  rcases k with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, piB_val, ← map_pow,
      ← map_mul, coeffB_algebraMap]
    have := T.zcoeff_π_pow_mul m y (n - m)
    rwa [sub_add_cancel] at this
  · have hb : ((T.piB ^ Int.negSucc m : T.Bˣ) : T.B) * algebraMap Γ T.B y *
        algebraMap Γ T.B T.π ^ (m + 1) = algebraMap Γ T.B y := by
      rw [zpow_negSucc, ← piB_val, ← Units.val_pow_eq_pow_val, mul_comm, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [T.coeffB_eq hb]
    congr 1

def ordB (b : T.B) : ℤ := sInf {n | T.coeffB b n ≠ 0}

/- English proof (translation)
Establish `hS : ∀ n, n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0} ↔ T.zcoeff y (n - k) ≠ 0` using `fun n => by`. Rewrite using `[Set.mem_ofPred_eq, coeffB_piB_zpow_mul]`. Establish `hk : k ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0}`. Rewrite using `[hS, sub_self]`. Rewrite using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, zcoeff_natCast, coeff_zero]` and apply the resulting hypothesis.

Establish `hlow : ∀ n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0}, k ≤ n`. Introduce `n hn`. Rewrite `hn` using `[hS]`. Assume the negation of the conclusion as `h`. Conclude with `hn (T.zcoeff_of_neg y (by omega))`.

Conclude with `le_antisymm (csInf_le ⟨k, hlow⟩ hk) (le_csInf ⟨k, hk⟩ hlow)`.
-/
theorem ordB_piB_zpow_mul (k : ℤ) {y : Γ} (hy : T.red y ≠ 0) :
    T.ordB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) = k := by
  have hS : ∀ n, n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0} ↔
      T.zcoeff y (n - k) ≠ 0 := fun n => by
    rw [Set.mem_ofPred_eq, coeffB_piB_zpow_mul]
  have hk : k ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0} := by
    rw [hS, sub_self]
    rwa [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, zcoeff_natCast, coeff_zero]
  have hlow : ∀ n ∈ {n | T.coeffB ((T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y) n ≠ 0}, k ≤ n := by
    intro n hn
    rw [hS] at hn
    by_contra h
    exact hn (T.zcoeff_of_neg y (by omega))
  exact le_antisymm (csInf_le ⟨k, hlow⟩ hk) (le_csInf ⟨k, hk⟩ hlow)

/- English proof (translation)
Take `⟨N, x, hx⟩` from `IsLocalization.Away.surj T.π b`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hb (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))`. Take `⟨j, y, rfl, hy⟩` from `T.exists_pi_pow_mul_red_ne hx0`. Use `⟨(j : ℤ) - N, y, ?_, hy⟩` and prove the remaining obligations. Establish `hN : ((T.piB ^ (N : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ N`.

Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, piB_val]`. Establish `hj : ((T.piB ^ (j : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ j`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, piB_val]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]`.

Use `_ = (b * algebraMap Γ T.B T.π ^ N) * (T.piB ^ (-(N : ℤ)) : T.Bˣ) := by`. Rewrite using `[Units.val_mul, hN]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[hx, map_mul, map_pow, ← hj, mul_comm, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_eq_sub]`.
-/
theorem exists_piB_zpow_mul {b : T.B} (hb : b ≠ 0) :
    ∃ (k : ℤ) (y : Γ), b = (T.piB ^ k : T.Bˣ) * algebraMap Γ T.B y ∧ T.red y ≠ 0 := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hx0 : x ≠ 0 := by rintro rfl; exact hb (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  obtain ⟨j, y, rfl, hy⟩ := T.exists_pi_pow_mul_red_ne hx0
  refine ⟨(j : ℤ) - N, y, ?_, hy⟩
  have hN : ((T.piB ^ (N : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ N := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  have hj : ((T.piB ^ (j : ℤ) : T.Bˣ) : T.B) = algebraMap Γ T.B T.π ^ j := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, piB_val]
  calc b = b * ((T.piB ^ (N : ℤ) : T.Bˣ) * (T.piB ^ (-(N : ℤ)) : T.Bˣ) : T.Bˣ) := by
        rw [← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
    _ = (b * algebraMap Γ T.B T.π ^ N) * (T.piB ^ (-(N : ℤ)) : T.Bˣ) := by
        rw [Units.val_mul, hN]; ring
    _ = _ := by
        rw [hx, map_mul, map_pow, ← hj, mul_comm, ← mul_assoc, ← Units.val_mul, ← zpow_add,
          neg_add_eq_sub]

/- English proof (translation)
Take `⟨k, y, rfl, hy⟩` from `T.exists_piB_zpow_mul hb`. Take `⟨l, z, rfl, hz⟩` from `T.exists_piB_zpow_mul hc`. Establish `e : ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y * (((T.piB ^ l : T.Bˣ) : T.B) * algebraMap Γ T.B z) = ((T.piB ^ (k + l) : T.Bˣ) : T.B) * algebraMap Γ T.B (y * z)`. Rewrite using `[zpow_add, Units.val_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ hz, T.ordB_piB_zpow_mul _ (by rw [map_mul]; exact mul_ne_zero hy hz)]`.
-/
theorem ordB_mul {b c : T.B} (hb : b ≠ 0) (hc : c ≠ 0) : T.ordB (b * c) = T.ordB b + T.ordB c := by
  obtain ⟨k, y, rfl, hy⟩ := T.exists_piB_zpow_mul hb
  obtain ⟨l, z, rfl, hz⟩ := T.exists_piB_zpow_mul hc
  have e : ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y * (((T.piB ^ l : T.Bˣ) : T.B) *
      algebraMap Γ T.B z) = ((T.piB ^ (k + l) : T.Bˣ) : T.B) * algebraMap Γ T.B (y * z) := by
    rw [zpow_add, Units.val_mul, map_mul]; ring
  rw [e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ hz,
    T.ordB_piB_zpow_mul _ (by rw [map_mul]; exact mul_ne_zero hy hz)]

namespace TeichFrob

variable {T} (F : T.TeichFrob)

/- English proof (translation)
Take `⟨k, y, rfl, hy⟩` from `T.exists_piB_zpow_mul hb`. Take `⟨v, -, huv, -⟩` from `F.exists_inv_u`. Use `set uU : Γˣ := ⟨F.u, v, huv, by rw [mul_comm]; exact huv⟩`. Establish `hpi : Units.map (F.toB : T.B →* T.B) T.piB = T.piB * Units.map (algebraMap Γ T.B : Γ →* T.B) uU`. Use `ext`.

Simplify using `only [Units.coe_map, Units.val_mul, MonoidHom.coe_coe]`. Rewrite using `[piB_val]`. Use `show F.toB (algebraMap Γ T.B T.π) = _`. Rewrite using `[F.toB_algebraMap, F.φ_π, map_mul]`. Establish `e : F.toB (((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y) = ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B (((uU ^ k : Γˣ) : Γ) * F.φ y)`.

Establish `h1 : F.toB (((T.piB ^ k : T.Bˣ) : T.B)) = ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B ((uU ^ k : Γˣ) : Γ)`. Use `congrArg Units.val (congrArg (· ^ k) hpi)` as an intermediate fact. Simplify using `only [← map_zpow, Units.coe_map, mul_zpow, Units.val_mul, MonoidHom.coe_coe] at this`. Conclude with `this`. Rewrite using `[map_mul, h1, F.toB_algebraMap, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu : T.red ((uU ^ k : Γˣ) : Γ) ≠ 0`. Use `(Units.map (T.red : Γ →* L) (uU ^ k)).ne_zero` as an intermediate fact. Rewrite `this` using `[Units.coe_map, MonoidHom.coe_coe]`. Then use the resulting hypothesis. Rewrite using `[e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ (by`.

Rewrite using `[map_mul, F.red_φ]`. Conclude with `mul_ne_zero hu (pow_ne_zero _ hy))]`.
-/
theorem ordB_toB {b : T.B} (hb : b ≠ 0) : T.ordB (F.toB b) = T.ordB b := by
  obtain ⟨k, y, rfl, hy⟩ := T.exists_piB_zpow_mul hb
  obtain ⟨v, -, huv, -⟩ := F.exists_inv_u
  set uU : Γˣ := ⟨F.u, v, huv, by rw [mul_comm]; exact huv⟩
  have hpi : Units.map (F.toB : T.B →* T.B) T.piB =
      T.piB * Units.map (algebraMap Γ T.B : Γ →* T.B) uU := by
    ext
    simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
    rw [piB_val]
    show F.toB (algebraMap Γ T.B T.π) = _
    rw [F.toB_algebraMap, F.φ_π, map_mul]
  have e : F.toB (((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B y) =
      ((T.piB ^ k : T.Bˣ) : T.B) * algebraMap Γ T.B (((uU ^ k : Γˣ) : Γ) * F.φ y) := by
    have h1 : F.toB (((T.piB ^ k : T.Bˣ) : T.B)) = ((T.piB ^ k : T.Bˣ) : T.B) *
        algebraMap Γ T.B ((uU ^ k : Γˣ) : Γ) := by
      have := congrArg Units.val (congrArg (· ^ k) hpi)
      simp only [← map_zpow, Units.coe_map, mul_zpow, Units.val_mul, MonoidHom.coe_coe] at this
      exact this
    rw [map_mul, h1, F.toB_algebraMap, map_mul]; ring
  have hu : T.red ((uU ^ k : Γˣ) : Γ) ≠ 0 := by
    have := (Units.map (T.red : Γ →* L) (uU ^ k)).ne_zero
    rwa [Units.coe_map, MonoidHom.coe_coe] at this
  rw [e, T.ordB_piB_zpow_mul _ hy, T.ordB_piB_zpow_mul _ (by
    rw [map_mul, F.red_φ]; exact mul_ne_zero hu (pow_ne_zero _ hy))]

end TeichFrob

variable [CompleteSpace L]

def unitPre (x : T.RobbaTildeˣ) : T.Edag := (T.mem_range_of_isUnit x.isUnit).choose

/- English proof (translation)
The claim follows from `(T.mem_range_of_isUnit x.isUnit).choose_spec`.
-/
theorem unitPre_spec (x : T.RobbaTildeˣ) : T.edagToTilde (T.unitPre x) = x :=
  (T.mem_range_of_isUnit x.isUnit).choose_spec

/- English proof (translation)
Introduce `h`. Establish `h0 : T.unitPre x = 0` using `Subtype.ext h`. Use `T.unitPre_spec x` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `x.ne_zero this.symm`.
-/
theorem unitPre_ne_zero (x : T.RobbaTildeˣ) : ((T.unitPre x : T.Edag) : T.B) ≠ 0 := by
  intro h
  have h0 : T.unitPre x = 0 := Subtype.ext h
  have := T.unitPre_spec x
  rw [h0, map_zero] at this
  exact x.ne_zero this.symm

def tildeOrd (x : T.RobbaTildeˣ) : ℤ := T.ordB (T.unitPre x : T.Edag)

/- English proof (translation)
Establish `: T.unitPre x = b` using `T.edagToTilde_injective ((T.unitPre_spec x).trans h.symm)`. Rewrite using `[tildeOrd, this]`.
-/
theorem tildeOrd_eq {x : T.RobbaTildeˣ} {b : T.Edag} (h : T.edagToTilde b = x) :
    T.tildeOrd x = T.ordB (b : T.B) := by
  have : T.unitPre x = b := T.edagToTilde_injective ((T.unitPre_spec x).trans h.symm)
  rw [tildeOrd, this]

/- English proof (translation)
Rewrite using `[T.tildeOrd_eq (b := T.unitPre x * T.unitPre y) (by`. Rewrite using `[map_mul, T.unitPre_spec, T.unitPre_spec, Units.val_mul]), Subring.coe_mul]`. Conclude with `T.ordB_mul (T.unitPre_ne_zero x) (T.unitPre_ne_zero y)`.
-/
theorem tildeOrd_mul (x y : T.RobbaTildeˣ) : T.tildeOrd (x * y) = T.tildeOrd x + T.tildeOrd y := by
  rw [T.tildeOrd_eq (b := T.unitPre x * T.unitPre y) (by
    rw [map_mul, T.unitPre_spec, T.unitPre_spec, Units.val_mul]), Subring.coe_mul]
  exact T.ordB_mul (T.unitPre_ne_zero x) (T.unitPre_ne_zero y)

namespace TeichFrob

variable {T} (F : T.TeichFrob)

/- English proof (translation)
Rewrite using `[T.tildeOrd_eq (b := F.edagEquiv (T.unitPre x)) (by`. Rewrite using `[← F.tildeFrob_edagToTilde, T.unitPre_spec]`. Use the proof step `rfl), F.edagEquiv_apply,`. Use the proof step `F.ordB_toB (T.unitPre_ne_zero x)]`. Both sides reduce to the same expression.
-/
theorem tildeOrd_map (x : T.RobbaTildeˣ) :
    T.tildeOrd (Units.map (F.tildeFrob : T.RobbaTilde →* T.RobbaTilde) x) = T.tildeOrd x := by
  rw [T.tildeOrd_eq (b := F.edagEquiv (T.unitPre x)) (by
    rw [← F.tildeFrob_edagToTilde, T.unitPre_spec]; rfl), F.edagEquiv_apply,
    F.ordB_toB (T.unitPre_ne_zero x)]
  rfl

def tildeUnitOrd : PhiModule.UnitOrd T.RobbaTilde F.tildeFrob where
  ord := T.tildeOrd
  map_mul := T.tildeOrd_mul
  map_phi := F.tildeOrd_map

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
