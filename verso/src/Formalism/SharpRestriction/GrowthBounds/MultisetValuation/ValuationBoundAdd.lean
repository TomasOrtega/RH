import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PlaceB
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap (K0 p) Y.Kc)]`. Conclude with `(map_ne_zero (algebraMap (K0 p) Y.Kc)).mpr (WittVector.FractionRing.p_nonzero p (kb p))`.
-/
theorem pKc_ne : (p : Y.Kc) ≠ 0 := by
  rw [← map_natCast (algebraMap (K0 p) Y.Kc)]
  exact (map_ne_zero (algebraMap (K0 p) Y.Kc)).mpr (WittVector.FractionRing.p_nonzero p (kb p))

include Y in
/- English proof (translation)
Introduce `h`. Apply `pKc_ne Y` to reduce the goal to its premises. Rewrite using `[← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]`.
-/
theorem pK_ne : (p : X.G.Kf) ≠ 0 := by
  intro h
  apply pKc_ne Y
  rw [← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]

/- English proof (translation)
Introduce `a b hb _`. Rewrite using `[zero_pow hb.ne', zero_mul]`. Conclude with `Y.Oc.zero_mem`.
-/
theorem geC_zero (g : ℝ) : Y.geC 0 g := by
  intro a b hb _
  rw [zero_pow hb.ne', zero_mul]
  exact Y.Oc.zero_mem

/- English proof (translation)
Introduce `a b hb hab`. Rewrite using `[neg_pow, mul_assoc]`. Conclude with `Y.Oc.mul_mem (Y.Oc.pow_mem (Y.Oc.neg_mem Y.Oc.one_mem) _) (h a b hb hab)`.
-/
theorem geC_neg {x : Y.Kc} {g : ℝ} (h : Y.geC x g) : Y.geC (-x) g := by
  intro a b hb hab
  rw [neg_pow, mul_assoc]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (Y.Oc.neg_mem Y.Oc.one_mem) _) (h a b hb hab)

/- English proof (translation)
Introduce `a b hb hab`. Establish `hp` using `pKc_ne Y`. Establish `hx'` using `hx (a + k * b) b hb (by push_cast; nlinarith)`. Establish `e : (y * x) ^ b * (p : Y.Kc) ^ (-a) = (y * (p : Y.Kc) ^ k) ^ b * (x ^ b * (p : Y.Kc) ^ (-(a + k * b)))`. Establish `h1 : (p : Y.Kc) ^ (-a) = ((p : Y.Kc) ^ k) ^ b * (p : Y.Kc) ^ (-(a + k * b))`.

Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Y.Oc.mul_mem (Y.Oc.pow_mem hy _) hx'`.
-/
theorem geC_mul_shift {x y : Y.Kc} {g : ℝ} (k : ℤ) (hx : Y.geC x g) (hy : y * (p : Y.Kc) ^ k ∈ Y.Oc) :
    Y.geC (y * x) (g - k) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hx' := hx (a + k * b) b hb (by push_cast; nlinarith)
  have e : (y * x) ^ b * (p : Y.Kc) ^ (-a) =
      (y * (p : Y.Kc) ^ k) ^ b * (x ^ b * (p : Y.Kc) ^ (-(a + k * b))) := by
    have h1 : (p : Y.Kc) ^ (-a) = ((p : Y.Kc) ^ k) ^ b * (p : Y.Kc) ^ (-(a + k * b)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp]
      congr 1
      ring
    rw [h1]
    ring
  rw [e]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem hy _) hx'

/- English proof (translation)
Introduce `a b hb hab`. Rewrite using `[mul_pow, mul_assoc]`. Conclude with `Y.Oc.mul_mem (Y.Oc.pow_mem hy _) (hx a b hb hab)`.
-/
theorem geC_mul_Oc {x y : Y.Kc} {g : ℝ} (hx : Y.geC x g) (hy : y ∈ Y.Oc) : Y.geC (y * x) g := by
  intro a b hb hab
  rw [mul_pow, mul_assoc]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem hy _) (hx a b hb hab)

/- English proof (translation)
Establish `e : x + y = (x / y + 1) * y`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `geC_mul_Oc Y hy (Y.Oc.add_mem h Y.Oc.one_mem)`.
-/
theorem valuation_bound_add {x y : Y.Kc} {g : ℝ} (hy0 : y ≠ 0) (h : x / y ∈ Y.Oc) (hy : Y.geC y g) : Y.geC (x + y) g := by
  have e : x + y = (x / y + 1) * y := by
    field_simp
  rw [e]
  exact geC_mul_Oc Y hy (Y.Oc.add_mem h Y.Oc.one_mem)

/- English proof (translation)
Distinguish the cases in `hy0 : y = 0`. Rewrite using `[hy0, add_zero]`. Conclude with `hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, zero_add]`.

Conclude with `hy`. Break down `Y.Oc_val (x / y) with h | h` into its components or cases. Conclude with `valuation_bound_add Y hy0 h hy`. Rewrite using `[add_comm]`. Use `valuation_bound_add Y hx0 ?_ hx` and prove the remaining obligations.

Rewrite `h` using `[inv_div]`. Conclude with `h`.
-/
theorem geC_add {x y : Y.Kc} {g : ℝ} (hx : Y.geC x g) (hy : Y.geC y g) : Y.geC (x + y) g := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
    exact hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]
    exact hy
  rcases Y.Oc_val (x / y) with h | h
  · exact valuation_bound_add Y hy0 h hy
  · rw [add_comm]
    refine valuation_bound_add Y hx0 ?_ hx
    rw [inv_div] at h
    exact h

def geCgrp (g : ℝ) : AddSubgroup Y.Kc where
  carrier := {x | Y.geC x g}
  add_mem' := fun hx hy => geC_add Y hx hy
  zero_mem' := geC_zero Y g
  neg_mem' := fun hx => geC_neg Y hx

def RK (X : Sys p) : Subring X.G.Kf := (algebraMap X.G.O X.G.Kf).range

/- English proof (translation)
Simplify using `only [Sys.intK, RK, LinearMap.mem_range, RingHom.mem_range, Algebra.linearMap_apply]`.
-/
theorem mem_intKF {x : X.G.Kf} : x ∈ X.intK ↔ x ∈ RK X := by
  simp only [Sys.intK, RK, LinearMap.mem_range, RingHom.mem_range, Algebra.linearMap_apply]

/- English proof (translation)
Rewrite using `[Y.Oc_K, mem_intKF]`.
-/
theorem mem_RK_iff {x : X.G.Kf} : x ∈ RK X ↔ algebraMap X.G.Kf Y.Kc x ∈ Y.Oc := by
  rw [Y.Oc_K, mem_intKF]

include Y in
/- English proof (translation)
Rewrite using `[mem_RK_iff Y, mem_RK_iff Y, map_inv₀]`. Conclude with `Y.Oc_val _`.
-/
theorem RK_val (x : X.G.Kf) : x ∈ RK X ∨ x⁻¹ ∈ RK X := by
  rw [mem_RK_iff Y, mem_RK_iff Y, map_inv₀]
  exact Y.Oc_val _

/- English proof (translation)
Break down `z with n | n` into its components or cases. Simplify using `only [Int.ofNat_eq_coe, zpow_natCast]`. Conclude with `pow_mem h1 n`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem h2 _`.
-/
theorem zpow_mem_RK {a : X.G.Kf} (h1 : a ∈ RK X) (h2 : a⁻¹ ∈ RK X) (z : ℤ) : a ^ z ∈ RK X := by
  rcases z with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_mem h1 n
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h2 _

abbrev vpK (X : Sys p) : X.G.Kf := algebraMap X.G.O X.G.Kf X.vp

/- English proof (translation)
Introduce `h`. Take `⟨o, ho⟩` from `RingHom.mem_range.mp (show (vpK X)⁻¹ ∈ (algebraMap X.G.O X.G.Kf).range from h)`. Establish `hu : IsUnit (1 - X.vp * o)` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mem_nonunits_iff.mpr fun h' => X.unif.1 (isUnit_of_mul_isUnit_left h'))`. Establish `h1 : algebraMap X.G.O X.G.Kf (1 - X.vp * o) = 0`. Rewrite using `[map_sub, map_one, map_mul, ho, mul_inv_cancel₀ h0, sub_self]`.

Conclude with `(hu.map (algebraMap X.G.O X.G.Kf)).ne_zero h1`.
-/
theorem vpK_inv_not_mem (h0 : vpK X ≠ 0) : (vpK X)⁻¹ ∉ RK X := by
  intro h
  obtain ⟨o, ho⟩ := RingHom.mem_range.mp (show (vpK X)⁻¹ ∈ (algebraMap X.G.O X.G.Kf).range from h)
  have hu : IsUnit (1 - X.vp * o) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (mem_nonunits_iff.mpr fun h' => X.unif.1 (isUnit_of_mul_isUnit_left h'))
  have h1 : algebraMap X.G.O X.G.Kf (1 - X.vp * o) = 0 := by
    rw [map_sub, map_one, map_mul, ho, mul_inv_cancel₀ h0, sub_self]
  exact (hu.map (algebraMap X.G.O X.G.Kf)).ne_zero h1

/- English proof (translation)
Establish `hm : o ∈ IsLocalRing.maximalIdeal X.G.O` using `(IsLocalRing.mem_maximalIdeal o).mpr (mem_nonunits_iff.mpr h)`. Rewrite `hm` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer X.vp).mp X.unif, Ideal.mem_span_singleton]`. Conclude with `hm`.
-/
theorem dvd_of_not_unit {o : X.G.O} (h : ¬ IsUnit o) : X.vp ∣ o := by
  have hm : o ∈ IsLocalRing.maximalIdeal X.G.O :=
    (IsLocalRing.mem_maximalIdeal o).mpr (mem_nonunits_iff.mpr h)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer X.vp).mp X.unif,
    Ideal.mem_span_singleton] at hm
  exact hm

include Y in

/- English proof (translation)
Break down `RK_val Y x with h | h` into its components or cases. Conclude with `Or.inl h`. Distinguish the cases in `hx : x ∈ RK X`. Conclude with `Or.inl hx`. Use `right`.

Take `⟨o', ho'⟩` from `h`. Establish `hnu : ¬ IsUnit o'`. Introduce and unpack `⟨w, rfl⟩`. Apply `hx` to reduce the goal to its premises. Use `⟨↑w⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_units_inv, ho', inv_inv]`. Take `⟨o, rfl⟩` from `dvd_of_not_unit hnu`. Conclude with `⟨o, by rw [← ho', map_mul]⟩`.
-/
theorem RK_or (x : X.G.Kf) : x ∈ RK X ∨ ∃ o : X.G.O, x⁻¹ = vpK X * algebraMap X.G.O X.G.Kf o := by
  rcases RK_val Y x with h | h
  · exact Or.inl h
  · by_cases hx : x ∈ RK X
    · exact Or.inl hx
    · right
      obtain ⟨o', ho'⟩ := h
      have hnu : ¬ IsUnit o' := by
        rintro ⟨w, rfl⟩
        apply hx
        refine ⟨↑w⁻¹, ?_⟩
        rw [map_units_inv, ho', inv_inv]
      obtain ⟨o, rfl⟩ := dvd_of_not_unit hnu
      exact ⟨o, by rw [← ho', map_mul]⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `X.eO_spec`. Use `⟨algebraMap X.G.O X.G.Kf u, ⟨u, rfl⟩, ⟨↑u⁻¹, map_units_inv (algebraMap X.G.O X.G.Kf) u⟩, (u.isUnit.map (algebraMap X.G.O X.G.Kf)).ne_zero, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (algebraMap X.G.O X.G.Kf) hu`. Rewrite `h` using `[map_mul, map_pow, map_natCast]`. Conclude with `h`.
-/
theorem p_eq : ∃ u : X.G.Kf, u ∈ RK X ∧ u⁻¹ ∈ RK X ∧ u ≠ 0 ∧ (p : X.G.Kf) * u = vpK X ^ X.eO := by
  obtain ⟨u, hu⟩ := X.eO_spec
  refine ⟨algebraMap X.G.O X.G.Kf u, ⟨u, rfl⟩, ⟨↑u⁻¹, map_units_inv (algebraMap X.G.O X.G.Kf) u⟩,
    (u.isUnit.map (algebraMap X.G.O X.G.Kf)).ne_zero, ?_⟩
  have h := congrArg (algebraMap X.G.O X.G.Kf) hu
  rw [map_mul, map_pow, map_natCast] at h
  exact h

include Y in
/- English proof (translation)
Take `⟨u, -, -, hu0, hu⟩` from `p_eq (X := X)`. Assume the negation of the conclusion as `hne`. Rewrite `hu` using `[h0, zero_pow hne]`. Conclude with `mul_ne_zero (pK_ne Y) hu0 hu`.
-/
theorem eO_zero_of_vpK_zero (h0 : vpK X = 0) : X.eO = 0 := by
  obtain ⟨u, -, -, hu0, hu⟩ := p_eq (X := X)
  by_contra hne
  rw [h0, zero_pow hne] at hu
  exact mul_ne_zero (pK_ne Y) hu0 hu

include Y in
/- English proof (translation)
Unfold `Sys.vsc`. Distinguish the cases in `h0 : vpK X = 0`. Rewrite using `[eO_zero_of_vpK_zero Y h0]`. Simplify using the standard rewrite rules. Conclude with `zpow_ne_zero _ h0`.
-/
theorem vsc_ne_zero (g : ℝ) : X.vsc g ≠ 0 := by
  unfold Sys.vsc
  by_cases h0 : vpK X = 0
  · rw [eO_zero_of_vpK_zero Y h0]
    simp
  · exact zpow_ne_zero _ h0

/- English proof (translation)
Simplify using `only [scale, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]`.
-/
theorem mem_scale_iff {M : Type*} [AddCommGroup M] [Module X.G.Kf M] [Module X.G.O M] [IsScalarTower X.G.O X.G.Kf M]
    (c : X.G.Kf) (N : Submodule X.G.O M) (x : M) : x ∈ scale c N ↔ ∃ y ∈ N, c • y = x := by
  simp only [scale, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Substitute `he` using the available equality. Use `⟨⌊g⌋, 1, one_pos, by simpa using Int.floor_le g, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Take `⟨c, hc⟩ : ∃ c : ℤ, c = ⌈g * (e : ℝ)⌉` from `⟨_, rfl⟩`.

Rewrite using `[← hc]`. Establish `hc1 : ((c : ℝ) - 1) < g * e`. Use `Int.ceil_lt_add_one (g * (e : ℝ))` as an intermediate fact. Rewrite `this` using `[← hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hδ : 0 < g * e - ((c : ℝ) - 1)` using `by linarith`. Take `⟨k, hk⟩` from `exists_nat_gt (1 / (g * e - ((c : ℝ) - 1)))`. Establish `hk0' : (0 : ℝ) < k` using `lt_trans (by positivity) hk`. Establish `hk0 : 0 < k` using `by exact_mod_cast hk0'`. Establish `hkδ : 1 < (k : ℝ) * (g * e - ((c : ℝ) - 1))`.

Establish `h1 : 1 / (g * e - ((c : ℝ) - 1)) * (g * e - ((c : ℝ) - 1)) = 1` using `by field_simp`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨⌊g * ((e * k : ℕ) : ℝ)⌋, e * k, Nat.mul_pos he hk0, Int.floor_le _, ?_⟩` and prove the remaining obligations. Establish `hfl : (c - 1) * (k : ℤ) < ⌊g * ((e * k : ℕ) : ℝ)⌋`. Rewrite using `[Int.lt_iff_add_one_le, Int.le_floor]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `he' : (0 : ℤ) < e` using `by exact_mod_cast he`. Move the coercions through the operations in `at hfl ⊢`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hfl he']`.
-/
theorem exists_ab (e : ℕ) (g : ℝ) : ∃ (a : ℤ) (b : ℕ), 0 < b ∧ (a : ℝ) ≤ g * b ∧ (⌈g * (e : ℝ)⌉ - 1) * (b : ℤ) - e * a < 0 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨⌊g⌋, 1, one_pos, by simpa using Int.floor_le g, ?_⟩
    simp
  · obtain ⟨c, hc⟩ : ∃ c : ℤ, c = ⌈g * (e : ℝ)⌉ := ⟨_, rfl⟩
    rw [← hc]
    have hc1 : ((c : ℝ) - 1) < g * e := by
      have := Int.ceil_lt_add_one (g * (e : ℝ))
      rw [← hc] at this
      linarith
    have hδ : 0 < g * e - ((c : ℝ) - 1) := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (g * e - ((c : ℝ) - 1)))
    have hk0' : (0 : ℝ) < k := lt_trans (by positivity) hk
    have hk0 : 0 < k := by exact_mod_cast hk0'
    have hkδ : 1 < (k : ℝ) * (g * e - ((c : ℝ) - 1)) := by
      have h1 : 1 / (g * e - ((c : ℝ) - 1)) * (g * e - ((c : ℝ) - 1)) = 1 := by field_simp
      nlinarith
    refine ⟨⌊g * ((e * k : ℕ) : ℝ)⌋, e * k, Nat.mul_pos he hk0, Int.floor_le _, ?_⟩
    have hfl : (c - 1) * (k : ℤ) < ⌊g * ((e * k : ℕ) : ℝ)⌋ := by
      rw [Int.lt_iff_add_one_le, Int.le_floor]
      push_cast
      nlinarith
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    push_cast at hfl ⊢
    nlinarith [mul_lt_mul_of_pos_left hfl he']

/- English proof (translation)
Establish `hv : X.vsc g ≠ 0` using `vsc_ne_zero Y g`. Establish `hvsc : X.vsc g = vpK X ^ ⌈g * (X.eO : ℝ)⌉` using `rfl`. It suffices to establish `hz : c * (X.vsc g)⁻¹ ∈ RK X by`. Unfold `Sys.vGeK`. Rewrite using `[mem_scale_iff]`.

Use `⟨c * (X.vsc g)⁻¹, (mem_intKF (X := X)).mpr hz, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hv, mul_one]`. Assume the negation of the conclusion as `hz`. Break down `RK_or Y (c * (X.vsc g)⁻¹) with hz' | ⟨o, ho⟩` into its components or cases. Conclude with `hz hz'`.

Establish `hz0 : c * (X.vsc g)⁻¹ ≠ 0` using `fun h0 => hz (h0 ▸ (RK X).zero_mem)`. Establish `hπ : vpK X ≠ 0` using `fun h0 => by`. Rewrite `ho` using `[h0, zero_mul, inv_eq_zero]`. Conclude with `hz0 ho`. Establish `hoK : algebraMap X.G.O X.G.Kf o ≠ 0` using `fun h0 => by`.

Rewrite `ho` using `[h0, mul_zero, inv_eq_zero]`. Conclude with `hz0 ho`. Take `⟨u, hu1, hu2, hu0, hpu⟩` from `p_eq (X := X)`. Take `⟨a, b, hb, hab, hN⟩` from `exists_ab X.eO g`. Establish `hw : c ^ b * (p : X.G.Kf) ^ (-a) ∈ RK X`.

Rewrite using `[mem_RK_iff Y, map_mul, map_pow, map_zpow₀, map_natCast]`. Conclude with `h a b hb hab`. Use `set m : ℤ := ⌈g * (X.eO : ℝ)⌉ with hm`. Use `set Ok := algebraMap X.G.O X.G.Kf o with hOk`. Establish `hc : c = (vpK X * Ok)⁻¹ * vpK X ^ m`.

Establish `h1 : c * (X.vsc g)⁻¹ = (vpK X * Ok)⁻¹` using `by rw [← ho, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hp : (p : X.G.Kf) = vpK X ^ X.eO * u⁻¹`. Rewrite using `[← hpu, mul_assoc, mul_inv_cancel₀ hu0, mul_one]`. Establish `hid : c ^ b * (p : X.G.Kf) ^ (-a) * (Ok ^ b * u ^ (-a)) = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a)`.

Rewrite using `[hc, hp]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← zpow_natCast, mul_zpow, inv_zpow', ← zpow_mul, neg_neg]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) := by`.

Rewrite using `[← zpow_add₀ hπ, ← zpow_add₀ hπ, ← zpow_add₀ hoK, ← zpow_add₀ hu0, neg_add_cancel, add_neg_cancel, zpow_zero, zpow_zero, mul_one, mul_one]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hPN : vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) ∈ RK X`. Rewrite using `[← hid]`.

Conclude with `(RK X).mul_mem hw ((RK X).mul_mem ((RK X).pow_mem ⟨o, rfl⟩ _) (zpow_mem_RK hu1 hu2 _))`. Establish `hk : 0 ≤ -((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) - 1` using `by linarith`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le hk`. Establish `hPn : vpK X ^ (n : ℤ) ∈ RK X`. Rewrite using `[zpow_natCast]`.

Conclude with `(RK X).pow_mem ⟨X.vp, rfl⟩ _`. Establish `hinv : (vpK X)⁻¹ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) * vpK X ^ (n : ℤ)`. Rewrite using `[← zpow_add₀ hπ, ← hn, ← zpow_neg_one]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `vpK_inv_not_mem hπ (by rw [hinv]; exact (RK X).mul_mem hPN hPn)`.
-/
theorem vGeK_of_geC (c : X.G.Kf) (g : ℝ) (h : Y.geC (algebraMap X.G.Kf Y.Kc c) g) : X.vGeK c g := by
  have hv : X.vsc g ≠ 0 := vsc_ne_zero Y g
  have hvsc : X.vsc g = vpK X ^ ⌈g * (X.eO : ℝ)⌉ := rfl
  suffices hz : c * (X.vsc g)⁻¹ ∈ RK X by
    unfold Sys.vGeK
    rw [mem_scale_iff]
    refine ⟨c * (X.vsc g)⁻¹, (mem_intKF (X := X)).mpr hz, ?_⟩
    rw [smul_eq_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  by_contra hz
  rcases RK_or Y (c * (X.vsc g)⁻¹) with hz' | ⟨o, ho⟩
  · exact hz hz'
  have hz0 : c * (X.vsc g)⁻¹ ≠ 0 := fun h0 => hz (h0 ▸ (RK X).zero_mem)
  have hπ : vpK X ≠ 0 := fun h0 => by
    rw [h0, zero_mul, inv_eq_zero] at ho
    exact hz0 ho
  have hoK : algebraMap X.G.O X.G.Kf o ≠ 0 := fun h0 => by
    rw [h0, mul_zero, inv_eq_zero] at ho
    exact hz0 ho
  obtain ⟨u, hu1, hu2, hu0, hpu⟩ := p_eq (X := X)
  obtain ⟨a, b, hb, hab, hN⟩ := exists_ab X.eO g
  have hw : c ^ b * (p : X.G.Kf) ^ (-a) ∈ RK X := by
    rw [mem_RK_iff Y, map_mul, map_pow, map_zpow₀, map_natCast]
    exact h a b hb hab
  set m : ℤ := ⌈g * (X.eO : ℝ)⌉ with hm
  set Ok := algebraMap X.G.O X.G.Kf o with hOk
  have hc : c = (vpK X * Ok)⁻¹ * vpK X ^ m := by
    have h1 : c * (X.vsc g)⁻¹ = (vpK X * Ok)⁻¹ := by rw [← ho, inv_inv]
    calc c = c * (X.vsc g)⁻¹ * X.vsc g := by rw [mul_assoc, inv_mul_cancel₀ hv, mul_one]
      _ = (vpK X * Ok)⁻¹ * vpK X ^ m := by rw [h1, hvsc]
  have hp : (p : X.G.Kf) = vpK X ^ X.eO * u⁻¹ := by
    rw [← hpu, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  have hid : c ^ b * (p : X.G.Kf) ^ (-a) * (Ok ^ b * u ^ (-a)) =
      vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) := by
    rw [hc, hp]
    calc ((vpK X * Ok)⁻¹ * vpK X ^ m) ^ b * (vpK X ^ X.eO * u⁻¹) ^ (-a) * (Ok ^ b * u ^ (-a))
        = (vpK X ^ (-(b : ℤ)) * vpK X ^ (m * b) * vpK X ^ ((X.eO : ℤ) * -a)) *
            (Ok ^ (-(b : ℤ)) * Ok ^ (b : ℤ)) * (u ^ a * u ^ (-a)) := by
          simp only [← zpow_natCast, mul_zpow, inv_zpow', ← zpow_mul, neg_neg]
          ring
      _ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) := by
          rw [← zpow_add₀ hπ, ← zpow_add₀ hπ, ← zpow_add₀ hoK, ← zpow_add₀ hu0, neg_add_cancel,
            add_neg_cancel, zpow_zero, zpow_zero, mul_one, mul_one]
          congr 1
          ring
  have hPN : vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) ∈ RK X := by
    rw [← hid]
    exact (RK X).mul_mem hw ((RK X).mul_mem ((RK X).pow_mem ⟨o, rfl⟩ _) (zpow_mem_RK hu1 hu2 _))
  have hk : 0 ≤ -((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) - 1 := by linarith
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk
  have hPn : vpK X ^ (n : ℤ) ∈ RK X := by
    rw [zpow_natCast]
    exact (RK X).pow_mem ⟨X.vp, rfl⟩ _
  have hinv : (vpK X)⁻¹ = vpK X ^ ((m - 1) * (b : ℤ) - (X.eO : ℤ) * a) * vpK X ^ (n : ℤ) := by
    rw [← zpow_add₀ hπ, ← hn, ← zpow_neg_one]
    congr 1
    ring
  exact vpK_inv_not_mem hπ (by rw [hinv]; exact (RK X).mul_mem hPN hPn)

end Formalism.MainNotions.FormalGroupSystem.Pf
