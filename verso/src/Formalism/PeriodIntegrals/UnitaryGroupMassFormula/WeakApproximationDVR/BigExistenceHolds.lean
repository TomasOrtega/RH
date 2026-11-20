import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExists

noncomputable section

namespace PI.WA

open PI.WADVR

section Field

variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}

/- English proof (translation)
Establish `h1` using `(Sm.pow hϖ hqs r).mul hϖ hY`. Rewrite using `[mul_inv, ← inv_pow]`. Conclude with `h1.mono hϖ (by push_cast; omega)`.
-/
lemma g_big_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hqs : Sm Q ϖ 1 q⁻¹) (hY : Sm Q ϖ 1 Y⁻¹)
    (r : ℕ) : Sm Q ϖ 1 (q ^ r * Y)⁻¹ := by
  have h1 := (Sm.pow hϖ hqs r).mul hϖ hY
  rw [mul_inv, ← inv_pow]
  exact h1.mono hϖ (by push_cast; omega)

/- English proof (translation)
The claim follows from `((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)`.
-/
lemma g_small_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y)
    (r : ℕ) (hr : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * Y) :=
  ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)

/- English proof (translation)
Conclude with `((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)`.
-/
lemma g_int_pow_mul (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 0 q) (hY : Sm Q ϖ 1 Y) (r : ℕ) :
    Sm Q ϖ 1 (q ^ r * Y) := by
  exact ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)

/- English proof (translation)
Establish `ht : Sm Q ϖ 1 ((q⁻¹) ^ r)` using `(Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)`. Take `⟨ht0, -⟩` from `one_add_of_sm hϖ ht`. Establish `hqr : q ^ r ≠ 0` using `pow_ne_zero _ hq`. Establish `h1 : 1 + q ^ r ≠ 0`. Introduce `h`.

Apply `ht0` to reduce the goal to its premises. Establish `e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r)`. Rewrite using `[inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]`. Rewrite using `[e, h, mul_zero]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Establish `e : (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ = (1 + (q⁻¹) ^ r) * Y⁻¹`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Establish `h2 : Sm Q ϖ 0 (1 + (q⁻¹) ^ r)` using `Sm.add Sm.one (ht.mono hϖ (by norm_num))`. Establish `h3` using `h2.mul hϖ hY`. Simplify using `using h3`.
-/
lemma g_B_big (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹) (hY0 : Y ≠ 0)
    (hY : Sm Q ϖ 1 Y⁻¹) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, -⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  refine ⟨h1, ?_⟩
  have e : (q ^ r * (1 + q ^ r)⁻¹ * Y)⁻¹ = (1 + (q⁻¹) ^ r) * Y⁻¹ := by
    rw [inv_pow]
    field_simp
    ring
  rw [e]
  have h2 : Sm Q ϖ 0 (1 + (q⁻¹) ^ r) := Sm.add Sm.one (ht.mono hϖ (by norm_num))
  have h3 := h2.mul hϖ hY
  simpa using h3

/- English proof (translation)
Establish `hqr` using `Sm.pow hϖ hq r`. Take `⟨-, hinv⟩` from `one_add_of_sm hϖ (hqr.mono hϖ (by push_cast; omega))`. Conclude with `((hqr.mul hϖ hinv).mul hϖ hY).mono hϖ (by push_cast; omega)`.
-/
lemma g_B_small (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y) {r : ℕ}
    (hr : 1 ≤ r) (hrm : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have hqr := Sm.pow hϖ hq r
  obtain ⟨-, hinv⟩ := one_add_of_sm hϖ (hqr.mono hϖ (by push_cast; omega))
  exact ((hqr.mul hϖ hinv).mul hϖ hY).mono hϖ (by push_cast; omega)

/- English proof (translation)
Establish `ht : Sm Q ϖ 1 ((q⁻¹) ^ r)` using `(Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)`. Take `⟨ht0, hinv⟩` from `one_add_of_sm hϖ ht`. Establish `hqr : q ^ r ≠ 0` using `pow_ne_zero _ hq`. Establish `h1 : 1 + q ^ r ≠ 0`. Introduce `h`.

Apply `ht0` to reduce the goal to its premises. Establish `e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r)`. Rewrite using `[inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]`. Rewrite using `[e, h, mul_zero]`. Establish `e : q ^ r * (1 + q ^ r)⁻¹ = (1 + (q⁻¹) ^ r)⁻¹`.

Rewrite using `[inv_pow, eq_comm, inv_eq_iff_eq_inv, mul_inv, inv_inv, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]`. Rewrite using `[e]`. Simplify using `using hinv.mul hϖ hY`.
-/
lemma g_B_bigj (hϖ : Irreducible ϖ) {q Y : Q} (hq : q ≠ 0) (hqs : Sm Q ϖ 1 q⁻¹)
    (hY : Sm Q ϖ 1 Y) {r : ℕ} (hr : 1 ≤ r) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have ht : Sm Q ϖ 1 ((q⁻¹) ^ r) := (Sm.pow hϖ hqs r).mono hϖ (by push_cast; omega)
  obtain ⟨ht0, hinv⟩ := one_add_of_sm hϖ ht
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ hq
  have h1 : 1 + q ^ r ≠ 0 := by
    intro h
    apply ht0
    have e : 1 + (q⁻¹) ^ r = (q ^ r)⁻¹ * (1 + q ^ r) := by
      rw [inv_pow, mul_add, inv_mul_cancel₀ hqr, mul_one, add_comm]
    rw [e, h, mul_zero]
  have e : q ^ r * (1 + q ^ r)⁻¹ = (1 + (q⁻¹) ^ r)⁻¹ := by
    rw [inv_pow, eq_comm, inv_eq_iff_eq_inv, mul_inv, inv_inv, mul_add, inv_mul_cancel₀ hqr, mul_one,
      add_comm]
  rw [e]
  simpa using hinv.mul hϖ hY

end Field

/- English proof (translation)
Introduce `E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden hdist ϖ hϖ i`. Establish `pair : ∀ j, j ≠ i → ∃ y : E, y ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i y)⁻¹ ∧ Sm (Q j) (ϖ j) 1 (iw j y)`. Introduce `j hji`. Take `⟨a, haj, hai⟩` from `hdist j i hji`. Take `⟨b, hbi, hbj⟩` from `hdist i j (Ne.symm hji)`.

Take `⟨hai0, hai1⟩` from `big_of_not_mem (hϖ i) hai`. Take `⟨hbj0, hbj1⟩` from `big_of_not_mem (hϖ j) hbj`. Establish `ha0 : a ≠ 0` using `fun h => hai0 (by rw [h, map_zero])`. Establish `hb0 : b ≠ 0` using `fun h => hbj0 (by rw [h, map_zero])`. Use `⟨a * b⁻¹, mul_ne_zero ha0 (inv_ne_zero hb0), ?_, ?_⟩` and prove the remaining obligations.

Establish `e : (iw i (a * b⁻¹))⁻¹ = iw i b * (iw i a)⁻¹`. Rewrite using `[map_mul, map_inv₀, mul_inv, inv_inv, mul_comm]`. Rewrite using `[e]`. Use `((sm_zero_iff (ϖ := ϖ i)).mpr hbi).mul (hϖ i) hai1` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Establish `e : iw j (a * b⁻¹) = iw j a * (iw j b)⁻¹` using `by rw [map_mul, map_inv₀]`. Rewrite using `[e]`. Use `((sm_zero_iff (ϖ := ϖ j)).mpr haj).mul (hϖ j) hbj1` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `base : ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹`.

Take `⟨a, c, hac⟩` from `hden i ((p : Q i)⁻¹) 1`. Establish `hpi` using `hp0 i`. Establish `hts : Sm (Q i) (ϖ i) 1 ((p : Q i) ^ 2 * algebraMap (W i) (Q i) c)`. Establish `h1` using `((sm_natCast (Q := Q i) (hϖ i) (hpu i)).pow (hϖ i) 2).mul (hϖ i) (Sm.alg (ϖ := ϖ i) (Q := Q i) c)`. Conclude with `h1.mono (hϖ i) (by norm_num)`.

Take `⟨h1t, h2t⟩` from `one_add_of_sm (hϖ i) hts`. Establish `e : iw i a = (p : Q i)⁻¹ * (1 + (p : Q i) ^ 2 * algebraMap (W i) (Q i) c)`. Rewrite using `[hac]`. Clear the denominators using the available nonvanishing facts. Use `⟨a, fun h => ?_, ?_⟩` and prove the remaining obligations.

Rewrite `e` using `[h, map_zero]`. Conclude with `mul_ne_zero (inv_ne_zero hpi) h1t e.symm`. Rewrite using `[e, mul_inv, inv_inv]`. Use `(sm_natCast (Q := Q i) (hϖ i) (hpu i)).mul (hϖ i) h2t` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.

Establish `main : ∀ S : Finset ι, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧ ∀ k ∈ S, k ≠ i → Sm (Q k) (ϖ k) 1 (iw k z)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Take `⟨z, hz, hzi⟩` from `base`.

Conclude with `⟨z, hz, hzi, by simp⟩`. Consider the case `@insert j S hjS ih`. Take `⟨z, hz0, hzi, hzS⟩` from `ih`. Distinguish the cases in `hji : j = i`. Use `⟨z, hz0, hzi, fun k hk hki => hzS k ?_ hki⟩` and prove the remaining obligations.

Conclude with `(Finset.mem_insert.mp hk).resolve_left (fun h => hki (h.trans hji))`. Take `⟨y, hy0, hyi, hyj⟩` from `pair j hji choose m hm using fun k => sm_exists (hϖ k) (iw k y)`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr1, hrm⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ k, 1 ≤ (r : ℤ) + m k := by`. Use `⟨1 + ∑ k, (-(m k)).toNat, by omega, fun k => ?_⟩` and prove the remaining obligations. Establish `h1 : (-(m k)).toNat ≤ ∑ k, (-(m k)).toNat` using `Finset.single_le_sum (f := fun k => (-(m k)).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`.

Establish `h2` using `Int.self_le_toNat (-(m k))`. Establish `h3 : ((1 + ∑ k, (-(m k)).toNat : ℕ) : ℤ) ≥ 1 + ((-(m k)).toNat : ℤ)`. Conclude with `Nat.add_le_add_left h1 1` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzi0 : iw i z ≠ 0` using `(map_ne_zero _).mpr hz0`.

Distinguish the cases in `hzj : iw j z ∈ Set.range (algebraMap (W j) (Q j))`. Use `⟨z ^ r * y, mul_ne_zero (pow_ne_zero _ hz0) hy0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Conclude with `g_big_pow_mul (hϖ i) hzi hyi r`. Introduce `k hk hki`.

Rewrite using `[map_mul, map_pow]`. Break down `Finset.mem_insert.mp hk with h | hkS` into its components or cases. Rewrite using `[h]`. Conclude with `g_int_pow_mul (hϖ j) ((sm_zero_iff (ϖ := ϖ j)).mpr hzj) hyj r`. Conclude with `g_small_pow_mul (hϖ k) (hzS k hkS hki) (hm k) r (hrm k)`.

Take `⟨hzj0, hzj1⟩` from `big_of_not_mem (hϖ j) hzj`. Take `⟨hd, hbig⟩` from `g_B_big (hϖ i) hzi0 hzi ((map_ne_zero _).mpr hy0) hyi hr1`. Establish `hmap : ∀ k, iw k (z ^ r * (1 + z ^ r)⁻¹ * y) = (iw k z) ^ r * (1 + (iw k z) ^ r)⁻¹ * iw k y` using `fun k => by`. Simplify using `only [map_mul, map_pow, map_inv₀, map_add, map_one]`. Establish `hd' : (1 + z ^ r : E) ≠ 0` using `fun h => hd (by`.

Establish `: iw i (1 + z ^ r) = 1 + (iw i z) ^ r`. Simplify using `only [map_add, map_one, map_pow]`. Rewrite using `[← this, h, map_zero])`. Use `⟨z ^ r * (1 + z ^ r)⁻¹ * y, mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hd')) hy0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap]`.

Conclude with `hbig`. Introduce `k hk hki`. Rewrite using `[hmap]`. Break down `Finset.mem_insert.mp hk with h | hkS` into its components or cases. Rewrite using `[h]`.

Conclude with `g_B_bigj (hϖ j) hzj0 hzj1 hyj hr1`. Conclude with `g_B_small (hϖ k) (hzS k hkS hki) (hm k) hr1 (hrm k)`. Take `⟨z, hz0, hzi, hzS⟩` from `main Finset.univ`. Conclude with `⟨z, hz0, hzi, fun j hj => hzS j (Finset.mem_univ j) hj⟩`.
-/
theorem big_existence_holds : BigExists := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden hdist ϖ hϖ i
  classical

  have pair : ∀ j, j ≠ i → ∃ y : E, y ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i y)⁻¹ ∧
      Sm (Q j) (ϖ j) 1 (iw j y) := by
    intro j hji
    obtain ⟨a, haj, hai⟩ := hdist j i hji
    obtain ⟨b, hbi, hbj⟩ := hdist i j (Ne.symm hji)
    obtain ⟨hai0, hai1⟩ := big_of_not_mem (hϖ i) hai
    obtain ⟨hbj0, hbj1⟩ := big_of_not_mem (hϖ j) hbj
    have ha0 : a ≠ 0 := fun h => hai0 (by rw [h, map_zero])
    have hb0 : b ≠ 0 := fun h => hbj0 (by rw [h, map_zero])
    refine ⟨a * b⁻¹, mul_ne_zero ha0 (inv_ne_zero hb0), ?_, ?_⟩
    · have e : (iw i (a * b⁻¹))⁻¹ = iw i b * (iw i a)⁻¹ := by
        rw [map_mul, map_inv₀, mul_inv, inv_inv, mul_comm]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ i)).mpr hbi).mul (hϖ i) hai1
      rwa [zero_add] at this
    · have e : iw j (a * b⁻¹) = iw j a * (iw j b)⁻¹ := by rw [map_mul, map_inv₀]
      rw [e]
      have := ((sm_zero_iff (ϖ := ϖ j)).mpr haj).mul (hϖ j) hbj1
      rwa [zero_add] at this

  have base : ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ := by
    obtain ⟨a, c, hac⟩ := hden i ((p : Q i)⁻¹) 1
    have hpi := hp0 i
    have hts : Sm (Q i) (ϖ i) 1 ((p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      have h1 := ((sm_natCast (Q := Q i) (hϖ i) (hpu i)).pow (hϖ i) 2).mul (hϖ i)
        (Sm.alg (ϖ := ϖ i) (Q := Q i) c)
      exact h1.mono (hϖ i) (by norm_num)
    obtain ⟨h1t, h2t⟩ := one_add_of_sm (hϖ i) hts
    have e : iw i a = (p : Q i)⁻¹ * (1 + (p : Q i) ^ 2 * algebraMap (W i) (Q i) c) := by
      rw [hac]
      field_simp
    refine ⟨a, fun h => ?_, ?_⟩
    · rw [h, map_zero] at e
      exact mul_ne_zero (inv_ne_zero hpi) h1t e.symm
    · rw [e, mul_inv, inv_inv]
      have := (sm_natCast (Q := Q i) (hϖ i) (hpu i)).mul (hϖ i) h2t
      rwa [add_zero] at this

  have main : ∀ S : Finset ι, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧
      ∀ k ∈ S, k ≠ i → Sm (Q k) (ϖ k) 1 (iw k z) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz, hzi⟩ := base
      exact ⟨z, hz, hzi, by simp⟩
    | @insert j S hjS ih =>
      obtain ⟨z, hz0, hzi, hzS⟩ := ih
      by_cases hji : j = i
      · refine ⟨z, hz0, hzi, fun k hk hki => hzS k ?_ hki⟩
        exact (Finset.mem_insert.mp hk).resolve_left (fun h => hki (h.trans hji))
      · obtain ⟨y, hy0, hyi, hyj⟩ := pair j hji
        choose m hm using fun k => sm_exists (hϖ k) (iw k y)
        obtain ⟨r, hr1, hrm⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ k, 1 ≤ (r : ℤ) + m k := by
          refine ⟨1 + ∑ k, (-(m k)).toNat, by omega, fun k => ?_⟩
          have h1 : (-(m k)).toNat ≤ ∑ k, (-(m k)).toNat :=
            Finset.single_le_sum (f := fun k => (-(m k)).toNat) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
          have h2 := Int.self_le_toNat (-(m k))
          have h3 : ((1 + ∑ k, (-(m k)).toNat : ℕ) : ℤ) ≥ 1 + ((-(m k)).toNat : ℤ) := by
            exact_mod_cast Nat.add_le_add_left h1 1
          linarith
        have hzi0 : iw i z ≠ 0 := (map_ne_zero _).mpr hz0
        by_cases hzj : iw j z ∈ Set.range (algebraMap (W j) (Q j))
        · refine ⟨z ^ r * y, mul_ne_zero (pow_ne_zero _ hz0) hy0, ?_, ?_⟩
          · rw [map_mul, map_pow]
            exact g_big_pow_mul (hϖ i) hzi hyi r
          · intro k hk hki
            rw [map_mul, map_pow]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_int_pow_mul (hϖ j) ((sm_zero_iff (ϖ := ϖ j)).mpr hzj) hyj r
            · exact g_small_pow_mul (hϖ k) (hzS k hkS hki) (hm k) r (hrm k)
        · obtain ⟨hzj0, hzj1⟩ := big_of_not_mem (hϖ j) hzj
          obtain ⟨hd, hbig⟩ := g_B_big (hϖ i) hzi0 hzi ((map_ne_zero _).mpr hy0) hyi hr1
          have hmap : ∀ k, iw k (z ^ r * (1 + z ^ r)⁻¹ * y) =
              (iw k z) ^ r * (1 + (iw k z) ^ r)⁻¹ * iw k y := fun k => by
            simp only [map_mul, map_pow, map_inv₀, map_add, map_one]
          have hd' : (1 + z ^ r : E) ≠ 0 := fun h => hd (by
            have : iw i (1 + z ^ r) = 1 + (iw i z) ^ r := by
              simp only [map_add, map_one, map_pow]
            rw [← this, h, map_zero])
          refine ⟨z ^ r * (1 + z ^ r)⁻¹ * y,
            mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hd')) hy0, ?_, ?_⟩
          · rw [hmap]
            exact hbig
          · intro k hk hki
            rw [hmap]
            rcases Finset.mem_insert.mp hk with h | hkS
            · rw [h]
              exact g_B_bigj (hϖ j) hzj0 hzj1 hyj hr1
            · exact g_B_small (hϖ k) (hzS k hkS hki) (hm k) hr1 (hrm k)
  obtain ⟨z, hz0, hzi, hzS⟩ := main Finset.univ
  exact ⟨z, hz0, hzi, fun j hj => hzS j (Finset.mem_univ j) hj⟩

end PI.WA
