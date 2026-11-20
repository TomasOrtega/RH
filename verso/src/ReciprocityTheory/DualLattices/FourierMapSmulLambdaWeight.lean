import ReciprocityTheory.DualLattices.SumLambdaWeight

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Establish `hp1 : ζ ^ p = 1` using `hζ.pow_eq_one`. Set `ψ : AddChar (ZMod p) C` to `AddChar.zmodChar p hp1`. Establish `hψ : ∀ a, ψ a = ζ ^ a.val` using `fun a => AddChar.zmodChar_apply hp1 a`. Set `f : ZMod p → AddChar (ZMod p) C` to `fun h => ψ.mulShift h`. Establish `hf : ∀ h a, f h a = ζ ^ (h * a).val` using `fun h a => by`.

Simplify using `only [f, AddChar.mulShift_apply, hψ]`. Establish `hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val`. Introduce `χ a`. Use `conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]`. Conclude with `AddChar.map_nsmul_eq_pow χ _ _`.

Establish `hinj : Function.Injective f`. Introduce `h h' hh`. Use `congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh` as an intermediate fact. Simplify using `only [hf, mul_one] at this`. Conclude with `ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)`.

Establish `hsurj : Function.Surjective f`. Introduce `χ`. Establish `h1 : χ 1 ^ p = 1`. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]`. Take `⟨k, hk, hkχ⟩` from `hζ.eq_pow_of_pow_eq_one h1`.

Use `⟨(k : ZMod p), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Rewrite using `[hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]`. Use `⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h h'`.

Use extensionality with `a`. Use `show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a`. Rewrite using `[AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul, AddChar.map_add_eq_mul]`. Introduce `h a`. Conclude with `hf h a`.
-/
theorem exists_charEquiv [NeZero p] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ZMod p ≃ AddChar (ZMod p) C, (∀ h h', e (h + h') = e h * e h') ∧
      ∀ h a, e h a = ζ ^ (h * a).val := by
  have hp1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) C := AddChar.zmodChar p hp1
  have hψ : ∀ a, ψ a = ζ ^ a.val := fun a => AddChar.zmodChar_apply hp1 a
  let f : ZMod p → AddChar (ZMod p) C := fun h => ψ.mulShift h
  have hf : ∀ h a, f h a = ζ ^ (h * a).val := fun h a => by
    simp only [f, AddChar.mulShift_apply, hψ]
  have hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val := by
    intro χ a
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]
    exact AddChar.map_nsmul_eq_pow χ _ _
  have hinj : Function.Injective f := by
    intro h h' hh
    have := congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh
    simp only [hf, mul_one] at this
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)
  have hsurj : Function.Surjective f := by
    intro χ
    have h1 : χ 1 ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    obtain ⟨k, hk, hkχ⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(k : ZMod p), ?_⟩
    ext a
    rw [hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro h h'
    ext a
    show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul,
      AddChar.map_add_eq_mul]
  · intro h a
    exact hf h a

/- English proof (translation)
Establish `hpp : 2 ≤ p` using `hp.out.two_le`. Establish `hζ1 : v ζ ≤ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2` using `one_lt_pow₀ h (show p ≠ 0 by omega)`.

Rewrite `h2` using `[← map_pow, hζ.pow_eq_one, map_one]`. Conclude with `lt_irrefl _ h2`. Establish `hπ1 : v (ζ - 1) < 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `h2` using `one_le_pow₀ (n := p - 1) h`. Rewrite `h2` using `[val_prim_root hζ]`. Conclude with `absurd hpv (not_lt.mpr h2)`. Establish `hnat : ∀ n : ℕ, v (n : C) ≤ 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Nat.cast_succ]; exact Valuation.map_add_le v ih (by rw [map_one])`. Establish `hdec : ∀ n : ℕ, ∃ s : C, v s ≤ 1 ∧ ζ ^ n - 1 = (ζ - 1) * (n + (ζ - 1) * s)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨s, hs1, hs⟩` from `ih`. Use `⟨n + ζ * s, Valuation.map_add_le v (hnat n) (by rw [map_mul]; exact mul_le_one' hζ1 hs1), ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `ζ * hs`. Use `choose s hs1 hs using hdec`. Establish `h1 : ∑ a, u0 ω a * ζ ^ a.val = ∑ a, wt ω a * (ζ ^ a.val - 1)`. Use `hω.lam_eq (fun a => ζ ^ a.val)` as an intermediate fact.

Simplify `this` using `[lam, ZMod.val_zero]`. Establish `h2 : ∑ a, wt ω a * ω a = (p : C) - 1`. Use `hω.lam_eq ω` as an intermediate fact. Rewrite `this` using `[hω.lam_omega, hω.zero]`. Simplify using `using this.symm`.

Establish `hγ : ∑ a, u0 ω a * ζ ^ a.val = (ζ - 1) * (((p : C) - 1) + (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val))`. Rewrite using `[h1, ← h2]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hδ : v (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val) < 1`. Apply `Valuation.map_add_lt v` to reduce the goal to its premises. Apply `Valuation.map_sum_lt v one_ne_zero` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Establish `hsum : v (∑ a, wt ω a * s a.val) ≤ 1` using `Valuation.map_sum_le v fun a _ => by rw [map_mul]; exact mul_le_one' (hω.wt_int a) (hs1 _)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hp1 : v ((p : C) - 1) = 1`. Establish `hnd : ¬ (p : ℤ) ∣ (p : ℤ) - 1`. Introduce `hd`. Establish `h1' : (p : ℤ) ∣ 1` using `by simpa using dvd_sub (dvd_refl (p : ℤ)) hd`. Use `Int.eq_one_of_dvd_one (by positivity) h1'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `v_intCast_eq_one hv hpv hnd` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hunit : v ((p : C) - 1 + (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val)) = 1`.

Rewrite using `[Valuation.map_add_eq_of_lt_left v (by rw [hp1]; exact hδ), hp1]`. Rewrite using `[hγ, map_mul, hunit, mul_one]`. Conclude with `val_prim_root hζ`.
-/
theorem v_gamma (hv : v.Integers R) (hpv : v (p : C) < 1) {ω : ZMod p → C} (hω : IsTeich v ω)
    {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    v (∑ a, u0 ω a * ζ ^ a.val) ^ (p - 1) = v (p : C) := by
  have hpp : 2 ≤ p := hp.out.two_le
  have hζ1 : v ζ ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 := one_lt_pow₀ h (show p ≠ 0 by omega)
    rw [← map_pow, hζ.pow_eq_one, map_one] at h2
    exact lt_irrefl _ h2
  have hπ1 : v (ζ - 1) < 1 := by
    by_contra h
    push_neg at h
    have h2 := one_le_pow₀ (n := p - 1) h
    rw [val_prim_root hζ] at h2
    exact absurd hpv (not_lt.mpr h2)
  have hnat : ∀ n : ℕ, v (n : C) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact Valuation.map_add_le v ih (by rw [map_one])
  have hdec : ∀ n : ℕ, ∃ s : C, v s ≤ 1 ∧ ζ ^ n - 1 = (ζ - 1) * (n + (ζ - 1) * s) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs1, hs⟩ := ih
      refine ⟨n + ζ * s, Valuation.map_add_le v (hnat n) (by rw [map_mul]; exact mul_le_one' hζ1 hs1), ?_⟩
      push_cast
      linear_combination ζ * hs
  choose s hs1 hs using hdec
  have h1 : ∑ a, u0 ω a * ζ ^ a.val = ∑ a, wt ω a * (ζ ^ a.val - 1) := by
    have := hω.lam_eq (fun a => ζ ^ a.val)
    simpa [lam, ZMod.val_zero] using this
  have h2 : ∑ a, wt ω a * ω a = (p : C) - 1 := by
    have := hω.lam_eq ω
    rw [hω.lam_omega, hω.zero] at this
    simpa using this.symm
  have hγ : ∑ a, u0 ω a * ζ ^ a.val = (ζ - 1) * (((p : C) - 1) +
      (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val)) := by
    rw [h1, ← h2]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs]
    ring
  have hδ : v (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val) < 1 := by
    apply Valuation.map_add_lt v
    · apply Valuation.map_sum_lt v one_ne_zero
      intro a _
      rw [map_mul]
      calc v (wt ω a) * v ((a.val : C) - ω a) ≤ 1 * v ((a.val : C) - ω a) := by
            gcongr; exact hω.wt_int a
        _ < 1 := by rw [one_mul, Valuation.map_sub_swap]; exact hω.cong a
    · rw [map_mul]
      have hsum : v (∑ a, wt ω a * s a.val) ≤ 1 :=
        Valuation.map_sum_le v fun a _ => by rw [map_mul]; exact mul_le_one' (hω.wt_int a) (hs1 _)
      calc v (ζ - 1) * v (∑ a, wt ω a * s a.val) ≤ v (ζ - 1) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hπ1
  have hp1 : v ((p : C) - 1) = 1 := by
    have hnd : ¬ (p : ℤ) ∣ (p : ℤ) - 1 := by
      intro hd
      have h1' : (p : ℤ) ∣ 1 := by simpa using dvd_sub (dvd_refl (p : ℤ)) hd
      have := Int.eq_one_of_dvd_one (by positivity) h1'
      omega
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    exact this
  have hunit : v ((p : C) - 1 + (∑ a, wt ω a * ((a.val : C) - ω a) +
      (ζ - 1) * ∑ a, wt ω a * s a.val)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left v (by rw [hp1]; exact hδ), hp1]
  rw [hγ, map_mul, hunit, mul_one]
  exact val_prim_root hζ

/- English proof (translation)
Establish `hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0`. Introduce `h hh`. Use `hω.sep h 0 hh` as an intermediate fact. Rewrite `this` using `[hω.zero, sub_zero]`. Introduce `h0`.

Rewrite `this` using `[h0, map_zero]`. Conclude with `zero_ne_one this`. Establish `hp2 : 2 ≤ p` using `hp.out.two_le`. Establish `hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1`. Introduce `h hh`.

Establish `e1` using `hω.pow h`. Establish `: ω h ^ (p - 1) * ω h = 1 * ω h`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]`. Conclude with `mul_right_cancel₀ (hω0 h hh) this`. Establish `hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1`.

Introduce `h hh`. Simplify using `only [wt]`. Rewrite using `[← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]`. Establish `hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b`. Introduce `a b`.

Simplify using `only [wt, hω.mul, mul_pow]`. Establish `hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h`. Introduce `h hh`. Establish `hi : h⁻¹ ≠ 0` using `inv_ne_zero hh`. Establish `e1` using `hwt h⁻¹ hi`.

Establish `e2 : ω h⁻¹ * ω h = 1` using `by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hwt0 : wt ω 0 = 0`. Simplify using `only [wt, hω.zero]; exact zero_pow (by omega)`. Establish `hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω`.

Introduce `h hh`. Use `Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh)) (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)` as an intermediate fact. Simplify using `only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this`. Simplify using `only [sS]`. Conclude with `this.symm`.

Establish `hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b`. Introduce `h hh b`. Simplify using `only [u0]`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality.

Simplify using `only [mul_zero, if_true, hwt0]`. Use `nth_rewrite 1 [hS h hh]`. Expand and normalize the polynomial expressions, which then agree. Establish `: h⁻¹ * b ≠ 0` using `mul_ne_zero (inv_ne_zero hh) hb`. Simplify using `only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]`.

Use function extensionality and compare the values at `h`. Simplify using `only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]`. Distinguish the cases in `hh : h = 0`. Substitute `hh` using the available equality. Simplify using `only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]`.

Rewrite using `[← Finset.mul_sum]`. Simplify using `only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `[sS]`. Establish `hb` using `Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh)) (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val) (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)`. Rewrite using `[← hb]`.

Simplify using `only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourierMap_smul_lambdaWeight {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by
  have hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0 := by
    intro h hh
    have := hω.sep h 0 hh
    rw [hω.zero, sub_zero] at this
    intro h0
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1 := by
    intro h hh
    have e1 := hω.pow h
    have : ω h ^ (p - 1) * ω h = 1 * ω h := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]
    exact mul_right_cancel₀ (hω0 h hh) this
  have hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1 := by
    intro h hh
    simp only [wt]
    rw [← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]
  have hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b := by
    intro a b; simp only [wt, hω.mul, mul_pow]
  have hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h := by
    intro h hh
    have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have e1 := hwt h⁻¹ hi
    have e2 : ω h⁻¹ * ω h = 1 := by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]
    calc wt ω h⁻¹ = wt ω h⁻¹ * (ω h⁻¹ * ω h) := by rw [e2, mul_one]
      _ = ω h := by rw [← mul_assoc, e1, one_mul]
  have hwt0 : wt ω 0 = 0 := by
    simp only [wt, hω.zero]; exact zero_pow (by omega)
  have hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω := by
    intro h hh
    have := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)
    simp only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this
    simp only [sS]; exact this.symm
  have hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b := by
    intro h hh b
    simp only [u0]
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, if_true, hwt0]
      nth_rewrite 1 [hS h hh]; ring
    · have : h⁻¹ * b ≠ 0 := mul_ne_zero (inv_ne_zero hh) hb
      simp only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]
  funext h
  simp only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]
  by_cases hh : h = 0
  · subst hh
    simp only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]
    rw [← Finset.mul_sum]
    simp only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [sS]
  · have hb := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val)
      (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)
    rw [← hb]
    simp only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end ReciprocityTheory.PGsh.Up.U3
