import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

/- English proof (translation)
Establish `hφ : ∀ x ∈ m, φ x ∈ m` using `fun x hx => by`. Establish `h1` using `Ideal.pow_le_self (two_ne_zero) (h x hx)`. Establish `h2` using `m.add_mem h1 (m.mul_mem_left 2 hx)`. Simplify using `using h2`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `y hy`. Simplify `hy)` using `using h y (by simpa`. Consider the case `succ n ih`. Introduce `y hy`.

Rewrite `hy` using `[pow_succ]`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Establish `e : φ (a * b) - 2 ^ (n + 1 + 1) * (a * b) = (φ a - 2 ^ (n + 1) * a) * φ b + (2 ^ (n + 1) * a) * (φ b - 2 * b)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Use `Ideal.mul_mem_mul (ih a ha) (hφ b hb)` as an intermediate fact. Rewrite `this` using `[← pow_succ]`. Then use the resulting hypothesis.

Use `Ideal.mul_mem_mul (Ideal.mul_mem_left _ (2 ^ (n + 1)) ha) (h b hb)` as an intermediate fact. Rewrite `this` using `[← pow_add]`. Conclude with `this`. Introduce `a b ha hb`. Establish `e : φ (a + b) - 2 ^ (n + 1 + 1) * (a + b) = (φ a - 2 ^ (n + 1 + 1) * a) + (φ b - 2 ^ (n + 1 + 1) * b)`.

Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ ha hb`.
-/
theorem map_sub_two_pow_mul_mem {R : Type} [CommRing R] (m : Ideal R) (φ : R →+* R)
    (h : ∀ x ∈ m, φ x - 2 * x ∈ m ^ 2) (n : ℕ) :
    ∀ y ∈ m ^ (n + 1), φ y - 2 ^ (n + 1) * y ∈ m ^ (n + 2) := by
  have hφ : ∀ x ∈ m, φ x ∈ m := fun x hx => by
    have h1 := Ideal.pow_le_self (two_ne_zero) (h x hx)
    have h2 := m.add_mem h1 (m.mul_mem_left 2 hx)
    simpa using h2
  induction n with
  | zero =>
    intro y hy
    simpa using h y (by simpa using hy)
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have e : φ (a * b) - 2 ^ (n + 1 + 1) * (a * b) =
          (φ a - 2 ^ (n + 1) * a) * φ b + (2 ^ (n + 1) * a) * (φ b - 2 * b) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul (ih a ha) (hφ b hb)
        rwa [← pow_succ] at this
      · have := Ideal.mul_mem_mul (Ideal.mul_mem_left _ (2 ^ (n + 1)) ha) (h b hb)
        rw [← pow_add] at this
        exact this
    · intro a b ha hb
      have e : φ (a + b) - 2 ^ (n + 1 + 1) * (a + b) =
          (φ a - 2 ^ (n + 1 + 1) * a) + (φ b - 2 ^ (n + 1 + 1) * b) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ (n + 2)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih`.

Introduce `x hx`. Use `set m := maximalIdeal RA with hm`. Establish `hy` using `ih x hx`. Establish `hle : Ideal.map ψ mB ≤ m ^ (n + 2)` using `Ideal.map_le_iff_le_comap.2 ih`. Establish `hz : ψ (φB x - 2 * x) ∈ m ^ (n + 3)`.

Establish `h2 : ψ (φB x - 2 * x) ∈ Ideal.map ψ (mB ^ 2)` using `Ideal.mem_map_of_mem _ (hB x hx)`. Rewrite `h2` using `[Ideal.map_pow]`. Establish `h3 : (Ideal.map ψ mB) ^ 2 ≤ (m ^ (n + 2)) ^ 2` using `Ideal.pow_right_mono hle 2`. Establish `h4` using `h3 h2`. Rewrite `h4` using `[← pow_mul]`.

Conclude with `Ideal.pow_le_pow_right (by omega) h4`. Establish `hd` using `map_sub_two_pow_mul_mem m φA hA (n + 1) _ hy`. Establish `e : (2 ^ (n + 2) - 2 : RA) * ψ x = ψ (φB x - 2 * x) - (φA (ψ x) - 2 ^ (n + 2) * ψ x)`. Rewrite using `[map_sub, map_mul, hc, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h5 : (2 ^ (n + 2) - 2 : RA) * ψ x ∈ m ^ (n + 3)`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ hz hd`. Establish `hne : (2 ^ (n + 2) - 2 : k) ≠ 0`. Establish `: ((2 ^ (n + 2) - 2 : ℤ) : k) ≠ 0`.

Rewrite using `[Int.cast_ne_zero]`. Establish `: (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n` using `by ring`. Establish `h6 : (0 : ℤ) < 2 ^ n` using `by positivity`. Use linear arithmetic over natural numbers and integers. Simplify using `using this`.

Establish `h7` using `Ideal.mul_mem_left _ (algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹) h5`. Establish `e2 : algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹ * ((2 ^ (n + 2) - 2 : RA) * ψ x) = ψ x`. Establish `: (2 ^ (n + 2) - 2 : RA) = algebraMap k RA (2 ^ (n + 2) - 2 : k)`. Rewrite using `[map_sub, map_pow, map_ofNat]`. Rewrite using `[this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]`.

Rewrite `h7` using `[e2]`. Then use the resulting hypothesis. Establish `hinf` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal RA) (Ideal.IsPrime.ne_top inferInstance)`. Establish `: ψ x ∈ (⨅ i : ℕ, maximalIdeal RA ^ i)`. Use `(Submodule.mem_iInf _).2 fun i => ?_` and prove the remaining obligations. Conclude with `Ideal.pow_le_pow_right (by omega) (key i x hx)`.

Rewrite `this` using `[hinf]`. Simplify using `using this`.
-/
theorem map_eq_zero_of_commute_doubling {k RA RB : Type} [Field k] [CharZero k] [CommRing RA]
    [IsLocalRing RA] [IsNoetherianRing RA] [Algebra k RA] [CommRing RB] (mB : Ideal RB)
    (φA : RA →+* RA) (φB : RB →+* RB) (ψ : RB →+* RA) (hc : ∀ x, ψ (φB x) = φA (ψ x))
    (h1 : ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ 2)
    (hA : ∀ x ∈ maximalIdeal RA, φA x - 2 * x ∈ maximalIdeal RA ^ 2)
    (hB : ∀ x ∈ mB, φB x - 2 * x ∈ mB ^ 2) (x : RB) (hx : x ∈ mB) : ψ x = 0 := by
  have key : ∀ n : ℕ, ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ (n + 2) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      intro x hx
      set m := maximalIdeal RA with hm
      have hy := ih x hx
      have hle : Ideal.map ψ mB ≤ m ^ (n + 2) := Ideal.map_le_iff_le_comap.2 ih
      have hz : ψ (φB x - 2 * x) ∈ m ^ (n + 3) := by
        have h2 : ψ (φB x - 2 * x) ∈ Ideal.map ψ (mB ^ 2) := Ideal.mem_map_of_mem _ (hB x hx)
        rw [Ideal.map_pow] at h2
        have h3 : (Ideal.map ψ mB) ^ 2 ≤ (m ^ (n + 2)) ^ 2 := Ideal.pow_right_mono hle 2
        have h4 := h3 h2
        rw [← pow_mul] at h4
        exact Ideal.pow_le_pow_right (by omega) h4
      have hd := map_sub_two_pow_mul_mem m φA hA (n + 1) _ hy
      have e : (2 ^ (n + 2) - 2 : RA) * ψ x = ψ (φB x - 2 * x) - (φA (ψ x) - 2 ^ (n + 2) * ψ x) := by
        rw [map_sub, map_mul, hc, map_ofNat]; ring
      have h5 : (2 ^ (n + 2) - 2 : RA) * ψ x ∈ m ^ (n + 3) := by
        rw [e]; exact Ideal.sub_mem _ hz hd
      have hne : (2 ^ (n + 2) - 2 : k) ≠ 0 := by
        have : ((2 ^ (n + 2) - 2 : ℤ) : k) ≠ 0 := by
          rw [Int.cast_ne_zero]
          have : (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
          have h6 : (0 : ℤ) < 2 ^ n := by positivity
          omega
        simpa using this
      have h7 := Ideal.mul_mem_left _ (algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹) h5
      have e2 : algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹ * ((2 ^ (n + 2) - 2 : RA) * ψ x) = ψ x := by
        have : (2 ^ (n + 2) - 2 : RA) = algebraMap k RA (2 ^ (n + 2) - 2 : k) := by
          rw [map_sub, map_pow, map_ofNat]
        rw [this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
      rwa [e2] at h7
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal RA) (Ideal.IsPrime.ne_top inferInstance)
  have : ψ x ∈ (⨅ i : ℕ, maximalIdeal RA ^ i) := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Ideal.pow_le_pow_right (by omega) (key i x hx)
  rw [hinf] at this
  simpa using this

section Tan

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] (ev : R →ₐ[k] k)

def kerPart (x : R) : RingHom.ker ev :=
  ⟨x - algebraMap k R (ev x), by simp [RingHom.mem_ker]⟩

def cotPart (x : R) : (RingHom.ker ev).Cotangent := (RingHom.ker ev).toCotangent (kerPart ev x)

/- English proof (translation)
Rewrite using `[cotPart, cotPart, cotPart, ← map_add]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [kerPart, map_add, Submodule.coe_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cotPart_add (x y : R) : cotPart ev (x + y) = cotPart ev x + cotPart ev y := by
  rw [cotPart, cotPart, cotPart, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [kerPart, map_add, Submodule.coe_add]
  ring

/- English proof (translation)
Establish `: kerPart ev (algebraMap k R a) = 0` using `Subtype.ext (by simp [kerPart])`. Rewrite using `[cotPart, this, map_zero]`.
-/
theorem cotPart_algebraMap (a : k) : cotPart ev (algebraMap k R a) = 0 := by
  have : kerPart ev (algebraMap k R a) = 0 := Subtype.ext (by simp [kerPart])
  rw [cotPart, this, map_zero]

/- English proof (translation)
Rewrite using `[← algebraMap_smul R (ev x), ← algebraMap_smul R (ev y), cotPart, cotPart, cotPart, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]`. Establish `e : ((kerPart ev (x * y) : R) - (algebraMap k R (ev x) • kerPart ev y + algebraMap k R (ev y) • kerPart ev x : RingHom.ker ev)) = (kerPart ev x : R) * (kerPart ev y : R)`. Simplify using `only [kerPart, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, pow_two]`.

Conclude with `Ideal.mul_mem_mul (kerPart ev x).2 (kerPart ev y).2`.
-/
theorem cotPart_mul (x y : R) : cotPart ev (x * y) = ev x • cotPart ev y + ev y • cotPart ev x := by
  rw [← algebraMap_smul R (ev x), ← algebraMap_smul R (ev y), cotPart, cotPart, cotPart, ← map_smul,
    ← map_smul, ← map_add, Ideal.toCotangent_eq]
  have e : ((kerPart ev (x * y) : R) - (algebraMap k R (ev x) • kerPart ev y + algebraMap k R (ev y) • kerPart ev x :
      RingHom.ker ev)) = (kerPart ev x : R) * (kerPart ev y : R) := by
    simp only [kerPart, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [e, pow_two]
  exact Ideal.mul_mem_mul (kerPart ev x).2 (kerPart ev y).2

def tanHom (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) : R →ₐ[k] DualNumber k where
  toFun x := TrivSqZeroExt.inl (ev x) + TrivSqZeroExt.inr (lam (cotPart ev x))
  map_one' := by
    have := cotPart_algebraMap ev 1
    rw [map_one] at this
    ext <;> simp [this]
  map_mul' x y := by
    ext
    · simp
    · simp [cotPart_mul, mul_comm]
  map_zero' := by
    have := cotPart_algebraMap ev 0
    rw [map_zero] at this
    ext <;> simp [this]
  map_add' x y := by
    ext
    · simp
    · simp [cotPart_add]
  commutes' a := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [cotPart_algebraMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Simplify using `[tanHom]`.
-/
theorem tanHom_fst (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) : (tanHom ev lam x).fst = ev x := by
  simp [tanHom]

/- English proof (translation)
Simplify using `[tanHom]`.
-/
theorem tanHom_snd (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) :
    (tanHom ev lam x).snd = lam (cotPart ev x) := by
  simp [tanHom]

/- English proof (translation)
Establish `h0 : ev x = 0` using `by rw [← tanHom_fst ev 0, h]; rfl`. Establish `h1 : cotPart ev x = 0`. Use `(Module.forall_dual_apply_eq_zero_iff k _).1 fun lam => ?_` and prove the remaining obligations. Rewrite using `[← tanHom_snd ev lam, h]`. Both sides reduce to the same expression.

Rewrite `h1` using `[cotPart, Ideal.toCotangent_eq_zero]`. Simplify `h1` using `[kerPart, h0]`.
-/
theorem mem_sq_of_tanHom_eq_zero (x : R) (h : ∀ lam, tanHom ev lam x = 0) : x ∈ RingHom.ker ev ^ 2 := by
  have h0 : ev x = 0 := by rw [← tanHom_fst ev 0, h]; rfl
  have h1 : cotPart ev x = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun lam => ?_
    rw [← tanHom_snd ev lam, h]; rfl
  rw [cotPart, Ideal.toCotangent_eq_zero] at h1
  simpa [kerPart, h0] using h1

/- English proof (translation)
The claim follows from `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev : R →+* k) (fun a => ⟨algebraMap k R a, by simp⟩))`.
-/
theorem ker_eq_maximalIdeal_of_algHom [IsLocalRing R] : RingHom.ker ev = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev : R →+* k)
    (fun a => ⟨algebraMap k R a, by simp⟩))

end Tan

end GlobalTheory.LieFaithful
