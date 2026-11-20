import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.LinCore
open Polynomial

section
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]

/- English proof (translation)
Take `⟨c, d, hcd⟩` from `h`. Use `congrArg (fun p => aeval f p y) hcd` as an intermediate fact. Simplify `this.symm` using `[Module.End.mul_apply, ha, hb]`.
-/
theorem eq_zero_of_isCoprime (f : Module.End 𝕜 V) {a b : ℚ[X]} (h : IsCoprime a b) {y : V}
    (ha : aeval f a y = 0) (hb : aeval f b y = 0) : y = 0 := by
  obtain ⟨c, d, hcd⟩ := h
  have := congrArg (fun p => aeval f p y) hcd
  simpa [Module.End.mul_apply, ha, hb] using this.symm

/- English proof (translation)
Establish `hp : ∀ n : ℕ, ∀ x ∈ K, (f ^ n) (L x) = L ((g ^ n) x)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `x hx`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hL x hx, ih _ (hK x hx)]`. Introduce `x hx`. Simplify using `only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul_of_tower, hp _ x hx]`.
-/
theorem aeval_intertwine (f g L : Module.End 𝕜 V) (K : Submodule 𝕜 V)
    (hK : ∀ x ∈ K, g x ∈ K) (hL : ∀ x ∈ K, f (L x) = L (g x)) (p : ℚ[X]) :
    ∀ x ∈ K, aeval f p (L x) = L (aeval g p x) := by
  have hp : ∀ n : ℕ, ∀ x ∈ K, (f ^ n) (L x) = L ((g ^ n) x) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hL x hx, ih _ (hK x hx)]
  intro x hx
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smul_of_tower, hp _ x hx]

/- English proof (translation)
Establish `hp : ∀ n : ℕ, ∀ x y, B ((f ^ n) x) y = B x ((g ^ n) y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x y`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `x y`. Rewrite using `[pow_succ', pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]`. Simplify using `only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul_of_tower, hp]`.
-/
theorem aeval_adjoint (B : LinearMap.BilinForm 𝕜 V) (f g : Module.End 𝕜 V)
    (h : ∀ x y, B (f x) y = B x (g y)) (p : ℚ[X]) (x y : V) :
    B (aeval f p x) y = B x (aeval g p y) := by
  have hp : ∀ n : ℕ, ∀ x y, B ((f ^ n) x) y = B x ((g ^ n) y) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ', pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smul_of_tower, hp]

end

/- English proof (translation)
Establish `hp : ∀ i : ℕ, u ^ i * v ^ i = 1`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [pow_succ, pow_succ', _root_.mul_assoc, ← _root_.mul_assoc u, h, _root_.one_mul, ih]`.

Rewrite using `[aeval_eq_sum_range v, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ R.natDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `: u ^ R.natDegree = u ^ (R.natDegree - i) * u ^ i`. Rewrite using `[← pow_add, Nat.sub_add_cancel hi']`.

Rewrite using `[map_mul, aeval_C, map_pow, aeval_X, mul_smul_comm, this, _root_.mul_assoc, hp, _root_.mul_one, Algebra.smul_def]`.
-/
theorem aeval_rev {A : Type} [Ring A] [Algebra ℚ A] (u v : A) (h : u * v = 1) (R : ℚ[X]) :
    aeval u (∑ i ∈ Finset.range (R.natDegree + 1), C (R.coeff i) * X ^ (R.natDegree - i))
      = u ^ R.natDegree * aeval v R := by
  have hp : ∀ i : ℕ, u ^ i * v ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_succ', _root_.mul_assoc, ← _root_.mul_assoc u, h, _root_.one_mul, ih]
  rw [aeval_eq_sum_range v, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : u ^ R.natDegree = u ^ (R.natDegree - i) * u ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [map_mul, aeval_C, map_pow, aeval_X, mul_smul_comm, this, _root_.mul_assoc, hp, _root_.mul_one,
    Algebra.smul_def]

/- English proof (translation)
Use `⟨_, ?_, by rw [aeval_rev u v h R, hv, mul_zero]⟩` and prove the remaining obligations. Introduce `β hβ`. Establish `hR0 : R ≠ 0`. Introduce and unpack `rfl`. Use `hR 2 (by simp)` as an intermediate fact.

Evaluate the numerical expressions using `at this`. Distinguish the cases in `hb : β = 0`. It suffices to derive a contradiction. Substitute `hb` using the available equality. Rewrite `hβ` using `[map_sum, Finset.sum_eq_single R.natDegree]`.

Simplify using `[hR0] at hβ`. Introduce `i hi hne`. Establish `hi' : i ≤ R.natDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `: R.natDegree - i ≠ 0` using `by omega`. Simplify using `[this]`.

Simplify using the standard rewrite rules. Rewrite `hβ` using `[aeval_rev β β⁻¹ (mul_inv_cancel₀ hb) R]`. Establish `h1` using `hR _ ((mul_eq_zero.mp hβ).resolve_left (pow_ne_zero _ hb))`. Rewrite `h1` using `[norm_inv]`. Conclude with `(inv_le_one₀ (norm_pos_iff.mpr hb)).mp h1`.
-/
theorem exists_rev {A : Type} [Ring A] [Algebra ℚ A] (u v : A) (h : u * v = 1) (R : ℚ[X])
    (hR : ∀ β : ℂ, aeval β R = 0 → ‖β‖ ≤ 1) (hv : aeval v R = 0) :
    ∃ R' : ℚ[X], (∀ β : ℂ, aeval β R' = 0 → 1 ≤ ‖β‖) ∧ aeval u R' = 0 := by
  refine ⟨_, ?_, by rw [aeval_rev u v h R, hv, mul_zero]⟩
  intro β hβ
  have hR0 : R ≠ 0 := by
    rintro rfl
    have := hR 2 (by simp)
    norm_num at this
  by_cases hb : β = 0
  · exfalso
    subst hb
    rw [map_sum, Finset.sum_eq_single R.natDegree] at hβ
    · simp [hR0] at hβ
    · intro i hi hne
      have hi' : i ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : R.natDegree - i ≠ 0 := by omega
      simp [this]
    · simp
  · rw [aeval_rev β β⁻¹ (mul_inv_cancel₀ hb) R] at hβ
    have h1 := hR _ ((mul_eq_zero.mp hβ).resolve_left (pow_ne_zero _ hb))
    rw [norm_inv] at h1
    exact (inv_le_one₀ (norm_pos_iff.mpr hb)).mp h1

/- English proof (translation)
Rewrite using `[aeval_comp, map_mul, aeval_C, aeval_X, Algebra.smul_def]`.
-/
theorem aeval_scale {A : Type} [Ring A] [Algebra ℚ A] (u : A) (c : ℚ) (R : ℚ[X]) :
    aeval u (R.comp (C c * X)) = aeval (c • u) R := by
  rw [aeval_comp, map_mul, aeval_C, aeval_X, Algebra.smul_def]

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ q ih`. Take `⟨v, hv⟩` from `ih`. Use `⟨C (q : ℚ) + v + X * v, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hv]`. Simplify using `only [Nat.cast_add, Nat.cast_one, map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_binom (q : ℕ) : ∃ v : ℚ[X], (X + 1) ^ q = 1 + X * (C (q : ℚ) + X * v) := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨C (q : ℚ) + v + X * v, ?_⟩
    rw [pow_succ, hv]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

section
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_binom q`. Take `⟨n, hn⟩` from `hT`. Use `set u : ℚ[X] := C (q : ℚ) + X * v with hu`. Establish `h1 : Φ * T = aeval T (X * u) * Φ`. Establish `h2` using `congrArg (aeval T) hv`.

Rewrite `h2` using `[map_pow, map_add, map_add, map_one, aeval_X]`. Rewrite `h` using `[h2, mul_add, add_mul, _root_.mul_one, _root_.one_mul, add_comm Φ]`. Conclude with `add_right_cancel h`. Establish `h2 : ∀ k : ℕ, Φ * T ^ k = aeval T ((X * u) ^ k) * Φ`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ← _root_.mul_assoc, ih, _root_.mul_assoc, h1, ← _root_.mul_assoc, ← map_mul, ← pow_succ]`. Establish `hcop : IsCoprime u X`.

Establish `hq' : (q : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hq`. Use `⟨C (q : ℚ)⁻¹, - (C (q : ℚ)⁻¹ * v), ?_⟩` and prove the remaining obligations. Establish `: (C (q : ℚ)⁻¹ * C (q : ℚ) : ℚ[X]) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hq', map_one]`. Rewrite using `[hu]`.

Take the linear combination `this`. Establish `h3 : (T ^ (i + 1)) (Φ x) = 0`. Use `eq_zero_of_isCoprime T (hcop.pow (m := i + 1) (n := n)) ?_ ?_` and prove the remaining obligations. Use `congrArg (fun f : Module.End 𝕜 V => f x) (h2 (i + 1))` as an intermediate fact. Simplify using `only [Module.End.mul_apply, hx, map_zero] at this`.

Rewrite `this` using `[mul_pow, mul_comm, map_mul, map_pow (aeval T) X, aeval_X, Module.End.mul_apply]`. Conclude with `this.symm`. Simplify using `[hn]`. Use `⟨h3, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩ : (X : ℚ[X]) ∣ u ^ i - C (q : ℚ) ^ i` from `Dvd.dvd.trans ⟨v, by rw [hu]; ring⟩ (sub_dvd_pow_sub_pow u (C (q : ℚ)) i)`.

Establish `h4 : (X * u) ^ i = C ((q : ℚ) ^ i) * X ^ i + w * X ^ (i + 1)`. Rewrite using `[mul_pow, map_pow]`. Take the linear combination `X ^ i * hw`. Use `congrArg (fun f : Module.End 𝕜 V => f x) (h2 i)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, h4, map_add, map_mul, map_pow (aeval T) X, aeval_X, aeval_C, LinearMap.add_apply, h3, map_zero, add_zero] at this`.

Rewrite using `[this, LinearMap.smul_apply, LinearMap.map_smul_of_tower, Algebra.algebraMap_eq_smul_one]`. Simplify using the standard rewrite rules.
-/
theorem graded_comm (T Φ : Module.End 𝕜 V) (q : ℕ) (hq : q ≠ 0) (hT : IsNilpotent T)
    (h : Φ * (T + 1) = (T + 1) ^ q * Φ) (i : ℕ) (x : V) (hx : (T ^ (i + 1)) x = 0) :
    (T ^ (i + 1)) (Φ x) = 0 ∧ Φ ((T ^ i) x) = (T ^ i) ((((q : ℚ) ^ i) • Φ) x) := by
  obtain ⟨v, hv⟩ := exists_binom q
  obtain ⟨n, hn⟩ := hT
  set u : ℚ[X] := C (q : ℚ) + X * v with hu
  have h1 : Φ * T = aeval T (X * u) * Φ := by
    have h2 := congrArg (aeval T) hv
    rw [map_pow, map_add, map_add, map_one, aeval_X] at h2
    rw [h2, mul_add, add_mul, _root_.mul_one, _root_.one_mul, add_comm Φ] at h
    exact add_right_cancel h
  have h2 : ∀ k : ℕ, Φ * T ^ k = aeval T ((X * u) ^ k) * Φ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← _root_.mul_assoc, ih, _root_.mul_assoc, h1, ← _root_.mul_assoc, ← map_mul,
        ← pow_succ]
  have hcop : IsCoprime u X := by
    have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    refine ⟨C (q : ℚ)⁻¹, - (C (q : ℚ)⁻¹ * v), ?_⟩
    have : (C (q : ℚ)⁻¹ * C (q : ℚ) : ℚ[X]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq', map_one]
    rw [hu]
    linear_combination this
  have h3 : (T ^ (i + 1)) (Φ x) = 0 := by
    refine eq_zero_of_isCoprime T (hcop.pow (m := i + 1) (n := n)) ?_ ?_
    · have := congrArg (fun f : Module.End 𝕜 V => f x) (h2 (i + 1))
      simp only [Module.End.mul_apply, hx, map_zero] at this
      rw [mul_pow, mul_comm, map_mul, map_pow (aeval T) X, aeval_X, Module.End.mul_apply] at this
      exact this.symm
    · simp [hn]
  refine ⟨h3, ?_⟩
  obtain ⟨w, hw⟩ : (X : ℚ[X]) ∣ u ^ i - C (q : ℚ) ^ i :=
    Dvd.dvd.trans ⟨v, by rw [hu]; ring⟩ (sub_dvd_pow_sub_pow u (C (q : ℚ)) i)
  have h4 : (X * u) ^ i = C ((q : ℚ) ^ i) * X ^ i + w * X ^ (i + 1) := by
    rw [mul_pow, map_pow]
    linear_combination X ^ i * hw
  have := congrArg (fun f : Module.End 𝕜 V => f x) (h2 i)
  simp only [Module.End.mul_apply, h4, map_add, map_mul, map_pow (aeval T) X, aeval_X, aeval_C,
    LinearMap.add_apply, h3, map_zero, add_zero] at this
  rw [this, LinearMap.smul_apply, LinearMap.map_smul_of_tower, Algebra.algebraMap_eq_smul_one]
  simp

/- English proof (translation)
Use `aeval_intertwine _ _ (T ^ i) (LinearMap.ker (T ^ (i + 1))) ?_ ?_ p x hx` and prove the remaining obligations. Introduce `y hy`. Use `(graded_comm T Φ q hq hT h i y hy).1` as an intermediate fact. Simplify using `[LinearMap.map_smul_of_tower, this]`. Introduce `y hy`.

Use `(graded_comm T Φ q hq hT h i y hy).2` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, LinearMap.map_smul_of_tower, this, mul_smul]`.
-/
theorem graded_aeval (T Φ : Module.End 𝕜 V) (q : ℕ) (hq : q ≠ 0) (hT : IsNilpotent T)
    (h : Φ * (T + 1) = (T + 1) ^ q * Φ) (i : ℕ) (c : ℚ) (p : ℚ[X]) (x : V)
    (hx : (T ^ (i + 1)) x = 0) :
    aeval (c • Φ) p ((T ^ i) x) = (T ^ i) (aeval ((c * (q : ℚ) ^ i) • Φ) p x) := by
  refine aeval_intertwine _ _ (T ^ i) (LinearMap.ker (T ^ (i + 1))) ?_ ?_ p x hx
  · intro y hy
    have := (graded_comm T Φ q hq hT h i y hy).1
    simp [LinearMap.map_smul_of_tower, this]
  · intro y hy
    have := (graded_comm T Φ q hq hT h i y hy).2
    simp only [LinearMap.smul_apply, LinearMap.map_smul_of_tower, this, mul_smul]

omit [CharZero 𝕜] [Module ℚ V] [IsScalarTower ℚ 𝕜 V] in
/- English proof (translation)
Take `⟨n, hn⟩` from `hT`. Establish `h2 : ∀ (k : ℕ) x, (T ^ (2 + k)) x = 0 → (T ^ 2) x = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x hx`.

Rewrite `hx` using `[add_zero]`. Then use the resulting hypothesis. Consider the case `succ k ih`. Introduce `x hx`. Apply `ih` to reduce the goal to its premises. Rewrite using `[pow_add, Module.End.mul_apply]`.

Apply `h32` to reduce the goal to its premises. Rewrite using `[← Module.End.mul_apply, ← pow_add, add_assoc, add_comm 1 k]` and apply the resulting hypothesis. Use `h2 n x (by rw [pow_add, hn, mul_zero, LinearMap.zero_apply])` as an intermediate fact. Rewrite `this` using `[pow_two, Module.End.mul_apply]`. Then use the resulting hypothesis.
-/
theorem sq_eq_zero_of_cube (T : Module.End 𝕜 V) (hT : IsNilpotent T)
    (h32 : ∀ x, (T ^ (2 + 1)) x = 0 → (T ^ 2) x = 0) (x : V) : T (T x) = 0 := by
  obtain ⟨n, hn⟩ := hT
  have h2 : ∀ (k : ℕ) x, (T ^ (2 + k)) x = 0 → (T ^ 2) x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; rwa [add_zero] at hx
    | succ k ih =>
      intro x hx
      apply ih
      rw [pow_add, Module.End.mul_apply]
      apply h32
      rwa [← Module.End.mul_apply, ← pow_add, add_assoc, add_comm 1 k]
  have := h2 n x (by rw [pow_add, hn, mul_zero, LinearMap.zero_apply])
  rwa [pow_two, Module.End.mul_apply] at this

omit [CharZero 𝕜] [Module ℚ V] [IsScalarTower ℚ 𝕜 V] in
/- English proof (translation)
Set `L : LinearMap.range T →ₗ[𝕜] W` to `(f.domRestrict (LinearMap.range T)).codRestrict W (by`. Introduce and unpack `⟨_, x, rfl⟩`. Conclude with `h1 x)`. Establish `hL : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce and unpack `⟨_, x, rfl⟩ hx`. Conclude with `Subtype.ext (h2 x (congrArg Subtype.val hx))`. Establish `h5` using `LinearMap.finrank_le_finrank_of_injective hL`. Establish `h6` using `LinearMap.finrank_range_add_finrank_ker T`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_of_injective [FiniteDimensional 𝕜 V] (T f : Module.End 𝕜 V)
    (W : Submodule 𝕜 V) (h1 : ∀ x, f (T x) ∈ W) (h2 : ∀ x, f (T x) = 0 → T x = 0) :
    Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker T) + Module.finrank 𝕜 W := by
  let L : LinearMap.range T →ₗ[𝕜] W :=
    (f.domRestrict (LinearMap.range T)).codRestrict W (by
      rintro ⟨_, x, rfl⟩
      exact h1 x)
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨_, x, rfl⟩ hx
    exact Subtype.ext (h2 x (congrArg Subtype.val hx))
  have h5 := LinearMap.finrank_le_finrank_of_injective hL
  have h6 := LinearMap.finrank_range_add_finrank_ker T
  omega

/- English proof (translation)
Establish `hq0 : q ≠ 0` using `by omega`. Establish `hqR : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hqQ : (q : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hq0`. Use `set Q : ℚ[X] := (X - C (q : ℚ)) * P with hQ`. Establish `hQr : ∀ β : ℂ, aeval β Q = 0 → ‖β‖ ≤ q`.

Introduce `β hβ`. Rewrite `hβ` using `[hQ, map_mul, mul_eq_zero]`. Break down `hβ with hβ | hβ` into its components or cases. Establish `: β = q` using `by simpa [sub_eq_zero] using hβ`. Simplify using `[this]`.

Conclude with `(hP β hβ).le`. Establish `hQk : ∀ x, T x = 0 → aeval Φ Q x = 0`. Introduce `x hx`. Use `hW _ (hPW x hx)` as an intermediate fact. Rewrite using `[hQ, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, this, Algebra.algebraMap_eq_smul_one]`.

Simplify using `[Nat.cast_smul_eq_nsmul]`. Establish `hTT : ∀ (i : ℕ) x, (T ^ (i + 1)) x = T ((T ^ i) x)`. Introduce `i x`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `hR : ∀ i : ℕ, ∃ R : ℚ[X], (∀ β : ℂ, aeval β R = 0 → ‖β‖ ≤ q) ∧ ∀ x, (T ^ i) x = 0 → aeval Φ R x = 0`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => exact ⟨1, by simp, fun x hx => by simpa using hx⟩`. Consider the case `succ i ih`. Take `⟨R, hR1, hR2⟩` from `ih`.

Use `⟨R * Q.comp (C ((q : ℚ) ^ i) * X), fun β hβ => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hβ` using `[map_mul, mul_eq_zero]`. Break down `hβ with hβ | hβ` into its components or cases. Conclude with `hR1 β hβ`. Rewrite `hβ` using `[aeval_scale]`.

Establish `h1` using `hQr _ hβ`. Rewrite `h1` using `[Rat.smul_def, norm_mul]`. Establish `h2 : (1 : ℝ) ≤ ‖(((q : ℚ) ^ i : ℚ) : ℂ)‖`. Simplify using `only [Rat.cast_pow, Rat.cast_natCast, norm_pow, Complex.norm_natCast]`. Conclude with `one_le_pow₀ (by linarith)`.

Use polynomial arithmetic with `[norm_nonneg β]`. Rewrite using `[map_mul, Module.End.mul_apply, aeval_scale]`. Apply `hR2` to reduce the goal to its premises. Use `graded_aeval T Φ q hq0 hT h i 1 Q x hx` as an intermediate fact. Rewrite `this` using `[_root_.one_mul, one_smul]`.

Rewrite using `[← this]`. Conclude with `hQk _ (by rw [← hTT, hx])`. Take `⟨n, hn⟩` from `id hT`. Take `⟨R, hR1, hR2⟩` from `hR n`. Establish `hadj : ∀ x y, B (((q : ℚ) • Ψ) x) y = B x (Φ y)`.

Introduce `x y`. Establish `h1 : Φ (Ψ x) = x` using `by rw [← Module.End.mul_apply, hΨ]; rfl`. Use `hΦ (Ψ x) y` as an intermediate fact. Rewrite `this` using `[h1]`. Rewrite using `[this]`.

Simplify using `[Nat.cast_smul_eq_nsmul]`. Establish `hR3 : aeval Ψ (R.comp (C (q : ℚ) * X)) = 0`. Rewrite using `[aeval_scale]`. Use extensionality with `x`. Use `hB.1 _ fun y => ?_` and prove the remaining obligations.

Rewrite using `[aeval_adjoint B _ _ hadj, hR2 y (by simp [hn]), map_zero]`. Take `⟨R', hR'1, hR'2⟩` from `exists_rev Φ Ψ hΨ _ (fun β hβ => by`. Rewrite `hβ` using `[aeval_scale]`. Establish `h1` using `hR1 _ hβ`. Rewrite `h1` using `[Rat.smul_def, norm_mul]`.

Simplify using `only [Rat.cast_natCast, Complex.norm_natCast] at h1`. Use polynomial arithmetic with `[norm_nonneg β]) hR3`. Establish `key : ∀ (i : ℕ) (p : ℚ[X]), (∀ β : ℂ, aeval β p = 0 → ‖β‖ < (q : ℝ) ^ i) → ∀ x, (T ^ (i + 1)) x = 0 → aeval Φ p ((T ^ i) x) = 0 → (T ^ i) x = 0`. Introduce `i p hp x hx hpx`. Use `eq_zero_of_isCoprime Φ (a := p) (b := R'.comp (C ((q : ℚ) ^ i)⁻¹ * X)) ?_ hpx ?_` and prove the remaining obligations.

Rewrite using `[isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ]`. Introduce `β`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1` using `hp _ hc.1`.

Establish `h2` using `hc.2`. Rewrite `h2` using `[aeval_scale]`. Establish `h3` using `hR'1 _ h2`. Rewrite `h3` using `[Rat.smul_def, norm_mul]`. Simplify using `only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, norm_inv, norm_pow, Complex.norm_natCast] at h3`.

Establish `h4 : (0 : ℝ) < (q : ℝ) ^ i` using `by positivity`. Rewrite `h3` using `[inv_mul_eq_div, one_le_div h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[aeval_scale, graded_aeval T Φ q hq0 hT h i _ R' x hx, inv_mul_cancel₀ (pow_ne_zero i hqQ), one_smul, hR'2]`. Simplify using the standard rewrite rules.

Establish `h32 : ∀ x, (T ^ (2 + 1)) x = 0 → (T ^ 2) x = 0`. Introduce `x hx`. Use `key 2 Q (fun β hβ => ?_) x hx (hQk _ (by rw [← hTT, hx]))` and prove the remaining obligations. Establish `h1` using `hQr β hβ`. Establish `h2 : (q : ℝ) < (q : ℝ) ^ 2` using `by clear * - hqR`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `h1.trans_lt h2`. Establish `hTk` using `sq_eq_zero_of_cube T hT h32`. Use `finrank_le_of_injective T (aeval Φ P) W (fun x => hPW _ (hTk x)) fun x hx => ?_` and prove the remaining obligations. Use `key 1 P (by simpa only [pow_one] using hP) x (by rw [hTT, pow_one, hTk]) (by rw [pow_one, hx])` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem core [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V) (hB : B.Nondegenerate)
    (T Φ Ψ : Module.End 𝕜 V) (q : ℕ) (hq : 2 ≤ q) (hT : IsNilpotent T) (hΨ : Φ * Ψ = 1)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (h : Φ * (T + 1) = (T + 1) ^ q * Φ)
    (W : Submodule 𝕜 V) (P : ℚ[X]) (hP : ∀ β : ℂ, aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ x ∈ W, Φ x = (q : 𝕜) • x) (hPW : ∀ x, T x = 0 → aeval Φ P x ∈ W) :
    Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker T) + Module.finrank 𝕜 W := by
  have hq0 : q ≠ 0 := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  set Q : ℚ[X] := (X - C (q : ℚ)) * P with hQ
  have hQr : ∀ β : ℂ, aeval β Q = 0 → ‖β‖ ≤ q := by
    intro β hβ
    rw [hQ, map_mul, mul_eq_zero] at hβ
    rcases hβ with hβ | hβ
    · have : β = q := by simpa [sub_eq_zero] using hβ
      simp [this]
    · exact (hP β hβ).le
  have hQk : ∀ x, T x = 0 → aeval Φ Q x = 0 := by
    intro x hx
    have := hW _ (hPW x hx)
    rw [hQ, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, this,
      Algebra.algebraMap_eq_smul_one]
    simp [Nat.cast_smul_eq_nsmul]
  have hTT : ∀ (i : ℕ) x, (T ^ (i + 1)) x = T ((T ^ i) x) := by
    intro i x
    rw [pow_succ', Module.End.mul_apply]
  have hR : ∀ i : ℕ, ∃ R : ℚ[X], (∀ β : ℂ, aeval β R = 0 → ‖β‖ ≤ q) ∧
      ∀ x, (T ^ i) x = 0 → aeval Φ R x = 0 := by
    intro i
    induction i with
    | zero => exact ⟨1, by simp, fun x hx => by simpa using hx⟩
    | succ i ih =>
      obtain ⟨R, hR1, hR2⟩ := ih
      refine ⟨R * Q.comp (C ((q : ℚ) ^ i) * X), fun β hβ => ?_, fun x hx => ?_⟩
      · rw [map_mul, mul_eq_zero] at hβ
        rcases hβ with hβ | hβ
        · exact hR1 β hβ
        · rw [aeval_scale] at hβ
          have h1 := hQr _ hβ
          rw [Rat.smul_def, norm_mul] at h1
          have h2 : (1 : ℝ) ≤ ‖(((q : ℚ) ^ i : ℚ) : ℂ)‖ := by
            simp only [Rat.cast_pow, Rat.cast_natCast, norm_pow, Complex.norm_natCast]
            exact one_le_pow₀ (by linarith)
          nlinarith [norm_nonneg β]
      · rw [map_mul, Module.End.mul_apply, aeval_scale]
        apply hR2
        have := graded_aeval T Φ q hq0 hT h i 1 Q x hx
        rw [_root_.one_mul, one_smul] at this
        rw [← this]
        exact hQk _ (by rw [← hTT, hx])
  obtain ⟨n, hn⟩ := id hT
  obtain ⟨R, hR1, hR2⟩ := hR n
  have hadj : ∀ x y, B (((q : ℚ) • Ψ) x) y = B x (Φ y) := by
    intro x y
    have h1 : Φ (Ψ x) = x := by rw [← Module.End.mul_apply, hΨ]; rfl
    have := hΦ (Ψ x) y
    rw [h1] at this
    rw [this]
    simp [Nat.cast_smul_eq_nsmul]
  have hR3 : aeval Ψ (R.comp (C (q : ℚ) * X)) = 0 := by
    rw [aeval_scale]
    ext x
    refine hB.1 _ fun y => ?_
    rw [aeval_adjoint B _ _ hadj, hR2 y (by simp [hn]), map_zero]
  obtain ⟨R', hR'1, hR'2⟩ := exists_rev Φ Ψ hΨ _ (fun β hβ => by
    rw [aeval_scale] at hβ
    have h1 := hR1 _ hβ
    rw [Rat.smul_def, norm_mul] at h1
    simp only [Rat.cast_natCast, Complex.norm_natCast] at h1
    nlinarith [norm_nonneg β]) hR3
  have key : ∀ (i : ℕ) (p : ℚ[X]), (∀ β : ℂ, aeval β p = 0 → ‖β‖ < (q : ℝ) ^ i) →
      ∀ x, (T ^ (i + 1)) x = 0 → aeval Φ p ((T ^ i) x) = 0 → (T ^ i) x = 0 := by
    intro i p hp x hx hpx
    refine eq_zero_of_isCoprime Φ (a := p) (b := R'.comp (C ((q : ℚ) ^ i)⁻¹ * X)) ?_ hpx ?_
    · rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ]
      intro β
      by_contra hc
      push Not at hc
      have h1 := hp _ hc.1
      have h2 := hc.2
      rw [aeval_scale] at h2
      have h3 := hR'1 _ h2
      rw [Rat.smul_def, norm_mul] at h3
      simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, norm_inv, norm_pow,
        Complex.norm_natCast] at h3
      have h4 : (0 : ℝ) < (q : ℝ) ^ i := by positivity
      rw [inv_mul_eq_div, one_le_div h4] at h3
      linarith
    · rw [aeval_scale, graded_aeval T Φ q hq0 hT h i _ R' x hx,
        inv_mul_cancel₀ (pow_ne_zero i hqQ), one_smul, hR'2]
      simp
  have h32 : ∀ x, (T ^ (2 + 1)) x = 0 → (T ^ 2) x = 0 := by
    intro x hx
    refine key 2 Q (fun β hβ => ?_) x hx (hQk _ (by rw [← hTT, hx]))
    have h1 := hQr β hβ
    have h2 : (q : ℝ) < (q : ℝ) ^ 2 := by
      clear * - hqR
      nlinarith
    exact h1.trans_lt h2
  have hTk := sq_eq_zero_of_cube T hT h32
  refine finrank_le_of_injective T (aeval Φ P) W (fun x => hPW _ (hTk x)) fun x hx => ?_
  have := key 1 P (by simpa only [pow_one] using hP) x (by rw [hTT, pow_one, hTk])
    (by rw [pow_one, hx])
  rwa [pow_one] at this

end

/- English proof (translation)
Introduce `𝕜 V _ _ _ _ _ B hB _ S Φ q hq hS _ hΦ h W P hP hW hPW`. Use `letI : Module ℚ V := Module.compHom V (algebraMap ℚ 𝕜)`. Use `haveI : IsScalarTower ℚ 𝕜 V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `core B hB _ (Φ : V →ₗ[𝕜] V) (Φ.symm : V →ₗ[𝕜] V) q hq hS ?_ hΦ ?_ W (P.map (algebraMap ℤ ℚ)) ?_ hW ?_` and prove the remaining obligations. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[sub_add_cancel]`. Use `congrArg (fun e : V ≃ₗ[𝕜] V => (e : V →ₗ[𝕜] V)) h` as an intermediate fact. Establish `h2 : ∀ k : ℕ, ((S ^ k : V ≃ₗ[𝕜] V) : V →ₗ[𝕜] V) = (S : V →ₗ[𝕜] V) ^ k`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ k ih => rw [pow_succ, pow_succ, ← ih]`. Simplify using the standard rewrite rules.

Simplify `this` using `[h2]`. Introduce `β hβ`. Rewrite `hβ` using `[aeval_map_algebraMap]`. Conclude with `hP β hβ`. Introduce `x hx`.

Rewrite using `[aeval_map_algebraMap]`. Conclude with `hPW x (by simpa [sub_eq_zero] using hx)`.
-/
theorem finrank_le_of_weights : ∀ (𝕜 V : Type) [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V), B.Nondegenerate → (∀ x y, B y x = - B x y) → ∀ (S Φ : V ≃ₗ[𝕜] V) (q : ℕ), 2 ≤ q → IsNilpotent ((S : V →ₗ[𝕜] V) - 1) → (∀ x y, B (S x) (S y) = B x y) → (∀ x y, B (Φ x) (Φ y) = q * B x y) → Φ * S = S ^ q * Φ → ∀ (W : Submodule 𝕜 V) (P : Polynomial ℤ), (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ x ∈ W, Φ x = (q : 𝕜) • x) → (∀ x, S x = x → Polynomial.aeval (Φ : V →ₗ[𝕜] V) P x ∈ W) → Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker ((S : V →ₗ[𝕜] V) - 1)) + Module.finrank 𝕜 W := by
  intro 𝕜 V _ _ _ _ _ B hB _ S Φ q hq hS _ hΦ h W P hP hW hPW
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ 𝕜)
  haveI : IsScalarTower ℚ 𝕜 V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine core B hB _ (Φ : V →ₗ[𝕜] V) (Φ.symm : V →ₗ[𝕜] V) q hq hS ?_ hΦ ?_ W
    (P.map (algebraMap ℤ ℚ)) ?_ hW ?_
  · ext x
    simp
  · rw [sub_add_cancel]
    have := congrArg (fun e : V ≃ₗ[𝕜] V => (e : V →ₗ[𝕜] V)) h
    have h2 : ∀ k : ℕ, ((S ^ k : V ≃ₗ[𝕜] V) : V →ₗ[𝕜] V) = (S : V →ₗ[𝕜] V) ^ k := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ k ih => rw [pow_succ, pow_succ, ← ih]; simp
    simpa [h2] using this
  · intro β hβ
    rw [aeval_map_algebraMap] at hβ
    exact hP β hβ
  · intro x hx
    rw [aeval_map_algebraMap]
    exact hPW x (by simpa [sub_eq_zero] using hx)

end GlobalTheory.SS.LinCore
