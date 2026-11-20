import Mathlib
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

section Cong

variable {A : ValuationSubring Ω}

/- English proof (translation)
Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis.
-/
theorem cong_symm {x y : Ω} (h : A.valuation (x - y) < 1) : A.valuation (y - x) < 1 := by
  rwa [Valuation.map_sub_swap]

/- English proof (translation)
Establish `e : x - z = (x - y) + (y - z)` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ h h'`.
-/
theorem cong_trans {x y z : Ω} (h : A.valuation (x - y) < 1) (h' : A.valuation (y - z) < 1) :
    A.valuation (x - z) < 1 := by
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]; exact Valuation.map_add_lt _ h h'

/- English proof (translation)
Rewrite using `[map_pow]`. Conclude with `pow_le_one₀ zero_le hx`.
-/
theorem val_pow_le_one {x : Ω} (hx : A.valuation x ≤ 1) (n : ℕ) : A.valuation (x ^ n) ≤ 1 := by
  rw [map_pow]; exact pow_le_one₀ zero_le hx

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y)` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_pow_le_one hy n)) h`.
-/
theorem cong_pow {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (n : ℕ) : A.valuation (x ^ n - y ^ n) < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_pow_le_one hy n)) h

/- English proof (translation)
Rewrite `hx`, the goal using `[A.valuation_le_one_iff]`. Conclude with `(apply_mem_iff_of_mem_Dec hσ x).mpr hx`.
-/
theorem val_apply_le_one {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 := by
  rw [A.valuation_le_one_iff] at hx ⊢
  exact (apply_mem_iff_of_mem_Dec hσ x).mpr hx

/- English proof (translation)
Establish `hdeg : (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω).degree = m`. Rewrite using `[Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]`. Rewrite using `[Polynomial.degree_X_pow, ← Polynomial.C_1, Polynomial.degree_X_pow_add_C hn]`. Conclude with `hmn` after adjusting the coercions. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω) (by rw [hdeg]; exact_mod_cast (hn.trans hmn).ne')`.

Establish `hx' : x ^ m = x ^ n + 1`. Use `hx` as an intermediate fact. Simplify using `only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this`. Conclude with `sub_eq_zero.mp this`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Establish `h1 : 1 < A.valuation x` using `not_le.mp hc`. Establish `h2 : A.valuation (x ^ n + 1) < A.valuation x ^ m`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `pow_lt_pow_right₀ h1 hmn`. Rewrite using `[map_one]`. Conclude with `one_lt_pow₀ h1 (hn.trans hmn).ne'`. Rewrite `h2` using `[← hx', map_pow]`. Conclude with `lt_irrefl _ h2`.

Rewrite using `[hx', add_sub_cancel_left, map_one]`. Conclude with `lt_irrefl _`.
-/
theorem exists_not_cong_pow [IsAlgClosed Ω] {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    ∃ x : Ω, A.valuation x ≤ 1 ∧ ¬ A.valuation (x ^ m - x ^ n) < 1 := by
  have hdeg : (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω).degree = m := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rw [Polynomial.degree_X_pow, ← Polynomial.C_1, Polynomial.degree_X_pow_add_C hn]
    exact_mod_cast hmn
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω)
    (by rw [hdeg]; exact_mod_cast (hn.trans hmn).ne')
  have hx' : x ^ m = x ^ n + 1 := by
    have := hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  refine ⟨x, ?_, ?_⟩
  · by_contra hc
    have h1 : 1 < A.valuation x := not_le.mp hc
    have h2 : A.valuation (x ^ n + 1) < A.valuation x ^ m := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_pow]; exact pow_lt_pow_right₀ h1 hmn
      · rw [map_one]; exact one_lt_pow₀ h1 (hn.trans hmn).ne'
    rw [← hx', map_pow] at h2
    exact lt_irrefl _ h2
  · rw [hx', add_sub_cancel_left, map_one]; exact lt_irrefl _

end Cong

def ActsAs (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (a b : ℕ) : Prop :=
  σ ∈ Dec (F := E) A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((σ x) ^ (q ^ b) - x ^ (q ^ a)) < 1

section ActsAs

variable {A : ValuationSubring Ω} {q : ℕ}

/- English proof (translation)
Use `⟨(Dec (F := E) A).mul_mem hσ.1 hτ.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hy` using `val_apply_le_one hτ.1 hx`. Establish `h1` using `cong_pow (val_pow_le_one (val_apply_le_one hσ.1 hy) _) (val_pow_le_one hy _) (hσ.2 _ hy) (q ^ d)`. Establish `h2` using `cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (hτ.2 _ hx) (q ^ a)`. Rewrite `h1`, `h2` using `[← pow_mul, ← pow_mul, ← pow_add, ← pow_add]`.

Rewrite `h2` using `[add_comm d a, add_comm c a]`. Conclude with `cong_trans h1 h2`.
-/
theorem ActsAs.mul {σ τ : G E Ω} {a b c d : ℕ} (hσ : ActsAs A q σ a b) (hτ : ActsAs A q τ c d) :
    ActsAs A q (σ * τ) (a + c) (b + d) := by
  refine ⟨(Dec (F := E) A).mul_mem hσ.1 hτ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one hτ.1 hx
  have h1 := cong_pow (val_pow_le_one (val_apply_le_one hσ.1 hy) _) (val_pow_le_one hy _)
    (hσ.2 _ hy) (q ^ d)
  have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (hτ.2 _ hx) (q ^ a)
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at h1 h2
  rw [add_comm d a, add_comm c a] at h2
  exact cong_trans h1 h2

/- English proof (translation)
Use `⟨(Dec (F := E) A).inv_mem hσ.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hy` using `val_apply_le_one ((Dec (F := E) A).inv_mem hσ.1) hx`. Establish `h1` using `hσ.2 _ hy`. Rewrite `h1` using `[mul_inv_apply]`. Conclude with `cong_symm h1`.
-/
theorem ActsAs.inv {σ : G E Ω} {a b : ℕ} (hσ : ActsAs A q σ a b) : ActsAs A q σ⁻¹ b a := by
  refine ⟨(Dec (F := E) A).inv_mem hσ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one ((Dec (F := E) A).inv_mem hσ.1) hx
  have h1 := hσ.2 _ hy
  rw [mul_inv_apply] at h1
  exact cong_symm h1

/- English proof (translation)
Simplify using `only [ActsAs, pow_zero, pow_one]`. Conclude with `Iff.rfl`.
-/
theorem actsAs_zero_iff {σ : G E Ω} : ActsAs A q σ 0 0 ↔ σ ∈ Ine (F := E) A := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl

/- English proof (translation)
Simplify using `only [ActsAs, pow_zero, pow_one]`. Conclude with `Iff.rfl`.
-/
theorem actsAs_one_iff {σ : G E Ω} : ActsAs A q σ 1 0 ↔ IsFrob A q σ := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl

/- English proof (translation)
Establish `h1` using `h.inv.mul h'`. Rewrite `h1` using `[inv_mul_cancel]`. Establish `key : ∀ m n : ℕ, ActsAs A q (1 : G E Ω) m n → ¬ n < m`. Introduce `m n hmn hlt`. Take `⟨x, hx, hx'⟩` from `exists_not_cong_pow (A := A) (pow_pos (zero_lt_one.trans hq) n) (pow_lt_pow_right₀ hq hlt)`.

Conclude with `hx' (cong_symm (hmn.2 x hx))`. Establish `k1` using `key _ _ h1`. Establish `k2` using `key _ _ (by simpa using h1.inv)`. Use linear arithmetic over natural numbers and integers.
-/
theorem ActsAs.unique [IsAlgClosed Ω] (hq : 1 < q) {σ : G E Ω} {a b c d : ℕ}
    (h : ActsAs A q σ a b) (h' : ActsAs A q σ c d) : (a : ℤ) - b = (c : ℤ) - d := by
  have h1 := h.inv.mul h'
  rw [inv_mul_cancel] at h1
  have key : ∀ m n : ℕ, ActsAs A q (1 : G E Ω) m n → ¬ n < m := by
    intro m n hmn hlt
    obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (pow_pos (zero_lt_one.trans hq) n)
      (pow_lt_pow_right₀ hq hlt)
    exact hx' (cong_symm (hmn.2 x hx))
  have k1 := key _ _ h1
  have k2 := key _ _ (by simpa using h1.inv)
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact h`. Consider the case `succ n ih`. Use `ih ⟨h.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.2 x hx`.

Rewrite `h1` using `[← add_assoc, ← add_assoc, pow_succ, pow_succ, pow_mul, pow_mul]`. Establish `hu` using `val_pow_le_one (val_apply_le_one h.1 hx) (q ^ (b + n))`. Establish `hv` using `val_pow_le_one hx (q ^ (a + n))`. Rewrite using `[← valuation_apply_lt_one_iff hφ.1, map_sub]`. Conclude with `cong_trans (cong_trans (hφ.2 _ hu) h1) (cong_symm (hφ.2 _ hv))`.
-/
theorem ActsAs.cancel {φ : G E Ω} (hφ : IsFrob A q φ) {σ : G E Ω} {a b : ℕ} (n : ℕ)
    (h : ActsAs A q σ (a + n) (b + n)) : ActsAs A q σ a b := by
  induction n with
  | zero => exact h
  | succ n ih =>
    refine ih ⟨h.1, fun x hx => ?_⟩
    have h1 := h.2 x hx
    rw [← add_assoc, ← add_assoc, pow_succ, pow_succ, pow_mul, pow_mul] at h1
    have hu := val_pow_le_one (val_apply_le_one h.1 hx) (q ^ (b + n))
    have hv := val_pow_le_one hx (q ^ (a + n))
    rw [← valuation_apply_lt_one_iff hφ.1, map_sub]
    exact cong_trans (cong_trans (hφ.2 _ hu) h1) (cong_symm (hφ.2 _ hv))

end ActsAs

def weilSub (A : ValuationSubring Ω) (q : ℕ) : Subgroup (G E Ω) where
  carrier := {σ | ∃ a b, ActsAs A q σ a b}
  one_mem' := ⟨0, 0, actsAs_zero_iff.mpr (Ine (F := E) A).one_mem⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, h⟩ ⟨c, d, h'⟩
    exact ⟨_, _, h.mul h'⟩
  inv_mem' := by
    rintro σ ⟨a, b, h⟩
    exact ⟨_, _, h.inv⟩

/- English proof (translation)
Establish `: Nontrivial (𝓞 E ⧸ w.asIdeal)` using `Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top`. Establish `: Finite (𝓞 E ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Conclude with `Finite.one_lt_card`.
-/
theorem one_lt_normV (w : HeightOneSpectrum (𝓞 E)) : 1 < normV w := by
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  exact Finite.one_lt_card

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def Weil (_h : IsPlaceOver A w) : Subgroup (G E Ω) := weilSub A (normV w)

variable (h : IsPlaceOver A w)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Weil {σ : G E Ω} : σ ∈ Weil h ↔ ∃ a b, ActsAs A (normV w) σ a b := Iff.rfl

/- English proof (translation)
Introduce `_ ⟨_, _, hσ⟩` and use `hσ.1`.
-/
theorem Weil_le_Dec : Weil h ≤ Dec (F := E) A := fun _ ⟨_, _, hσ⟩ => hσ.1

/- English proof (translation)
Introduce `_ hσ` and use `⟨0, 0, actsAs_zero_iff.mpr hσ⟩`.
-/
theorem Ine_le_Weil : Ine (F := E) A ≤ Weil h := fun _ hσ => ⟨0, 0, actsAs_zero_iff.mpr hσ⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 0, actsAs_one_iff.mpr hσ⟩`.
-/
theorem mem_Weil_of_isFrob {σ : G E Ω} (hσ : IsFrob A (normV w) σ) : σ ∈ Weil h :=
  ⟨1, 0, actsAs_one_iff.mpr hσ⟩

def ineIncl : Ine (F := E) A →* Weil h := Subgroup.inclusion (Ine_le_Weil h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_ineIncl (σ : Ine (F := E) A) : (ineIncl h σ : G E Ω) = σ := rfl

variable {h}

def deg (σ : Weil h) : ℤ :=
  (σ.2.choose : ℤ) - (σ.2.choose_spec.choose : ℤ)

variable [IsAlgClosure E Ω]

/- English proof (translation)
The claim follows from `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E ActsAs.unique (one_lt_normV w) σ.2.choose_spec.choose_spec hσ`.
-/
theorem deg_eq {σ : Weil h} {a b : ℕ} (hσ : ActsAs A (normV w) (σ : G E Ω) a b) :
    deg σ = (a : ℤ) - b :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  ActsAs.unique (one_lt_normV w) σ.2.choose_spec.choose_spec hσ

/- English proof (translation)
Take `⟨a, b, hσ⟩` from `σ.2`. Take `⟨c, d, hτ⟩` from `τ.2`. Rewrite using `[deg_eq hσ, deg_eq hτ, deg_eq (σ := σ * τ) (hσ.mul hτ)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
@[simp] theorem deg_mul (σ τ : Weil h) : deg (σ * τ) = deg σ + deg τ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  obtain ⟨c, d, hτ⟩ := τ.2
  rw [deg_eq hσ, deg_eq hτ, deg_eq (σ := σ * τ) (hσ.mul hτ)]
  push_cast; ring

/- English proof (translation)
Use `deg_mul (1 : Weil h) 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
@[simp] theorem deg_one : deg (1 : Weil h) = 0 := by
  have := deg_mul (1 : Weil h) 1
  rw [mul_one] at this; omega

/- English proof (translation)
Use `deg_mul σ σ⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, deg_one]`. Use linear arithmetic over natural numbers and integers.
-/
@[simp] theorem deg_inv (σ : Weil h) : deg σ⁻¹ = -deg σ := by
  have := deg_mul σ σ⁻¹
  rw [mul_inv_cancel, deg_one] at this; omega

variable (h) in

def degHom : Weil h →* Multiplicative ℤ where
  toFun σ := Multiplicative.ofAdd (deg σ)
  map_one' := by simp
  map_mul' σ τ := by simp [ofAdd_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem degHom_apply (σ : Weil h) : degHom h σ = Multiplicative.ofAdd (deg σ) := rfl

/- English proof (translation)
Use `congrArg Multiplicative.toAdd (map_zpow (degHom h) σ n)` as an intermediate fact. Simplify using `using this`.
-/
@[simp] theorem deg_zpow (σ : Weil h) (n : ℤ) : deg (σ ^ n) = n * deg σ := by
  have := congrArg Multiplicative.toAdd (map_zpow (degHom h) σ n)
  simpa using this

/- English proof (translation)
Rewrite using `[← zpow_natCast, deg_zpow]`.
-/
@[simp] theorem deg_pow (σ : Weil h) (n : ℕ) : deg (σ ^ n) = n * deg σ := by
  rw [← zpow_natCast, deg_zpow]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_isFrob h`. Take `⟨c, d, hcd⟩` from `σ.2`. Rewrite `hσ` using `[deg_eq hcd]`. Establish `h1 : ActsAs A (normV w) (1 : G E Ω) b b` using `⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩`. Establish `h2` using `hcd.mul h1`.

Rewrite `h2` using `[mul_one, show c + b = a + d by omega, add_comm d b]`. Conclude with `ActsAs.cancel hφ d h2`.
-/
theorem actsAs_of_deg {σ : Weil h} {a b : ℕ} (hσ : deg σ = (a : ℤ) - b) :
    ActsAs A (normV w) (σ : G E Ω) a b := by
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  obtain ⟨c, d, hcd⟩ := σ.2
  rw [deg_eq hcd] at hσ
  have h1 : ActsAs A (normV w) (1 : G E Ω) b b := ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
  have h2 := hcd.mul h1
  rw [mul_one, show c + b = a + d by omega, add_comm d b] at h2
  exact ActsAs.cancel hφ d h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hσ => actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using hσ)), fun hσ => by simpa using deg_eq (actsAs_zero_iff.mpr hσ)⟩`.
-/
theorem deg_eq_zero_iff {σ : Weil h} : deg σ = 0 ↔ (σ : G E Ω) ∈ Ine (F := E) A :=
  ⟨fun hσ => actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_zero_iff.mpr hσ)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hσ => actsAs_one_iff.mp (actsAs_of_deg (a := 1) (b := 0) (by simpa using hσ)), fun hσ => by simpa using deg_eq (actsAs_one_iff.mpr hσ)⟩`.
-/
theorem deg_eq_one_iff {σ : Weil h} : deg σ = 1 ↔ IsFrob A (normV w) (σ : G E Ω) :=
  ⟨fun hσ => actsAs_one_iff.mp (actsAs_of_deg (a := 1) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_one_iff.mpr hσ)⟩

/- English proof (translation)
The claim follows from `deg_eq_zero_iff.mpr σ.2`.
-/
@[simp] theorem deg_ineIncl (σ : Ine (F := E) A) : deg (ineIncl h σ) = 0 :=
  deg_eq_zero_iff.mpr σ.2

variable (h) in

def frob : Weil h := ⟨(exists_isFrob h).choose, mem_Weil_of_isFrob h (exists_isFrob h).choose_spec⟩

/- English proof (translation)
The claim follows from `(exists_isFrob h).choose_spec`.
-/
theorem isFrob_frob : IsFrob A (normV w) (frob h : G E Ω) := (exists_isFrob h).choose_spec

/- English proof (translation)
The claim follows from `deg_eq_one_iff.mpr isFrob_frob`.
-/
@[simp] theorem deg_frob : deg (frob h) = 1 := deg_eq_one_iff.mpr isFrob_frob

/- English proof (translation)
Introduce `n` and use `⟨frob h ^ n, by simp⟩`.
-/
theorem deg_surjective : Function.Surjective (deg (h := h)) :=
  fun n => ⟨frob h ^ n, by simp⟩

/- English proof (translation)
Establish `h0 : deg ((φ ^ deg σ)⁻¹ * σ) = 0` using `by simp [hφ]`. Use `⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_mul_eq_iff_eq_mul]`. Both sides reduce to the same expression.
-/
theorem exists_eq_zpow_mul {φ : Weil h} (hφ : deg φ = 1) (σ : Weil h) :
    ∃ τ : Ine (F := E) A, σ = φ ^ deg σ * ineIncl h τ := by
  have h0 : deg ((φ ^ deg σ)⁻¹ * σ) = 0 := by simp [hφ]
  refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  rfl

variable (h) in

def unrChar (c : ℂˣ) : Weil h →* ℂˣ := (zpowersHom ℂˣ c).comp (degHom h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem unrChar_apply (c : ℂˣ) (σ : Weil h) : unrChar h c σ = c ^ deg σ := rfl

variable (w) in

def qPow (s : ℝ) : ℂˣ :=
  Units.mk0 (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_qPow (s : ℝ) : (qPow w s : ℂ) = ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := rfl

omit [IsAlgClosure E Ω] in

/- English proof (translation)
The claim follows from `Units.ext (by simp)`.
-/
@[simp] theorem qPow_zero : qPow w 0 = 1 := Units.ext (by simp)

omit [IsAlgClosure E Ω] in

/- English proof (translation)
The claim follows from `Units.ext (by simp only [coe_qPow, Units.val_mul, Complex.ofReal_add] exact Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))`.
-/
theorem qPow_add (s t : ℝ) : qPow w (s + t) = qPow w s * qPow w t := Units.ext (by
  simp only [coe_qPow, Units.val_mul, Complex.ofReal_add]
  exact Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coe_qPow_one : (qPow w 1 : ℂ) = ((normV w : ℕ) : ℂ) := by simp

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Rewrite using `[coe_qPow, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (one_lt_normV w))]`. Simplify using the standard rewrite rules.
-/
theorem norm_qPow (s : ℝ) : ‖(qPow w s : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ s := by
  rw [coe_qPow, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (one_lt_normV w))]
  simp

/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Conclude with `isCompact_iff_compactSpace.mp (isClosed_Ine A).isCompact`.
-/
theorem compactSpace_Ine (A : ValuationSubring Ω) : CompactSpace (Ine (F := E) A) := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  exact isCompact_iff_compactSpace.mp (isClosed_Ine A).isCompact

/- English proof (translation)
Rewrite using `[← deg_eq_zero_iff, deg_frob]`. Conclude with `one_ne_zero`.
-/
example : (frob h : G E Ω) ∉ Ine (F := E) A := by
  rw [← deg_eq_zero_iff, deg_frob]; exact one_ne_zero

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example : deg (frob h)⁻¹ = -1 := by simp

end GlobalTheory.WeilDeligne
