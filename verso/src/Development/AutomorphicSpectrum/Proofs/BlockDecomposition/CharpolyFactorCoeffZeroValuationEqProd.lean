import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open scoped NumberTheorySymbols

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfInt

variable {M : ℕ}

def tw (c : DirichletCharacter ℂ M) (n : ℤ) (d : ℕ) : ℂ := c (d : ZMod M) * ((J(n | d) : ℤ) : ℂ)

/- English proof (translation)
The claim follows from `c.map_nonunit fun hu => h ((ZMod.isUnit_iff_coprime d M).1 hu)`.
-/
theorem c_eq_zero (c : DirichletCharacter ℂ M) {d : ℕ} (h : ¬ d.Coprime M) : c (d : ZMod M) = 0 :=
  c.map_nonunit fun hu => h ((ZMod.isUnit_iff_coprime d M).1 hu)

/- English proof (translation)
Apply `c_eq_zero` to reduce the goal to its premises. Introduce `h`. Establish `: M = 1` using `by simpa using h`. Substitute `this` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem c_zero (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) : c ((0 : ℕ) : ZMod M) = 0 := by
  apply c_eq_zero
  intro h
  have : M = 1 := by simpa using h
  subst this
  omega

/- English proof (translation)
Simplify using `only [tw]`. Rewrite using `[c_zero h2 c, zero_mul]`.
-/
theorem tw_zero (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (n : ℤ) : tw c n 0 = 0 := by
  simp only [tw]
  rw [c_zero h2 c, zero_mul]

/- English proof (translation)
Simplify using `[tw]`.
-/
theorem tw_one (c : DirichletCharacter ℂ M) (n : ℤ) : tw c n 1 = 1 := by
  simp [tw]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Simplify using `[tw_zero h2]`. Break down `Nat.eq_zero_or_pos b with rfl | hb` into its components or cases. Simplify using `[tw_zero h2]`. Use `haveI : NeZero a := ⟨ha.ne'⟩`.

Use `haveI : NeZero b := ⟨hb.ne'⟩`. Simplify using `only [tw, Nat.cast_mul, map_mul, jacobiSym.mul_right, Int.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tw_mul (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (n : ℤ) (a b : ℕ) :
    tw c n (a * b) = tw c n a * tw c n b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [tw_zero h2]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [tw_zero h2]
  haveI : NeZero a := ⟨ha.ne'⟩
  haveI : NeZero b := ⟨hb.ne'⟩
  simp only [tw, Nat.cast_mul, map_mul, jacobiSym.mul_right, Int.cast_mul]
  ring

/- English proof (translation)
Simplify using `only [tw, norm_mul]`. Establish `h1 : ‖c (d : ZMod M)‖ ≤ 1` using `c.norm_le_one _`. Establish `h2 : ‖((J(n | d) : ℤ) : ℂ)‖ ≤ 1`. Apply the tactic sequence `rcases jacobiSym.trichotomy n d with h | h | h <;> simp [h]`. Conclude with `mul_le_one₀ h1 (norm_nonneg _) h2`.
-/
theorem tw_norm (c : DirichletCharacter ℂ M) (n : ℤ) (d : ℕ) : ‖tw c n d‖ ≤ 1 := by
  simp only [tw, norm_mul]
  have h1 : ‖c (d : ZMod M)‖ ≤ 1 := c.norm_le_one _
  have h2 : ‖((J(n | d) : ℤ) : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy n d with h | h | h <;> simp [h]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

/- English proof (translation)
Establish `hc : ((d + 4 * M * n.natAbs : ℕ) : ZMod M) = (d : ZMod M)`. Simplify using the standard rewrite rules. Break down `Nat.even_or_odd d with he | ho` into its components or cases. Establish `hne : ∀ e : ℕ, Even e → c (e : ZMod M) = 0`. Introduce `e he`.

Apply `c_eq_zero` to reduce the goal to its premises. Introduce `h`. Establish `h2e : 2 ∣ e` using `he.two_dvd`. Use `Nat.dvd_gcd h2e h2` as an intermediate fact. Rewrite `this` using `[h]`.

Use linear arithmetic over natural numbers and integers. Establish `he' : Even (d + 4 * M * n.natAbs)`. Apply `he.add` to reduce the goal to its premises. Conclude with `⟨2 * M * n.natAbs, by ring⟩`. Simplify using `only [tw]`.

Rewrite using `[hne _ he, hne _ he', zero_mul, zero_mul]`. Establish `ho' : Odd (d + 4 * M * n.natAbs)`. Apply `ho.add_even` to reduce the goal to its premises. Conclude with `⟨2 * M * n.natAbs, by ring⟩`. Simplify using `only [tw]`.

Rewrite using `[hc, jacobiSym.mod_right n ho', jacobiSym.mod_right n ho]`. Establish `: (d + 4 * M * n.natAbs) % (4 * n.natAbs) = d % (4 * n.natAbs)`. Establish `: 4 * M * n.natAbs = (4 * n.natAbs) * M` using `by ring`. Rewrite using `[this, Nat.add_mul_mod_self_left]`. Rewrite using `[this]`.
-/
theorem tw_periodic (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} (d : ℕ) :
    tw c n (d + 4 * M * n.natAbs) = tw c n d := by
  have hc : ((d + 4 * M * n.natAbs : ℕ) : ZMod M) = (d : ZMod M) := by
    simp
  rcases Nat.even_or_odd d with he | ho
  · have hne : ∀ e : ℕ, Even e → c (e : ZMod M) = 0 := by
      intro e he
      apply c_eq_zero
      intro h
      have h2e : 2 ∣ e := he.two_dvd
      have := Nat.dvd_gcd h2e h2
      rw [h] at this
      omega
    have he' : Even (d + 4 * M * n.natAbs) := by
      apply he.add
      exact ⟨2 * M * n.natAbs, by ring⟩
    simp only [tw]
    rw [hne _ he, hne _ he', zero_mul, zero_mul]
  · have ho' : Odd (d + 4 * M * n.natAbs) := by
      apply ho.add_even
      exact ⟨2 * M * n.natAbs, by ring⟩
    simp only [tw]
    rw [hc, jacobiSym.mod_right n ho', jacobiSym.mod_right n ho]
    have : (d + 4 * M * n.natAbs) % (4 * n.natAbs) = d % (4 * n.natAbs) := by
      have : 4 * M * n.natAbs = (4 * n.natAbs) * M := by ring
      rw [this, Nat.add_mul_mod_self_left]
    rw [this]

def twHom (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (n : ℤ) {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun d := tw c n d * (d : ℂ) ^ (-s)
  map_zero' := by simp [tw_zero h2]
  map_one' := by simp [tw_one]
  map_mul' a b := by
    have := riemannZetaSummandHom hs |>.map_mul a b
    simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at this
    rw [tw_mul h2, this]
    ring

/- English proof (translation)
Establish `hs0` using `Complex.ne_zero_of_one_lt_re hs`. Establish `hsum : Summable (fun d => ‖twHom h2 c n hs0 d‖)`. Use `(summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun d => ?_` and prove the remaining obligations. Simplify using `only [twHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (tw_norm c n d)`.

Establish `ht : ∑' d : ℕ, twHom h2 c n hs0 d = LSeries (tw c n) s`. Simplify using `only [twHom, Complex.cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries, LSeries.term_of_ne_zero' hs0, div_eq_mul_inv]`. Establish `h` using `EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum`. Rewrite `h` using `[ht]`. Conclude with `h`.
-/
theorem tw_euler (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) (n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - tw c n p * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (LSeries (tw c n) s) := by
  have hs0 := Complex.ne_zero_of_one_lt_re hs
  have hsum : Summable (fun d => ‖twHom h2 c n hs0 d‖) := by
    refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun d => ?_
    simp only [twHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (tw_norm c n d)
  have ht : ∑' d : ℕ, twHom h2 c n hs0 d = LSeries (tw c n) s := by
    simp only [twHom, Complex.cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
      LSeries.term_of_ne_zero' hs0, div_eq_mul_inv]
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
  rw [ht] at h
  exact h

/- English proof (translation)
Establish `hg` using `(hasSum_geometric_of_norm_lt_one hX).mul_left ((1 + Jp) * X)`. Establish `hs : HasSum (fun j : ℕ => a j * X ^ j) ((1 + Jp) * X * (1 - X)⁻¹ + 1)`. Establish `h' : HasSum (fun j : ℕ => (fun j : ℕ => a j * X ^ j) (j + 1)) ((1 + Jp) * X * (1 - X)⁻¹)`. Establish `e : (fun j : ℕ => (fun j : ℕ => a j * X ^ j) (j + 1)) = fun i : ℕ => (1 + Jp) * X * X ^ i`. Use function extensionality and compare the values at `j`.

Simplify using `only [h1, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hg`. Use `(hasSum_nat_add_iff (f := fun j : ℕ => a j * X ^ j) 1).1 h'` as an intermediate fact.

Simplify `this` using `[h0]`. Establish `hXn : ∀ u : ℂ, ‖u‖ = 1 → 1 + u * X ≠ 0`. Introduce `u hu h`. Establish `: u * X = -1` using `by linear_combination h`. Establish `h3 : ‖u * X‖ = 1` using `by rw [this]; simp`.

Rewrite `h3` using `[norm_mul, hu, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJn : ‖Jp‖ = 1`. Establish `: ‖Jp‖ ^ 2 = 1` using `by rw [← norm_pow, hJ]; simp`. Use polynomial arithmetic with `[norm_nonneg Jp]`.

Establish `e1 : 1 - X ≠ 0`. Use `hXn (-1) (by simp)` as an intermediate fact. Introduce `h`. Apply `this` to reduce the goal to its premises. Take the linear combination `h`.

Establish `e2 : 1 + X ≠ 0`. Use `hXn 1 (by simp)` as an intermediate fact. Introduce `h`. Apply `this` to reduce the goal to its premises. Take the linear combination `h`.

Establish `e3 : 1 - Jp * X ≠ 0`. Use `hXn (-Jp) (by simpa using hJn)` as an intermediate fact. Introduce `h`. Apply `this` to reduce the goal to its premises. Take the linear combination `h`.

Rewrite using `[hs.tsum_eq]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-X ^ 2) * hJ`.
-/
theorem local_id {a : ℕ → ℂ} {X Jp : ℂ} (hJ : Jp ^ 2 = 1) (hX : ‖X‖ < 1) (h0 : a 0 = 1)
    (h1 : ∀ j, a (j + 1) = 1 + Jp) : (∑' j : ℕ, a j * X ^ j) / (1 + X) = (1 - Jp * X)⁻¹ := by
  have hg := (hasSum_geometric_of_norm_lt_one hX).mul_left ((1 + Jp) * X)
  have hs : HasSum (fun j : ℕ => a j * X ^ j) ((1 + Jp) * X * (1 - X)⁻¹ + 1) := by
    have h' : HasSum (fun j : ℕ => (fun j : ℕ => a j * X ^ j) (j + 1)) ((1 + Jp) * X * (1 - X)⁻¹) := by
      have e : (fun j : ℕ => (fun j : ℕ => a j * X ^ j) (j + 1)) = fun i : ℕ => (1 + Jp) * X * X ^ i := by
        funext j
        simp only [h1, pow_succ]
        ring
      rw [e]
      exact hg
    have := (hasSum_nat_add_iff (f := fun j : ℕ => a j * X ^ j) 1).1 h'
    simpa [h0] using this
  have hXn : ∀ u : ℂ, ‖u‖ = 1 → 1 + u * X ≠ 0 := by
    intro u hu h
    have : u * X = -1 := by linear_combination h
    have h3 : ‖u * X‖ = 1 := by rw [this]; simp
    rw [norm_mul, hu, one_mul] at h3
    linarith
  have hJn : ‖Jp‖ = 1 := by
    have : ‖Jp‖ ^ 2 = 1 := by rw [← norm_pow, hJ]; simp
    nlinarith [norm_nonneg Jp]
  have e1 : 1 - X ≠ 0 := by
    have := hXn (-1) (by simp)
    intro h; apply this; linear_combination h
  have e2 : 1 + X ≠ 0 := by
    have := hXn 1 (by simp)
    intro h; apply this; linear_combination h
  have e3 : 1 - Jp * X ≠ 0 := by
    have := hXn (-Jp) (by simpa using hJn)
    intro h; apply this; linear_combination h
  rw [hs.tsum_eq]
  field_simp
  linear_combination (-X ^ 2) * hJ

def Fp (c : DirichletCharacter ℂ M) (n : ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  ∑' j : ℕ, (NN n (p ^ j) : ℂ) * (c (p : ZMod M) * (p : ℂ) ^ (-s)) ^ j

def Qp (c : DirichletCharacter ℂ M) (n : ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  Fp c n p s / (1 + c (p : ZMod M) * (p : ℂ) ^ (-s))

/- English proof (translation)
Establish `hc : c (p : ZMod M) = 0`. Apply `c_eq_zero` to reduce the goal to its premises. Introduce `h`. Conclude with `hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hpM)`. Establish `h1` using `(hN n).1`.

Simplify using `only [Qp, Fp, hc, zero_mul, add_zero, div_one]`. Rewrite using `[tsum_eq_single 0]`. Simplify using `[h1]`. Introduce `j hj`. Simplify using `[hj]`.
-/
theorem Qp_of_dvd (hN : N2) (c : DirichletCharacter ℂ M) (n : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M)
    (s : ℂ) : Qp c n p s = 1 := by
  have hc : c (p : ZMod M) = 0 := by
    apply c_eq_zero
    intro h
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hpM)
  have h1 := (hN n).1
  simp only [Qp, Fp, hc, zero_mul, add_zero, div_one]
  rw [tsum_eq_single 0]
  · simp [h1]
  · intro j hj
    simp [hj]

/- English proof (translation)
Rewrite using `[norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]`. Conclude with `mul_le_of_le_one_left (by positivity) (c.norm_le_one _)`.
-/
theorem norm_X_le (c : DirichletCharacter ℂ M) {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖c (p : ZMod M) * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  exact mul_le_of_le_one_left (by positivity) (c.norm_le_one _)

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Establish `: J(n | p) = 0`. Rewrite using `[jacobiSym.eq_zero_iff_not_coprime]`. Introduce `h`. Establish `h3 : (p : ℤ) ∣ (Int.gcd n p : ℤ)` using `Int.dvd_coe_gcd hn dvd_rfl`.

Rewrite `h3` using `[h]`. Use `Int.natCast_dvd_natCast.1 (by simpa using h3 : (p : ℤ) ∣ ((1 : ℕ) : ℤ))` as an intermediate fact. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 this)`. Simplify using `[tw, this]`.
-/
theorem tw_prime_dvd (c : DirichletCharacter ℂ M) {n : ℤ} {p : ℕ} (hp : p.Prime) (hn : (p : ℤ) ∣ n) :
    tw c n p = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have : J(n | p) = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    intro h
    have h3 : (p : ℤ) ∣ (Int.gcd n p : ℤ) := Int.dvd_coe_gcd hn dvd_rfl
    rw [h] at h3
    have := Int.natCast_dvd_natCast.1 (by simpa using h3 : (p : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  simp [tw, this]

/- English proof (translation)
Distinguish the cases in `hpM : p ∣ M`. Rewrite using `[Qp_of_dvd hN c n hp hpM]`. Establish `hc : c (p : ZMod M) = 0`. Apply `c_eq_zero` to reduce the goal to its premises. Introduce `h`.

Conclude with `hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hpM)`. Simplify using `[tw, hc]`. Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `hpM h2`.

Establish `hJ : ((J(n | p) : ℤ) : ℂ) ^ 2 = 1`. Establish `: Int.gcd n p = 1`. Establish `: Nat.Coprime n.natAbs p`. Apply `Nat.Coprime.symm` to reduce the goal to its premises. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hp]`.

Introduce `h`. Conclude with `hpn (Int.natCast_dvd.2 h)`. Simplify `this` using `[Int.gcd]`. Establish `h3` using `jacobiSym.sq_one this`. Conclude with `h3` after adjusting the coercions.

Establish `hX : ‖c (p : ZMod M) * (p : ℂ) ^ (-s)‖ < 1`. Use `(norm_X_le c hp.pos s).trans_lt ?_` and prove the remaining obligations. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa using hs)`. Establish `h1` using `(hN n).1`. Establish `hl` using `local_id (a := fun j => (NN n (p ^ j) : ℂ)) hJ hX (by simp [h1]) (fun j => by`.

Use `((hN n).2.2.2 p j hp hp2).1 hpn` as an intermediate fact. Conclude with `this)` after adjusting the coercions. Simplify using `only [Qp, Fp]`. Rewrite using `[hl]`. Simplify using `only [tw]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Qp_off (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} {p : ℕ} (hp : p.Prime)
    (hpn : ¬ (p : ℤ) ∣ n) {s : ℂ} (hs : 0 < s.re) :
    Qp c n p s = (1 - tw c n p * (p : ℂ) ^ (-s))⁻¹ := by
  by_cases hpM : p ∣ M
  · rw [Qp_of_dvd hN c n hp hpM]
    have hc : c (p : ZMod M) = 0 := by
      apply c_eq_zero
      intro h
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hpM)
    simp [tw, hc]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM h2
  have hJ : ((J(n | p) : ℤ) : ℂ) ^ 2 = 1 := by
    have : Int.gcd n p = 1 := by
      have : Nat.Coprime n.natAbs p := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro h
        exact hpn (Int.natCast_dvd.2 h)
      simpa [Int.gcd] using this
    have h3 := jacobiSym.sq_one this
    exact_mod_cast h3
  have hX : ‖c (p : ZMod M) * (p : ℂ) ^ (-s)‖ < 1 := by
    refine (norm_X_le c hp.pos s).trans_lt ?_
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa using hs)
  have h1 := (hN n).1
  have hl := local_id (a := fun j => (NN n (p ^ j) : ℂ)) hJ hX (by simp [h1]) (fun j => by
    have := ((hN n).2.2.2 p j hp hp2).1 hpn
    exact_mod_cast this)
  simp only [Qp, Fp]
  rw [hl]
  simp only [tw]
  congr 1
  ring

def r0 : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))

/- English proof (translation)
Unfold `r0`. Check the signs of the components of the expression.
-/
theorem r0_pos : 0 < r0 := by unfold r0; positivity

/- English proof (translation)
The claim follows from `Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)`.
-/
theorem euler_radius_lt_one : r0 < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

def K0 : ℝ := 2 / (1 - r0) ^ 2

/- English proof (translation)
Establish `h1` using `r0_pos`. Establish `h2` using `euler_radius_lt_one`. Unfold `K0`. Rewrite using `[le_div_iff₀ (by nlinarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem euler_constant_ge_one : 1 ≤ K0 := by
  have h1 := r0_pos
  have h2 := euler_radius_lt_one
  unfold K0
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/- English proof (translation)
Use `(norm_X_le c (by omega) s).trans ?_` and prove the remaining obligations. Establish `hs' : (1 / 4 : ℝ) < s.re` using `hs`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (by omega : 1 ≤ p)`. Establish `hp3 : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_euler_factor_le_radius (c : DirichletCharacter ℂ M) {p : ℕ} (hp : 3 ≤ p) {s : ℂ} (hs : s ∈ HP (1 / 4)) :
    ‖c (p : ZMod M) * (p : ℂ) ^ (-s)‖ ≤ r0 := by
  refine (norm_X_le c (by omega) s).trans ?_
  have hs' : (1 / 4 : ℝ) < s.re := hs
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ ≤ r0 := Real.rpow_le_rpow_of_nonpos (by norm_num) hp3 (by norm_num)

/- English proof (translation)
Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `hpM h2`. Establish `hp3 : 3 ≤ p`. Use `hp.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1 : (NN n (p ^ j) : ℝ) ≤ 2 * (p : ℝ) ^ n.natAbs.factorization p`. Use `((hN n).2.2.2 p j hp hp2).2.1 hn` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast]`.

Conclude with `mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (norm_euler_factor_le_radius c hp3 hs) j) (by positivity) (by positivity)`.
-/
theorem term_le (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} (hn : n ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) {s : ℂ} (hs : s ∈ HP (1 / 4)) (j : ℕ) :
    ‖(NN n (p ^ j) : ℂ) * (c (p : ZMod M) * (p : ℂ) ^ (-s)) ^ j‖ ≤
      2 * (p : ℝ) ^ n.natAbs.factorization p * r0 ^ j := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM h2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : (NN n (p ^ j) : ℝ) ≤ 2 * (p : ℝ) ^ n.natAbs.factorization p := by
    have := ((hN n).2.2.2 p j hp hp2).2.1 hn
    exact_mod_cast this
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (norm_euler_factor_le_radius c hp3 hs) j)
    (by positivity) (by positivity)

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_re`.
-/
theorem isOpen_HP (a : ℝ) : IsOpen (HP a) :=
  isOpen_lt continuous_const Complex.continuous_re

/- English proof (translation)
Distinguish the cases in `hpM : p ∣ M`. Establish `: Qp c n p = fun _ => 1` using `funext fun s => Qp_of_dvd hN c n hp hpM s`. Rewrite using `[this]`. Conclude with `differentiableOn_const _`. Establish `hp2 : p ≠ 2`.

Introduce and unpack `rfl`. Conclude with `hpM h2`. Establish `hp3 : 3 ≤ p`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hXd : Differentiable ℂ (fun s : ℂ => c (p : ZMod M) * (p : ℂ) ^ (-s))` using `fun s => (differentiableAt_id.neg.const_cpow (Or.inl hp0)).const_mul _`. Establish `hF : DifferentiableOn ℂ (Fp c n p) (HP (1 / 4))`. Use `Complex.differentiableOn_tsum_of_summable_norm (u := fun j => 2 * (p : ℝ) ^ n.natAbs.factorization p * r0 ^ j) ((summable_geometric_of_lt_one r0_pos.le euler_radius_lt_one).mul_left _) (fun j => ?_) (isOpen_HP _) (fun j s hs => term_le hN h2 c hn hp hpM hs j)` and prove the remaining obligations. Conclude with `((hXd.pow j).const_mul _).differentiableOn`.

Use `hF.div ((differentiable_const _).add hXd).differentiableOn fun s hs h => ?_` and prove the remaining obligations. Establish `h1` using `norm_euler_factor_le_radius c hp3 hs`. Establish `h3 : c (p : ZMod M) * (p : ℂ) ^ (-s) = -1` using `by linear_combination h`. Rewrite `h1` using `[h3]`. Use `euler_radius_lt_one` as an intermediate fact.

Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Qp_diff (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} (hn : n ≠ 0) {p : ℕ}
    (hp : p.Prime) : DifferentiableOn ℂ (Qp c n p) (HP (1 / 4)) := by
  by_cases hpM : p ∣ M
  · have : Qp c n p = fun _ => 1 := funext fun s => Qp_of_dvd hN c n hp hpM s
    rw [this]
    exact differentiableOn_const _
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM h2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hXd : Differentiable ℂ (fun s : ℂ => c (p : ZMod M) * (p : ℂ) ^ (-s)) := fun s =>
    (differentiableAt_id.neg.const_cpow (Or.inl hp0)).const_mul _
  have hF : DifferentiableOn ℂ (Fp c n p) (HP (1 / 4)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun j => 2 * (p : ℝ) ^ n.natAbs.factorization p * r0 ^ j)
      ((summable_geometric_of_lt_one r0_pos.le euler_radius_lt_one).mul_left _) (fun j => ?_) (isOpen_HP _)
      (fun j s hs => term_le hN h2 c hn hp hpM hs j)
    exact ((hXd.pow j).const_mul _).differentiableOn
  refine hF.div ((differentiable_const _).add hXd).differentiableOn fun s hs h => ?_
  have h1 := norm_euler_factor_le_radius c hp3 hs
  have h3 : c (p : ZMod M) * (p : ℂ) ^ (-s) = -1 := by linear_combination h
  rw [h3] at h1
  have := euler_radius_lt_one
  simp at h1
  linarith

/- English proof (translation)
Establish `hK` using `euler_constant_ge_one`. Establish `hpow : (1 : ℝ) ≤ (p : ℝ) ^ n.natAbs.factorization p` using `one_le_pow₀ (by exact_mod_cast hp.one_lt.le)`. Distinguish the cases in `hpM : p ∣ M`. Rewrite using `[Qp_of_dvd hN c n hp hpM]`. Simplify using `only [norm_one]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `hpM h2`. Establish `hp3 : 3 ≤ p`.

Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hr` using `euler_radius_lt_one`. Establish `hr0` using `r0_pos`. Establish `hpos : 0 < 1 - r0` using `by linarith`.

Establish `hF : ‖Fp c n p s‖ ≤ 2 * (p : ℝ) ^ n.natAbs.factorization p * (1 - r0)⁻¹` using `tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hr0.le hr).mul_left _) (fun j => term_le hN h2 c hn hp hpM hs j)`. Establish `hd : 1 - r0 ≤ ‖1 + c (p : ZMod M) * (p : ℂ) ^ (-s)‖`. Establish `h1` using `norm_euler_factor_le_radius c hp3 hs`. Establish `h3` using `norm_sub_norm_le (1 : ℂ) (-(c (p : ZMod M) * (p : ℂ) ^ (-s)))`. Simplify using `only [norm_one, norm_neg, sub_neg_eq_add] at h3`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Qp, norm_div]`. Combine the equalities or inequalities in the displayed calculation. Unfold `K0`. Clear the denominators using the available nonvanishing facts.
-/
theorem Qp_bound (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} (hn : n ≠ 0) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : s ∈ HP (1 / 4)) :
    ‖Qp c n p s‖ ≤ K0 * (p : ℝ) ^ n.natAbs.factorization p := by
  have hK := euler_constant_ge_one
  have hpow : (1 : ℝ) ≤ (p : ℝ) ^ n.natAbs.factorization p :=
    one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  by_cases hpM : p ∣ M
  · rw [Qp_of_dvd hN c n hp hpM]
    simp only [norm_one]
    nlinarith
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM h2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hr := euler_radius_lt_one
  have hr0 := r0_pos
  have hpos : 0 < 1 - r0 := by linarith
  have hF : ‖Fp c n p s‖ ≤ 2 * (p : ℝ) ^ n.natAbs.factorization p * (1 - r0)⁻¹ :=
    tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hr0.le hr).mul_left _)
      (fun j => term_le hN h2 c hn hp hpM hs j)
  have hd : 1 - r0 ≤ ‖1 + c (p : ZMod M) * (p : ℂ) ^ (-s)‖ := by
    have h1 := norm_euler_factor_le_radius c hp3 hs
    have h3 := norm_sub_norm_le (1 : ℂ) (-(c (p : ZMod M) * (p : ℂ) ^ (-s)))
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h3
    linarith
  rw [Qp, norm_div]
  calc ‖Fp c n p s‖ / ‖1 + c (p : ZMod M) * (p : ℂ) ^ (-s)‖
      ≤ (2 * (p : ℝ) ^ n.natAbs.factorization p * (1 - r0)⁻¹) / (1 - r0) :=
        div_le_div₀ (by positivity) hF hpos hd
    _ = K0 * (p : ℝ) ^ n.natAbs.factorization p := by
        unfold K0
        field_simp

/- English proof (translation)
Establish `hn0 : n.natAbs ≠ 0` using `Int.natAbs_ne_zero.2 hn`. Establish `hprod : ∏ p ∈ n.natAbs.primeFactors, (p : ℝ) ^ n.natAbs.factorization p = |(n : ℝ)|`. Establish `h` using `Nat.factorization_prod_pow_eq_self hn0`. Rewrite `h` using `[Finsupp.prod, Nat.support_factorization]`. Establish `h'` using `congrArg (Nat.cast : ℕ → ℝ) h`.

Rewrite `h'` using `[Nat.cast_prod]`. Simplify using `only [Nat.cast_pow] at h'`. Rewrite using `[h', Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[norm_prod, ← hprod, ← Finset.prod_pow]`. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hpS => ?_` and prove the remaining obligations.

Establish `hp` using `Nat.prime_of_mem_primeFactors hpS`. Establish `hv : 1 ≤ n.natAbs.factorization p` using `(hp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hpS)`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.one_lt.le`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Use `(Qp_bound hN h2 c hn hp hs).trans ?_` and prove the remaining obligations.

Establish `hle : (p : ℝ) ≤ (p : ℝ) ^ n.natAbs.factorization p`. Combine the equalities or inequalities in the displayed calculation. Establish `h2B : K0 ≤ ((p : ℝ) ^ n.natAbs.factorization p) ^ B` using `hB.le.trans ((pow_le_pow_left₀ (by norm_num) (hp2.trans hle) B))`. Rewrite using `[pow_succ]`. Conclude with `mul_le_mul_of_nonneg_right h2B (by positivity)`.
-/
theorem prod_bound (hN : N2) (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ} (hn : n ≠ 0) {B : ℕ}
    (hB : K0 < 2 ^ B) {s : ℂ} (hs : s ∈ HP (1 / 4)) :
    ‖∏ p ∈ n.natAbs.primeFactors, Qp c n p s‖ ≤ |(n : ℝ)| ^ (B + 1) := by
  have hn0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  have hprod : ∏ p ∈ n.natAbs.primeFactors, (p : ℝ) ^ n.natAbs.factorization p = |(n : ℝ)| := by
    have h := Nat.factorization_prod_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at h
    have h' := congrArg (Nat.cast : ℕ → ℝ) h
    rw [Nat.cast_prod] at h'
    simp only [Nat.cast_pow] at h'
    rw [h', Nat.cast_natAbs, Int.cast_abs]
  rw [norm_prod, ← hprod, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hpS => ?_
  have hp := Nat.prime_of_mem_primeFactors hpS
  have hv : 1 ≤ n.natAbs.factorization p :=
    (hp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hpS)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine (Qp_bound hN h2 c hn hp hs).trans ?_
  have hle : (p : ℝ) ≤ (p : ℝ) ^ n.natAbs.factorization p := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hp1 hv
  have h2B : K0 ≤ ((p : ℝ) ^ n.natAbs.factorization p) ^ B :=
    hB.le.trans ((pow_le_pow_left₀ (by norm_num) (hp2.trans hle) B))
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right h2B (by positivity)

/- English proof (translation)
Establish `hn0 : n.natAbs ≠ 0` using `Int.natAbs_ne_zero.2 hn`. Establish `hs0 : 0 < s.re` using `by linarith`. Establish `h1 : HasProd (fun p : Nat.Primes => Qp c n p s) (DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c n s)` using `(hA M c n s hs).2`. Establish `h3` using `tw_euler h2 c n (s := s) (by linarith)`. Set `S : Finset Nat.Primes` to `n.natAbs.primeFactors.subtype Nat.Prime`.

Establish `hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℤ) ∣ n`. Introduce `p`. Establish `hm : p ∈ S ↔ (p : ℕ) ∈ n.natAbs.primeFactors` using `Finset.mem_subtype`. Rewrite using `[hm, Nat.mem_primeFactors]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, h, _⟩`. Conclude with `Int.natCast_dvd.2 h`. Introduce `h`. Conclude with `⟨p.2, Int.natCast_dvd.1 h, hn0⟩`. Establish `h4 : HasProd (fun p : Nat.Primes => if p ∈ S then Qp c n p s else 1) (∏ p ∈ S, if p ∈ S then Qp c n p s else 1)` using `hasProd_prod_of_ne_finset_one fun p hp => by simp [hp]`.

Establish `h5 : (∏ p ∈ S, if p ∈ S then Qp c n p s else 1) = ∏ p ∈ n.natAbs.primeFactors, Qp c n p s`. Rewrite using `[Finset.prod_congr rfl fun p hp => if_pos hp]`. Conclude with `Finset.prod_subtype_of_mem (fun p : ℕ => Qp c n p s) fun p hp => Nat.prime_of_mem_primeFactors hp`. Rewrite `h4` using `[h5]`. Use `h1.unique ?_` and prove the remaining obligations.

Use `h3.mul h4 using 2 with p` and compare the differences between its conclusion and the goal. Distinguish the cases in `hp : p ∈ S`. Rewrite using `[if_pos hp, tw_prime_dvd c p.2 ((hS p).1 hp)]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hp, mul_one]`.

Conclude with `Qp_off hN h2 c p.2 (fun h => hp ((hS p).2 h)) hs0`.
-/
theorem product_eq (hN : N2) (hA : A2) [NeZero M] (h2 : 2 ∣ M) (c : DirichletCharacter ℂ M) {n : ℤ}
    (hn : n ≠ 0) {s : ℂ} (hs : 2 < s.re) :
    DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c n s =
      LSeries (tw c n) s * ∏ p ∈ n.natAbs.primeFactors, Qp c n p s := by
  have hn0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  have hs0 : 0 < s.re := by linarith
  have h1 : HasProd (fun p : Nat.Primes => Qp c n p s)
      (DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c n s) := (hA M c n s hs).2
  have h3 := tw_euler h2 c n (s := s) (by linarith)
  let S : Finset Nat.Primes := n.natAbs.primeFactors.subtype Nat.Prime
  have hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℤ) ∣ n := by
    intro p
    have hm : p ∈ S ↔ (p : ℕ) ∈ n.natAbs.primeFactors := Finset.mem_subtype
    rw [hm, Nat.mem_primeFactors]
    constructor
    · rintro ⟨_, h, _⟩
      exact Int.natCast_dvd.2 h
    · intro h
      exact ⟨p.2, Int.natCast_dvd.1 h, hn0⟩
  have h4 : HasProd (fun p : Nat.Primes => if p ∈ S then Qp c n p s else 1)
      (∏ p ∈ S, if p ∈ S then Qp c n p s else 1) :=
    hasProd_prod_of_ne_finset_one fun p hp => by simp [hp]
  have h5 : (∏ p ∈ S, if p ∈ S then Qp c n p s else 1) =
      ∏ p ∈ n.natAbs.primeFactors, Qp c n p s := by
    rw [Finset.prod_congr rfl fun p hp => if_pos hp]
    exact Finset.prod_subtype_of_mem (fun p : ℕ => Qp c n p s)
      fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [h5] at h4
  refine h1.unique ?_
  convert h3.mul h4 using 2 with p
  by_cases hp : p ∈ S
  · rw [if_pos hp, tw_prime_dvd c p.2 ((hS p).1 hp)]
    simp
  · rw [if_neg hp, mul_one]
    exact Qp_off hN h2 c p.2 (fun h => hp ((hS p).2 h)) hs0

end GlobalTheory.CompanionTheory.HalfInt

open GlobalTheory.CompanionTheory.HalfInt in
/- English proof (translation)
Introduce and unpack `⟨C₀, hC₀⟩ hN hA M _ h2 c`. Take `⟨B, hB⟩` from `pow_unbounded_of_one_lt K0 (one_lt_two : (1 : ℝ) < 2)`. Use `⟨|C₀| * (4 * M) ^ 2, B + 3, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hMpos : 0 < M` using `Nat.pos_of_ne_zero (NeZero.ne M)`. Establish `hn0 : 0 < n.natAbs` using `Int.natAbs_pos.2 hn`.

Take `⟨G, hGd, hGe, hGb⟩` from `hC₀ (4 * M * n.natAbs) (tw c n) (by positivity) (tw_periodic h2 c) (tw_norm c n)`. Establish `hsub : HP (1 / 4) ⊆ HP (-1)` using `fun s hs => by`. Establish `: (1 / 4 : ℝ) < s.re` using `hs`. Use `show (-1 : ℝ) < s.re`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨fun s => G s * ∏ p ∈ n.natAbs.primeFactors, Qp c n p s, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hGd.mono hsub).mul ?_` and prove the remaining obligations. Conclude with `DifferentiableOn.fun_finset_prod fun p hp => Qp_diff hN h2 c hn (Nat.prime_of_mem_primeFactors hp)`. Introduce `s hs`. Use `product_eq hN hA h2 c hn hs` as an intermediate fact.

Simplify using `only`. Rewrite using `[hGe s (by linarith)]`. Take the linear combination `(-(s - 1)) * this`. Introduce `s hs`. Establish `hb` using `hGb s (by linarith)`.

Establish `hp` using `prod_bound hN h2 c hn hB (s := s) hs`. Establish `hq : (((4 * M * n.natAbs : ℕ) : ℝ)) = 4 * M * |(n : ℝ)|`. Use `push_cast`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite `hb` using `[hq]`.

Rewrite using `[norm_mul]`. Establish `hbd : ‖G s‖ ≤ |C₀| * (4 * M * |(n : ℝ)|) ^ 2 * (1 + ‖s‖) ^ 4`. Use `hb.trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `le_abs_self _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1 := by
  rintro ⟨C₀, hC₀⟩ hN hA M _ h2 c
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt K0 (one_lt_two : (1 : ℝ) < 2)
  refine ⟨|C₀| * (4 * M) ^ 2, B + 3, fun n hn => ?_⟩
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hn0 : 0 < n.natAbs := Int.natAbs_pos.2 hn
  obtain ⟨G, hGd, hGe, hGb⟩ := hC₀ (4 * M * n.natAbs) (tw c n) (by positivity)
    (tw_periodic h2 c) (tw_norm c n)
  have hsub : HP (1 / 4) ⊆ HP (-1) := fun s hs => by
    have : (1 / 4 : ℝ) < s.re := hs
    show (-1 : ℝ) < s.re
    linarith
  refine ⟨fun s => G s * ∏ p ∈ n.natAbs.primeFactors, Qp c n p s, ?_, ?_, ?_⟩
  · refine (hGd.mono hsub).mul ?_
    exact DifferentiableOn.fun_finset_prod fun p hp =>
      Qp_diff hN h2 c hn (Nat.prime_of_mem_primeFactors hp)
  · intro s hs
    have := product_eq hN hA h2 c hn hs
    simp only
    rw [hGe s (by linarith)]
    linear_combination (-(s - 1)) * this
  · intro s hs
    have hb := hGb s (by linarith)
    have hp := prod_bound hN h2 c hn hB (s := s) hs
    have hq : (((4 * M * n.natAbs : ℕ) : ℝ)) = 4 * M * |(n : ℝ)| := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hq] at hb
    rw [norm_mul]
    have hbd : ‖G s‖ ≤ |C₀| * (4 * M * |(n : ℝ)|) ^ 2 * (1 + ‖s‖) ^ 4 := by
      refine hb.trans ?_
      gcongr
      exact le_abs_self _
    calc ‖G s‖ * ‖∏ p ∈ n.natAbs.primeFactors, Qp c n p s‖
        ≤ (|C₀| * (4 * M * |(n : ℝ)|) ^ 2 * (1 + ‖s‖) ^ 4) * |(n : ℝ)| ^ (B + 1) :=
          mul_le_mul hbd hp (norm_nonneg _) (by positivity)
      _ = |C₀| * (4 * M) ^ 2 * |(n : ℝ)| ^ (B + 3) * (1 + ‖s‖) ^ 4 := by ring
