import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReprMem

open NumberField IntermediateField

namespace UpperTheory.RootOfUnityNormQuadraticSubfield
open Polynomial

/- English proof (translation)
Use `symm`. Use `minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime Nat.prime_two hc) ?_ (monic_X_pow_sub_C c two_ne_zero)` and prove the remaining obligations. Simplify using `[ht]`.
-/
private lemma minpoly_eq {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) :
    minpoly F t = X ^ 2 - C c := by
  symm
  refine minpoly.eq_of_irreducible_of_monic
    (X_pow_sub_C_irreducible_of_prime Nat.prime_two hc) ?_ (monic_X_pow_sub_C c two_ne_zero)
  simp [ht]

/- English proof (translation)
Assemble the required witnesses or components as `⟨X ^ 2 - C c, monic_X_pow_sub_C c two_ne_zero, by simp [ht]⟩`.
-/
private lemma isInt {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) : IsIntegral F t :=
  ⟨X ^ 2 - C c, monic_X_pow_sub_C c two_ne_zero, by simp [ht]⟩

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin.finrank (isInt t c ht), minpoly_eq t c ht hc, natDegree_X_pow_sub_C]`.
-/
private lemma finrank_eq {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) :
    Module.finrank F F⟮t⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (isInt t c ht), minpoly_eq t c ht hc,
    natDegree_X_pow_sub_C]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ReprMem.repr_mem t c ht x hx`.
-/
private lemma repr_mem {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (x : E) (hx : x ∈ F⟮t⟯) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t :=
  _root_.UpperTheory.Reformulated.B.ReprMem.repr_mem t c ht x hx

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `repr_mem t c ht x hx`. Establish `inj` using `(algebraMap F E).injective`. Distinguish the cases in `ha : a = 0`. Use `right`. Use `⟨b, inj ?_⟩` and prove the remaining obligations.

Rewrite using `[← he, ha, map_mul, map_pow, ← ht, map_zero]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hb : b = 0`. Use `left`. Use `⟨a, inj ?_⟩` and prove the remaining obligations.

Rewrite using `[← he, hb, map_pow, map_zero]`. Expand and normalize the polynomial expressions, which then agree. It suffices to derive a contradiction. Establish `h2 : (2 * a * b : F) ≠ 0` using `by simp [ha, hb]`. Apply `hc ((e - a ^ 2 - b ^ 2 * c) / (2 * a * b))` to reduce the goal to its premises.

Apply `inj` to reduce the goal to its premises. Rewrite using `[← ht, map_pow]`. Use `congr 1`. Establish `h3 : algebraMap F E (2 * a * b) ≠ 0`. Rewrite using `[Ne, map_eq_zero]` and apply the resulting hypothesis.

Rewrite using `[map_div₀, div_eq_iff h3]`. Simplify using `only [map_sub, map_mul, map_pow, ← he, ← ht, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sq_cases {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) (x : E) (hx : x ∈ F⟮t⟯) (e : F)
    (he : x ^ 2 = algebraMap F E e) : (∃ a : F, e = a ^ 2) ∨ ∃ b : F, e = c * b ^ 2 := by
  obtain ⟨a, b, rfl⟩ := repr_mem t c ht x hx
  have inj := (algebraMap F E).injective
  by_cases ha : a = 0
  · right
    refine ⟨b, inj ?_⟩
    rw [← he, ha, map_mul, map_pow, ← ht, map_zero]; ring
  by_cases hb : b = 0
  · left
    refine ⟨a, inj ?_⟩
    rw [← he, hb, map_pow, map_zero]; ring
  exfalso
  have h2 : (2 * a * b : F) ≠ 0 := by simp [ha, hb]
  apply hc ((e - a ^ 2 - b ^ 2 * c) / (2 * a * b))
  apply inj
  rw [← ht, map_pow]
  congr 1
  have h3 : algebraMap F E (2 * a * b) ≠ 0 := by
    rwa [Ne, map_eq_zero]
  rw [map_div₀, div_eq_iff h3]
  simp only [map_sub, map_mul, map_pow, ← he, ← ht, map_ofNat]
  ring

/- English proof (translation)
Introduce `h`. Establish `h1 : IsSquare ((c * d : ℕ) : ℚ)` using `⟨d * b, by push_cast; rw [h]; ring⟩`. Rewrite `h1` using `[Rat.isSquare_natCast_iff]`. Take `⟨k, hk⟩` from `h1`. Establish `h2 : d ∣ k`.

Establish `: d ∣ k * k` using `⟨c, by rw [← hk]; ring⟩`. Conclude with `(hd.dvd_mul.mp this).elim id id`. Take `⟨l, rfl⟩` from `h2`. Establish `h3 : c = d * (l * l)`. Apply `Nat.eq_of_mul_eq_mul_right hd.pos` to reduce the goal to its premises.

Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd (Nat.le_of_dvd hc ⟨_, h3⟩) (by omega)`.
-/
private lemma rat_nsq (d c : ℕ) (hd : d.Prime) (hc : 0 < c) (hcd : c < d) (b : ℚ) :
    (c : ℚ) ≠ d * b ^ 2 := by
  intro h
  have h1 : IsSquare ((c * d : ℕ) : ℚ) := ⟨d * b, by push_cast; rw [h]; ring⟩
  rw [Rat.isSquare_natCast_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have h2 : d ∣ k := by
    have : d ∣ k * k := ⟨c, by rw [← hk]; ring⟩
    exact (hd.dvd_mul.mp this).elim id id
  obtain ⟨l, rfl⟩ := h2
  have h3 : c = d * (l * l) := by
    apply Nat.eq_of_mul_eq_mul_right hd.pos
    rw [hk]; ring
  exact absurd (Nat.le_of_dvd hc ⟨_, h3⟩) (by omega)

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => intro y h h'`. Simplify using `at h`. Conclude with `absurd h h'`. Consider the case `succ a ih`.

Introduce `y h h'`. Distinguish the cases in `h2 : y ^ 2 = 1`. Conclude with `⟨1, by simpa [h'] using (sq_eq_one_iff.mp h2)⟩`. Take `⟨j, hj⟩` from `ih (y ^ 2) (by rw [← pow_mul, ← pow_succ', h]) h2`. Conclude with `⟨2 * j, by rw [pow_mul, hj]⟩`.
-/
private lemma exists_neg_one {R : Type} [Field R] (a : ℕ) :
    ∀ y : R, y ^ 2 ^ a = 1 → y ≠ 1 → ∃ j : ℕ, y ^ j = -1 := by
  induction a with
  | zero => intro y h h'; simp at h; exact absurd h h'
  | succ a ih =>
    intro y h h'
    by_cases h2 : y ^ 2 = 1
    · exact ⟨1, by simpa [h'] using (sq_eq_one_iff.mp h2)⟩
    · obtain ⟨j, hj⟩ := ih (y ^ 2) (by rw [← pow_mul, ← pow_succ', h]) h2
      exact ⟨2 * j, by rw [pow_mul, hj]⟩

section
variable {E : Type} [Field E] [NumberField E] (s : E) (d : ℕ) (hd : d.Prime) (h3 : 3 < d)
  (hs : s ^ 2 = -(d : E))
include hd h3 hs

omit hd in
/- English proof (translation)
Introduce `b h`. Establish `: (3 : ℚ) < d` using `by exact_mod_cast h3`. Use polynomial arithmetic with `[sq_nonneg b]`.
-/
private lemma d_nsq : ∀ b : ℚ, b ^ 2 ≠ -(d : ℚ) := by
  intro b h
  have : (3 : ℚ) < d := by exact_mod_cast h3
  nlinarith [sq_nonneg b]

omit hd h3 in
/- English proof (translation)
Simplify using `[hs]`.
-/
private lemma hs' : s ^ 2 = algebraMap ℚ E (-(d : ℚ)) := by simp [hs]

/- English proof (translation)
Introduce `h`. Establish `h1 : (k : E) ^ 2 = algebraMap ℚ E (-(c : ℚ))`. Use `congrArg (fun x : ℚ⟮s⟯ => (x : E)) h` as an intermediate fact. Simplify using `using this`. Establish `hc' : (0 : ℚ) < c` using `by exact_mod_cast hc`.

Break down `sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩` into its components or cases. Use polynomial arithmetic with `[sq_nonneg a]`. Conclude with `rat_nsq d c hd hc (by omega) b (by linarith)`.
-/
private lemma neg_nsq (c : ℕ) (hc : 0 < c) (hc3 : c ≤ 3) (k : ℚ⟮s⟯) : k ^ 2 ≠ -(c : ℚ⟮s⟯) := by
  intro h
  have h1 : (k : E) ^ 2 = algebraMap ℚ E (-(c : ℚ)) := by
    have := congrArg (fun x : ℚ⟮s⟯ => (x : E)) h
    simpa using this
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  rcases sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩
  · nlinarith [sq_nonneg a]
  · exact rat_nsq d c hd hc (by omega) b (by linarith)

/- English proof (translation)
Introduce `h`. Establish `h1 : (k : E) ^ 2 = algebraMap ℚ E 2`. Use `congrArg (algebraMap ℚ⟮s⟯ E) h` as an intermediate fact. Rewrite `this` using `[map_pow, map_ofNat]`. Rewrite using `[map_ofNat]`.

Conclude with `this`. Establish `hd' : (3 : ℚ) < d` using `by exact_mod_cast h3`. Break down `sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩` into its components or cases. Use `rat_nsq 2 1 Nat.prime_two one_pos one_lt_two (a / 2) ?_` and prove the remaining obligations. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Use polynomial arithmetic with `[sq_nonneg b]`.
-/
private lemma two_nsq (k : ℚ⟮s⟯) : k ^ 2 ≠ 2 := by
  intro h
  have h1 : (k : E) ^ 2 = algebraMap ℚ E 2 := by
    have := congrArg (algebraMap ℚ⟮s⟯ E) h
    rw [map_pow, map_ofNat] at this
    rw [map_ofNat]
    exact this
  have hd' : (3 : ℚ) < d := by exact_mod_cast h3
  rcases sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩
  · refine rat_nsq 2 1 Nat.prime_two one_pos one_lt_two (a / 2) ?_
    push_cast
    nlinarith
  · nlinarith [sq_nonneg b]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hdvd : orderOf w ∣ o` using `orderOf_dvd_of_pow_eq_one hw`. Establish `hn1 : orderOf w ≠ 1` using `fun h => hne (orderOf_eq_one_iff.mp h)`. Establish `hnodd : Odd (orderOf w)` using `ho.of_dvd_nat hdvd`. Take `⟨p, hp, q, hq⟩` from `Nat.exists_prime_and_dvd hn1`.

Establish `hu : IsPrimitiveRoot (w ^ q) p` using `(IsPrimitiveRoot.orderOf w).pow hnodd.pos (by rw [hq, mul_comm])`. Establish `hpodd : Odd p` using `hnodd.of_dvd_nat ⟨q, hq⟩`. Establish `hle : p - 1 ≤ 2`. Rewrite using `[← Nat.totient_prime hp, ← natDegree_cyclotomic p ℚ, cyclotomic_eq_minpoly_rat hu hp.pos, ← finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)]`. Conclude with `minpoly.natDegree_le _`.

Establish `hp3 : p = 3`. Use `hp.two_le` as an intermediate fact. Take `⟨r, hr⟩` from `hpodd`. Use linear arithmetic over natural numbers and integers. Substitute `hp3` using the available equality.

Establish `h1` using `hu.pow_eq_one`. Establish `h2` using `hu.ne_one (by norm_num)`. Use `set u := w ^ q`. Establish `h4 : u ^ 2 + u + 1 = 0`. Establish `: (u - 1) * (u ^ 2 + u + 1) = 0` using `by linear_combination h1`.

Conclude with `(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)`. Apply `neg_nsq s d hd h3 hs 3 (by norm_num) le_rfl (2 * u + 1)` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `4 * h4`.
-/
private lemma odd_root (w : ℚ⟮s⟯) (o : ℕ) (ho : Odd o) (hw : w ^ o = 1) : w = 1 := by
  by_contra hne
  have hdvd : orderOf w ∣ o := orderOf_dvd_of_pow_eq_one hw
  have hn1 : orderOf w ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have hnodd : Odd (orderOf w) := ho.of_dvd_nat hdvd
  obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd hn1
  have hu : IsPrimitiveRoot (w ^ q) p :=
    (IsPrimitiveRoot.orderOf w).pow hnodd.pos (by rw [hq, mul_comm])
  have hpodd : Odd p := hnodd.of_dvd_nat ⟨q, hq⟩
  have hle : p - 1 ≤ 2 := by
    rw [← Nat.totient_prime hp, ← natDegree_cyclotomic p ℚ,
      cyclotomic_eq_minpoly_rat hu hp.pos, ← finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)]
    exact minpoly.natDegree_le _
  have hp3 : p = 3 := by
    have := hp.two_le
    obtain ⟨r, hr⟩ := hpodd
    omega
  subst hp3
  have h1 := hu.pow_eq_one
  have h2 := hu.ne_one (by norm_num)
  set u := w ^ q
  have h4 : u ^ 2 + u + 1 = 0 := by
    have : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  apply neg_nsq s d hd h3 hs 3 (by norm_num) le_rfl (2 * u + 1)
  push_cast
  linear_combination 4 * h4

/- English proof (translation)
Distinguish the cases in `h2 : y ^ 2 = 1`. Establish `hev : Even (Module.finrank ℚ⟮s⟯ E)`. Rewrite `h4` using `[← Module.finrank_mul_finrank ℚ ℚ⟮s⟯ E, finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)]`. Rewrite using `[even_iff_two_dvd]`. Use linear arithmetic over natural numbers and integers.

Break down `(sq_eq_one_iff.mp h2) with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Establish `: (-1 : E) = algebraMap ℚ⟮s⟯ E (-1)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, hev.neg_one_pow]`. Take `⟨j, hj⟩` from `exists_neg_one a (y ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]) h2`.

Use `set K := ℚ⟮s⟯ with hK`. Use `set i := y ^ j with hi`. Establish `hi2 : i ^ 2 = algebraMap K E (-1)`. Rewrite using `[hi, ← pow_mul, mul_comm, pow_mul, hj]`. Simplify using the standard rewrite rules.

Establish `hn : ∀ b : K, b ^ 2 ≠ -1` using `fun b => by`. Simplify using `using neg_nsq s d hd h3 hs 1 one_pos (by norm_num) b`. Establish `hfr` using `finrank_eq i _ hi2 hn`. Rewrite using `[← Algebra.norm_norm (S := K⟮i⟯)]`. Establish `hv : (Algebra.norm K⟮i⟯ y) ^ 2 ^ a = 1` using `by rw [← map_pow, hy, map_one]`.

Use `set v := Algebra.norm K⟮i⟯ y`. Establish `hv4 : v ^ 4 = 1`. Assume the negation of the conclusion as `hne`. Take `⟨l, hl⟩` from `exists_neg_one a (v ^ 4) (by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]) hne`. Establish `hw : (v ^ l) ^ 4 = -1` using `by rw [← pow_mul, mul_comm, pow_mul, hl]`.

Use `set w := v ^ l`. Establish `hx : (w - w ^ 3) ^ 2 = 2` using `by linear_combination (w ^ 2 - 2) * hw`. Establish `hx' : ((w - w ^ 3 : K⟮i⟯) : E) ^ 2 = algebraMap K E 2`. Use `congrArg (algebraMap K⟮i⟯ E) hx` as an intermediate fact. Rewrite `this` using `[map_pow, map_ofNat]`.

Rewrite using `[map_ofNat]`. Conclude with `this`. Break down `sq_cases i _ hi2 hn _ (w - w ^ 3).2 _ hx' with ⟨b, hb⟩ | ⟨b, hb⟩` into its components or cases. Conclude with `two_nsq s d hd h3 hs b hb.symm`. Apply `neg_nsq s d hd h3 hs 2 two_pos (by norm_num) b` to reduce the goal to its premises.

Use `push_cast`. Take the linear combination `hb`. Establish `hm1 : Algebra.norm K (-1 : K⟮i⟯) = 1`. Establish `: (-1 : K⟮i⟯) = algebraMap K K⟮i⟯ (-1)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, hfr]`.

Evaluate the numerical expressions. Establish `hg : Algebra.norm K (AdjoinSimple.gen K i) = 1`. Use `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis (isInt i _ hi2))` as an intermediate fact. Rewrite `this` using `[IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim, IntermediateField.minpoly_gen, minpoly_eq i _ hi2 hn, natDegree_X_pow_sub_C]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hg2 : (AdjoinSimple.gen K i) ^ 2 = -1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hi2`. Use `set g := AdjoinSimple.gen K i`.

Establish `: (v - 1) * (v + 1) * (v - g) * (v + g) = 0`. Take the linear combination `hv4 - (v ^ 2 - 1) * hg2`. Simplify using `only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this`. Break down `this with ((h | h) | h) | h` into its components or cases. Rewrite using `[h, map_one]`.

Rewrite using `[h, hm1]`. Rewrite using `[h, hg]`. Rewrite using `[h, ← neg_one_mul, map_mul, hm1, hg, one_mul]`.
-/
private lemma two_pow_norm (h4 : 4 ∣ Module.finrank ℚ E) (y : E) (a : ℕ) (hy : y ^ 2 ^ a = 1) :
    Algebra.norm ℚ⟮s⟯ y = 1 := by
  by_cases h2 : y ^ 2 = 1
  · have hev : Even (Module.finrank ℚ⟮s⟯ E) := by
      rw [← Module.finrank_mul_finrank ℚ ℚ⟮s⟯ E,
        finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)] at h4
      rw [even_iff_two_dvd]
      omega
    rcases (sq_eq_one_iff.mp h2) with rfl | rfl
    · simp
    · have : (-1 : E) = algebraMap ℚ⟮s⟯ E (-1) := by simp
      rw [this, Algebra.norm_algebraMap, hev.neg_one_pow]
  obtain ⟨j, hj⟩ := exists_neg_one a (y ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]) h2
  set K := ℚ⟮s⟯ with hK
  set i := y ^ j with hi
  have hi2 : i ^ 2 = algebraMap K E (-1) := by
    rw [hi, ← pow_mul, mul_comm, pow_mul, hj]; simp
  have hn : ∀ b : K, b ^ 2 ≠ -1 := fun b => by
    simpa using neg_nsq s d hd h3 hs 1 one_pos (by norm_num) b
  have hfr := finrank_eq i _ hi2 hn
  rw [← Algebra.norm_norm (S := K⟮i⟯)]
  have hv : (Algebra.norm K⟮i⟯ y) ^ 2 ^ a = 1 := by rw [← map_pow, hy, map_one]
  set v := Algebra.norm K⟮i⟯ y
  have hv4 : v ^ 4 = 1 := by
    by_contra hne
    obtain ⟨l, hl⟩ := exists_neg_one a (v ^ 4)
      (by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]) hne
    have hw : (v ^ l) ^ 4 = -1 := by rw [← pow_mul, mul_comm, pow_mul, hl]
    set w := v ^ l
    have hx : (w - w ^ 3) ^ 2 = 2 := by linear_combination (w ^ 2 - 2) * hw
    have hx' : ((w - w ^ 3 : K⟮i⟯) : E) ^ 2 = algebraMap K E 2 := by
      have := congrArg (algebraMap K⟮i⟯ E) hx
      rw [map_pow, map_ofNat] at this
      rw [map_ofNat]
      exact this
    rcases sq_cases i _ hi2 hn _ (w - w ^ 3).2 _ hx' with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact two_nsq s d hd h3 hs b hb.symm
    · apply neg_nsq s d hd h3 hs 2 two_pos (by norm_num) b
      push_cast
      linear_combination hb
  have hm1 : Algebra.norm K (-1 : K⟮i⟯) = 1 := by
    have : (-1 : K⟮i⟯) = algebraMap K K⟮i⟯ (-1) := by simp
    rw [this, Algebra.norm_algebraMap, hfr]; norm_num
  have hg : Algebra.norm K (AdjoinSimple.gen K i) = 1 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis (isInt i _ hi2))
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen, minpoly_eq i _ hi2 hn, natDegree_X_pow_sub_C] at this
    rw [this]; simp
  have hg2 : (AdjoinSimple.gen K i) ^ 2 = -1 := by
    apply Subtype.ext
    simpa using hi2
  set g := AdjoinSimple.gen K i
  have : (v - 1) * (v + 1) * (v - g) * (v + g) = 0 := by
    linear_combination hv4 - (v ^ 2 - 1) * hg2
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
  rcases this with ((h | h) | h) | h
  · rw [h, map_one]
  · rw [h, hm1]
  · rw [h, hg]
  · rw [h, ← neg_one_mul, map_mul, hm1, hg, one_mul]

end
end UpperTheory.RootOfUnityNormQuadraticSubfield

/- English proof (translation)
Introduce `E _ _ s d hd h3 hs h4 z ⟨m, hm, hz⟩`. Take `⟨a, o, ho, rfl⟩` from `Nat.exists_eq_two_pow_mul_odd hm.ne'`. Apply `UpperTheory.RootOfUnityNormQuadraticSubfield.odd_root s d hd h3 hs _ o ho` to reduce the goal to its premises. Rewrite using `[← map_pow]`. Conclude with `UpperTheory.RootOfUnityNormQuadraticSubfield.two_pow_norm s d hd h3 hs h4 _ a (by rw [← pow_mul, mul_comm, hz])`.
-/
theorem UpperTheory.norm_root_of_unity_quadratic_subfield :
    ∀ (E : Type) [Field E] [NumberField E] (s : E) (d : ℕ), d.Prime → 3 < d → s ^ 2 = -(d : E) → 4 ∣ Module.finrank ℚ E →
      ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → Algebra.norm ℚ⟮s⟯ z = 1 := by
  intro E _ _ s d hd h3 hs h4 z ⟨m, hm, hz⟩
  obtain ⟨a, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  apply UpperTheory.RootOfUnityNormQuadraticSubfield.odd_root s d hd h3 hs _ o ho
  rw [← map_pow]
  exact UpperTheory.RootOfUnityNormQuadraticSubfield.two_pow_norm s d hd h3 hs h4 _ a (by rw [← pow_mul, mul_comm, hz])
