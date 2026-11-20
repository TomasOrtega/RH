import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.PlogMul

open Polynomial

variable {B : Type} [CommRing B]

noncomputable def logPoly (c : ℕ → B) (s : ℕ) : B[X] :=
  ∑ k ∈ Finset.range s, C ((-1) ^ k * c k) * X ^ (k + 1)

/- English proof (translation)
Unfold `logPoly`. Rewrite using `[derivative_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1 : (C (c k) : B[X]) * ((k : B[X]) + 1) = 1`. Use `congrArg (C : B →+* B[X]) (hc k)` as an intermediate fact.

Simplify using `using this`. Rewrite using `[derivative_C_mul, derivative_X_pow, neg_pow (X : B[X]) k]`. Simplify using `only [Nat.add_sub_cancel, map_mul, map_pow, map_neg, map_one, Nat.cast_add, Nat.cast_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_add, map_natCast, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h1, mul_one]`.
-/
theorem derivative_logPoly (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1) (s : ℕ) :
    derivative (logPoly c s) = ∑ k ∈ Finset.range s, (-X) ^ k := by
  unfold logPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (C (c k) : B[X]) * ((k : B[X]) + 1) = 1 := by
    have := congrArg (C : B →+* B[X]) (hc k)
    simpa using this
  rw [derivative_C_mul, derivative_X_pow, neg_pow (X : B[X]) k]
  simp only [Nat.add_sub_cancel, map_mul, map_pow, map_neg, map_one, Nat.cast_add, Nat.cast_one]
  calc _ = (-1) ^ k * (C (c k) * ((k : B[X]) + 1)) * X ^ k := by
        simp only [map_add, map_natCast, map_one]; ring
    _ = _ := by rw [h1, mul_one]

/- English proof (translation)
Use `mul_neg_geom_sum (-u) s` as an intermediate fact. Simplify using `using this`.
-/
theorem one_add_mul_geom {R : Type} [CommRing R] (u : R) (s : ℕ) :
    (1 + u) * ∑ k ∈ Finset.range s, (-u) ^ k = 1 - (-u) ^ s := by
  have := mul_neg_geom_sum (-u) s
  simpa using this

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ n ih => simp [Finset.sum_range_succ, ih]`.
-/
theorem geom_comp (s : ℕ) (u : B[X]) :
    (∑ k ∈ Finset.range s, (-X : B[X]) ^ k).comp u = ∑ k ∈ Finset.range s, (-u) ^ k := by
  induction s with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]

/- English proof (translation)
Simplify using `[logPoly, eval_finset_sum]`.
-/
theorem eval_logPoly_zero (c : ℕ → B) (s : ℕ) : (logPoly c s).eval 0 = 0 := by
  simp [logPoly, eval_finset_sum]

/- English proof (translation)
Use `set a : B[X] := C x * X with ha`. Use `set Z : B[X] := (1 + a) * (1 + C y) - 1 with hZ`. Use `set G : B[X] := (logPoly c s).comp Z - (logPoly c s).comp a - C ((logPoly c s).eval y) with hG`. Establish `has : a ^ s = 0`. Establish `h` using `hxy s 0 (by simp)`.

Establish `h' : x ^ s = 0` using `by simpa using h`. Rewrite using `[ha, mul_pow, ← C_pow, h']`. Simplify using the standard rewrite rules. Establish `hZs : Z ^ s = 0`. Establish `hZ' : Z = a * (1 + C y) + C y` using `by rw [hZ]; ring`.

Rewrite using `[hZ', add_pow]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ s` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Establish `h0` using `hxy i (s - i) (by omega)`. Establish `: (a * (1 + C y)) ^ i * (C y) ^ (s - i) = C (x ^ i * y ^ (s - i)) * (X ^ i * (1 + C y) ^ i)`.

Rewrite using `[ha, C_mul, C_pow, C_pow, mul_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h0]`. Simplify using the standard rewrite rules. Establish `hderiv : derivative G = 0`.

Establish `hda : derivative a = C x` using `by rw [ha]; simp`. Establish `hdZ : derivative Z = C x * (1 + C y)`. Rewrite using `[hZ]`. Simplify using `[hda]`. Establish `hD : derivative G = C x * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) - C x * (∑ k ∈ Finset.range s, (-a) ^ k)`.

Rewrite using `[hG, derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_comp, derivative_comp, derivative_logPoly c hc, hdZ, hda]`. Rewrite using `[geom_comp, geom_comp]`. Establish `h1 : (1 + a) * (∑ k ∈ Finset.range s, (-a) ^ k) = 1`. Rewrite using `[one_add_mul_geom, neg_pow, has]`. Simplify using the standard rewrite rules.

Establish `h2 : (1 + a) * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) = 1`. Use `one_add_mul_geom Z s` as an intermediate fact. Rewrite `this` using `[neg_pow, hZs]`. Establish `e : 1 + Z = (1 + a) * (1 + C y)` using `by rw [hZ]; ring`. Rewrite using `[← e, this]`.

Simplify using the standard rewrite rules. Establish `h3 : (1 + a) * derivative G = 0`. Rewrite using `[hD]`. Take the linear combination `(C x) * h2 - (C x) * h1`. Establish `h4 : derivative G = (∑ k ∈ Finset.range s, (-a) ^ k) * ((1 + a) * derivative G)`.

Take the linear combination `(- derivative G) * h1`. Rewrite using `[h4, h3, mul_zero]`. Establish `hG0 : G.eval 0 = 0`. Simplify using `[hG, hZ, ha, eval_comp, eval_logPoly_zero]`. Establish `hGC : G = C (G.eval 0)`.

Use extensionality with `n`. Consider the cases of `n with`. Consider the case `zero => simp [coeff_zero_eq_eval_zero]`. Consider the case `succ n`. Establish `h` using `congrArg (fun p => coeff p n) hderiv`.

Simplify using `only [coeff_derivative, coeff_zero] at h`. Establish `hn : IsUnit ((n : B) + 1)`. Use `hu (n + 1) (by omega)` as an intermediate fact. Simplify using `using this`. Establish `: G.coeff (n + 1) = 0` using `hn.mul_left_eq_zero.1 h`.

Simplify using `[this, coeff_C]`. Establish `hG1 : G.eval 1 = 0`. Rewrite using `[hGC, hG0]`. Simplify using the standard rewrite rules. Establish `: (logPoly c s).eval ((1 + x) * (1 + y) - 1) - (logPoly c s).eval x - (logPoly c s).eval y = 0`.

Simplify `hG1` using `[hG, hZ, ha, eval_comp]`. Take the linear combination `this`.
-/
theorem eval_logPoly_mul (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) (s : ℕ) {x y : B}
    (hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0) :
    (logPoly c s).eval ((1 + x) * (1 + y) - 1) = (logPoly c s).eval x + (logPoly c s).eval y := by
  set a : B[X] := C x * X with ha
  set Z : B[X] := (1 + a) * (1 + C y) - 1 with hZ
  set G : B[X] := (logPoly c s).comp Z - (logPoly c s).comp a - C ((logPoly c s).eval y) with hG
  have has : a ^ s = 0 := by
    have h := hxy s 0 (by simp)
    have h' : x ^ s = 0 := by simpa using h
    rw [ha, mul_pow, ← C_pow, h']
    simp
  have hZs : Z ^ s = 0 := by
    have hZ' : Z = a * (1 + C y) + C y := by rw [hZ]; ring
    rw [hZ', add_pow]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h0 := hxy i (s - i) (by omega)
    have : (a * (1 + C y)) ^ i * (C y) ^ (s - i) = C (x ^ i * y ^ (s - i)) * (X ^ i * (1 + C y) ^ i) := by
      rw [ha, C_mul, C_pow, C_pow, mul_pow, mul_pow]; ring
    rw [this, h0]
    simp
  have hderiv : derivative G = 0 := by
    have hda : derivative a = C x := by rw [ha]; simp
    have hdZ : derivative Z = C x * (1 + C y) := by
      rw [hZ]; simp [hda]
    have hD : derivative G = C x * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k)
        - C x * (∑ k ∈ Finset.range s, (-a) ^ k) := by
      rw [hG, derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_comp, derivative_comp,
        derivative_logPoly c hc, hdZ, hda]
      rw [geom_comp, geom_comp]
    have h1 : (1 + a) * (∑ k ∈ Finset.range s, (-a) ^ k) = 1 := by
      rw [one_add_mul_geom, neg_pow, has]; simp
    have h2 : (1 + a) * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) = 1 := by
      have := one_add_mul_geom Z s
      rw [neg_pow, hZs] at this
      have e : 1 + Z = (1 + a) * (1 + C y) := by rw [hZ]; ring
      rw [← e, this]; simp
    have h3 : (1 + a) * derivative G = 0 := by
      rw [hD]
      linear_combination (C x) * h2 - (C x) * h1
    have h4 : derivative G = (∑ k ∈ Finset.range s, (-a) ^ k) * ((1 + a) * derivative G) := by
      linear_combination (- derivative G) * h1
    rw [h4, h3, mul_zero]
  have hG0 : G.eval 0 = 0 := by
    simp [hG, hZ, ha, eval_comp, eval_logPoly_zero]
  have hGC : G = C (G.eval 0) := by
    ext n
    cases n with
    | zero => simp [coeff_zero_eq_eval_zero]
    | succ n =>
      have h := congrArg (fun p => coeff p n) hderiv
      simp only [coeff_derivative, coeff_zero] at h
      have hn : IsUnit ((n : B) + 1) := by
        have := hu (n + 1) (by omega)
        simpa using this
      have : G.coeff (n + 1) = 0 := hn.mul_left_eq_zero.1 h
      simp [this, coeff_C]
  have hG1 : G.eval 1 = 0 := by
    rw [hGC, hG0]; simp
  have : (logPoly c s).eval ((1 + x) * (1 + y) - 1) - (logPoly c s).eval x - (logPoly c s).eval y = 0 := by
    simpa [hG, hZ, ha, eval_comp] using hG1
  linear_combination this

/- English proof (translation)
Establish `hunit : ∀ k : ℕ, IsUnit ((k : B) + 1)` using `fun k => by`. Use `hu (k + 1) (by omega)` as an intermediate fact. Simplify using `using this`. Use `choose c hc using fun k : ℕ => (hunit k).exists_left_inv`. Establish `hlog : ∀ {z : B}, z ∈ J → plogK δ s z = (logPoly c s).eval z`.

Introduce `z hz`. Simplify using `only [plogK, logPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `δ.factorial_mul_dpow_eq_pow (n := k + 1) hz`. Rewrite `h` using `[Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]`.

Rewrite using `[← h]`. Take the linear combination `(-(-1 : B) ^ k * (k.factorial : B) * δ.dpow (k + 1) z) * hc k`. Establish `hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0`. Introduce `a b hab`. Establish `hmem : δ.dpow a x * δ.dpow b y ∈ pdP δ s`.

Use `Ideal.subset_span ⟨[(a, x), (b, y)], ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hq`. Break down `hq with rfl | rfl` into its components or cases. Conclude with `hx`.

Conclude with `hy`. Simplify using `using hab`. Simplify using the standard rewrite rules. Rewrite `hmem` using `[hs, Ideal.mem_bot]`. Rewrite using `[← δ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]`.

Take the linear combination `((a.factorial : B) * (b.factorial : B)) * hmem`. Establish `hz : (1 + x) * (1 + y) - 1 ∈ J`. Establish `e : (1 + x) * (1 + y) - 1 = x + y + x * y` using `by ring`. Rewrite using `[e]`. Conclude with `J.add_mem (J.add_mem hx hy) (J.mul_mem_right y hx)`.

Rewrite using `[hlog hz, hlog hx, hlog hy]`. Conclude with `eval_logPoly_mul c hc hu s hxy`.
-/
theorem plogK_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ)
    (hs : pdP δ s = ⊥) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {x y : B} (hx : x ∈ J) (hy : y ∈ J) :
    plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  have hunit : ∀ k : ℕ, IsUnit ((k : B) + 1) := fun k => by
    have := hu (k + 1) (by omega)
    simpa using this
  choose c hc using fun k : ℕ => (hunit k).exists_left_inv
  have hlog : ∀ {z : B}, z ∈ J → plogK δ s z = (logPoly c s).eval z := by
    intro z hz
    simp only [plogK, logPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := δ.factorial_mul_dpow_eq_pow (n := k + 1) hz
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    linear_combination (-(-1 : B) ^ k * (k.factorial : B) * δ.dpow (k + 1) z) * hc k
  have hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0 := by
    intro a b hab
    have hmem : δ.dpow a x * δ.dpow b y ∈ pdP δ s := by
      refine Ideal.subset_span ⟨[(a, x), (b, y)], ?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hx
        · exact hy
      · simpa using hab
      · simp
    rw [hs, Ideal.mem_bot] at hmem
    rw [← δ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]
    linear_combination ((a.factorial : B) * (b.factorial : B)) * hmem
  have hz : (1 + x) * (1 + y) - 1 ∈ J := by
    have e : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [e]
    exact J.add_mem (J.add_mem hx hy) (J.mul_mem_right y hx)
  rw [hlog hz, hlog hx, hlog hy]
  exact eval_logPoly_mul c hc hu s hxy

end GlobalTheory.CompanionTheory.PlogMul
