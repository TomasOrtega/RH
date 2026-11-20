import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.RankTwoProof

variable {W : Type} [AddCommGroup W] [Module ℚ W]

/- English proof (translation)
Unfold `coef`. Rewrite using `[show k + 1 + i + 1 = (k + i + 1) + 1 by ring, Nat.factorial_succ (k + i + 1), Nat.factorial_succ k]`. Establish `a1 : ((k.factorial : ℚ)) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Establish `a2 : (((k + i + 1).factorial : ℚ)) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_succ_mul (i k : ℕ) :
    coef i (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + i + 2)) = - coef i k := by
  unfold coef
  rw [show k + 1 + i + 1 = (k + i + 1) + 1 by ring, Nat.factorial_succ (k + i + 1), Nat.factorial_succ k]
  have a1 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have a2 : (((k + i + 1).factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/- English proof (translation)
Rewrite using `[pow_succ', Module.End.mul_apply]`.
-/
theorem pow_succ_apply' (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = Y ((Y ^ k) v) := by
  rw [pow_succ', Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[← h1, ← h2]`. Use `noncomm_ring`.
-/
theorem comm_sub' (A B X x y : Module.End ℚ W) (h1 : A * X - X * A = x) (h2 : B * X - X * B = y) :
    (A - B) * X - X * (A - B) = x - y := by
  rw [← h1, ← h2]; noncomm_ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hv`. Consider the case `succ k ih`. Establish `e` using `LinearMap.congr_fun hHX ((X ^ k) v)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at e`.

Rewrite using `[pow_succ_apply', eq_add_of_sub_eq e, ih, map_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eig_pow (H X : Module.End ℚ W) (d c : ℚ) (hHX : H * X - X * H = d • X) (v : W)
    (hv : H v = c • v) (k : ℕ) : H ((X ^ k) v) = (c + k * d) • (X ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have e := LinearMap.congr_fun hHX ((X ^ k) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at e
    rw [pow_succ_apply', eq_add_of_sub_eq e, ih, map_smul, ← add_smul]
    congr 1; push_cast; ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `e` using `LinearMap.congr_fun h v`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, one_smul]`.

Rewrite using `[eq_add_of_sub_eq e]`. Normalize the expressions using the abelian group laws. Consider the case `succ k ih`. Establish `e` using `LinearMap.congr_fun h ((Y ^ (k + 1)) v)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`.

Establish `hp : P ((Y ^ (k + 1)) v) = Y (P ((Y ^ k) v))`. Rewrite using `[pow_succ_apply', ← Module.End.mul_apply P Y, hP, Module.End.mul_apply]`. Rewrite using `[pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (Z v), eq_add_of_sub_eq e, ih, hp, map_add, map_smul]`. Use `push_cast`. Use `module`.
-/
theorem comm_pow_apply (Z Y P : Module.End ℚ W) (h : Z * Y - Y * Z = P) (hP : P * Y = Y * P) (v : W)
    (k : ℕ) : Z ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (Z v) + ((k : ℚ) + 1) • P ((Y ^ k) v) := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun h v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, one_smul]
    rw [eq_add_of_sub_eq e]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun h ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hp : P ((Y ^ (k + 1)) v) = Y (P ((Y ^ k) v)) := by
      rw [pow_succ_apply', ← Module.End.mul_apply P Y, hP, Module.End.mul_apply]
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (Z v), eq_add_of_sub_eq e, ih, hp, map_add, map_smul]
    push_cast
    module

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `e` using `LinearMap.congr_fun hXY v`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]`.

Rewrite using `[eq_add_of_sub_eq e, hv]`. Normalize the expressions using the abelian group laws. Consider the case `succ k ih`. Establish `e` using `LinearMap.congr_fun hXY ((Y ^ (k + 1)) v)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`.

Establish `hH` using `eig_pow H Y (-2) c hHY v hv (k + 1)`. Rewrite using `[pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (X v), eq_add_of_sub_eq e, ih, hH, map_add, map_smul, ← pow_succ_apply' Y k v]`. Use `push_cast`. Use `module`.
-/
theorem sl2_X_Ypow (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHY : H * Y - Y * H = (-2 : ℚ) • Y)
    (v : W) (c : ℚ) (hv : H v = c • v) (k : ℕ) :
    X ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (X v) + (((k : ℚ) + 1) * (c - k)) • (Y ^ k) v := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun hXY v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
    rw [eq_add_of_sub_eq e, hv]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun hXY ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H Y (-2) c hHY v hv (k + 1)
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (X v), eq_add_of_sub_eq e, ih, hH, map_add,
      map_smul, ← pow_succ_apply' Y k v]
    push_cast
    module

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero`. Establish `e` using `LinearMap.congr_fun hXY u`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]`.

Rewrite using `[eq_add_of_sub_eq e, hu]`. Normalize the expressions using the abelian group laws. Consider the case `succ l ih`. Establish `e` using `LinearMap.congr_fun hXY ((X ^ (l + 1)) u)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`.

Establish `hH` using `eig_pow H X 2 c hHX u hu (l + 1)`. Rewrite using `[pow_succ_apply' X (l + 1) (Y u), ih, map_add, map_smul, eq_add_of_sub_eq e, hH, ← pow_succ_apply' X (l + 1) u, ← pow_succ_apply' X l u]`. Use `push_cast`. Use `module`.
-/
theorem sl2_Xpow_Y (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHX : H * X - X * H = (2 : ℚ) • X)
    (u : W) (c : ℚ) (hu : H u = c • u) (l : ℕ) :
    (X ^ (l + 1)) (Y u) = Y ((X ^ (l + 1)) u) + (((l : ℚ) + 1) * (c + l)) • (X ^ l) u := by
  induction l with
  | zero =>
    have e := LinearMap.congr_fun hXY u
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [eq_add_of_sub_eq e, hu]; abel
  | succ l ih =>
    have e := LinearMap.congr_fun hXY ((X ^ (l + 1)) u)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H X 2 c hHX u hu (l + 1)
    rw [pow_succ_apply' X (l + 1) (Y u), ih, map_add, map_smul, eq_add_of_sub_eq e, hH,
      ← pow_succ_apply' X (l + 1) u, ← pow_succ_apply' X l u]
    push_cast
    module

/- English proof (translation)
Rewrite using `[pow_succ, Module.End.mul_apply]`.
-/
theorem pow_succ_apply2 (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = (Y ^ k) (Y v) := by
  rw [pow_succ, Module.End.mul_apply]

/- English proof (translation)
Introduce `W _ _ N K D hG hB o p q ho hp hq hop hoq hpq j T hoo hpp hqq hpqT`. Establish `hpo` using `Ne.symm hop`. Establish `hqo` using `Ne.symm hoq`. Establish `hqp` using `Ne.symm hpq`. Establish `rZXp : D p q * D o p - D o p * D p q = -D o q`.

Simplify `hG p q o p hp hq ho hp` using `[hqo]`. Establish `rZXq : D p q * D o q = D o q * D p q`. Use `hG p q o q hp hq ho hq` as an intermediate fact. Simplify `this` using `[hqo, hqp, sub_eq_zero]`. Establish `rZYp : D p q * D p o = D p o * D p q`.

Use `hG p q p o hp hq hp ho` as an intermediate fact. Simplify `this` using `[hqp, hop, sub_eq_zero]`. Establish `rZYq : D p q * D q o - D q o * D p q = D p o`. Simplify `hG p q q o hp hq hq ho` using `[hop]`. Establish `rXqXp : D o q * D o p = D o p * D o q`.

Use `hG o p o q ho hp ho hq` as an intermediate fact. Conclude with `(by simpa [hpo, hqo, sub_eq_zero] using this : D o p * D o q = D o q * D o p).symm`. Establish `rYpYq : D p o * D q o = D q o * D p o`. Use `hG p o q o hp ho hq ho` as an intermediate fact. Simplify `this` using `[hoq, hop, sub_eq_zero]`.

Establish `sXYp : D o p * D p o - D p o * D o p = D o o - D p p` using `by simpa using hG o p p o ho hp hp ho`. Establish `sXYq : D o q * D q o - D q o * D o q = D o o - D q q` using `by simpa using hG o q q o ho hq hq ho`. Establish `hHpXp : (D o o - D p p) * D o p - D o p * (D o o - D p p) = (2 : ℚ) • D o p`. Rewrite using `[comm_sub' _ _ _ (D o p) (-D o p) (by simpa [hpo] using hG o o o p ho ho ho hp) (by simpa [hpo] using hG p p o p hp hp ho hp), sub_neg_eq_add, two_smul]`. Establish `hHqXq : (D o o - D q q) * D o q - D o q * (D o o - D q q) = (2 : ℚ) • D o q`.

Rewrite using `[comm_sub' _ _ _ (D o q) (-D o q) (by simpa [hqo] using hG o o o q ho ho ho hq) (by simpa [hqo] using hG q q o q hq hq ho hq), sub_neg_eq_add, two_smul]`. Establish `hHqYq : (D o o - D q q) * D q o - D q o * (D o o - D q q) = (-2 : ℚ) • D q o`. Rewrite using `[comm_sub' _ _ _ (-D q o) (D q o) (by simpa [hoq] using hG o o q o ho ho hq ho) (by simpa [hoq] using hG q q q o hq hq hq ho), neg_smul, two_smul]; abel`. Establish `hHpXq : (D o o - D p p) * D o q - D o q * (D o o - D p p) = (1 : ℚ) • D o q`. Rewrite using `[comm_sub' _ _ _ (D o q) 0 (by simpa [hqo] using hG o o o q ho ho ho hq) (by simpa [hpo, hqp] using hG p p o q hp hp ho hq), sub_zero, one_smul]`.

Establish `hHpYq : (D o o - D p p) * D q o - D q o * (D o o - D p p) = (-1 : ℚ) • D q o`. Rewrite using `[comm_sub' _ _ _ (-D q o) 0 (by simpa [hoq] using hG o o q o ho ho hq ho) (by simpa [hpq, hop] using hG p p q o hp hp hq ho), sub_zero, neg_one_smul]`. Establish `hHpT : (D o o - D p p) T = (0 : ℚ) • T` using `by simp [hoo, hpp]`. Establish `hHqT : (D o o - D q q) T = (0 : ℚ) • T` using `by simp [hoo, hqq]`. Establish `hZv : ∀ k : ℕ, D p q ((D o q ^ k) T) = 0` using `fun k => by`.

Establish `c` using `LinearMap.congr_fun (Commute.pow_right rZXq k).eq T`. Simplify using `only [Module.End.mul_apply] at c`. Rewrite using `[c, hpqT, map_zero]`. Establish `hHqv : ∀ k : ℕ, (D o o - D q q) ((D o q ^ k) T) = ((2 : ℚ) * k) • (D o q ^ k) T` using `fun k => by`. Rewrite using `[eig_pow _ _ 2 0 hHqXq T hHqT k]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hXqK : (D o q ^ (K + 1)) T = 0`. Apply `hB o ho q hq (2 * K + 2 : ℤ)` to reduce the goal to its premises. Rewrite using `[← LinearMap.sub_apply, hHqv]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Establish `hproj : ∀ (i : ℕ) (X Y : Module.End ℚ W) (x : W), (proj K i X Y) x = ∑ k ∈ Finset.range (K + 1), coef i k • (Y ^ k) ((X ^ k) x)`. Introduce `i X Y x`. Unfold `proj`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, Module.End.mul_apply]`.

Take `⟨T', hT'⟩ : ∃ x : W, x = (proj K (j + 1) (D o q) (D q o)) T` from `⟨_, rfl⟩`. Take `⟨U, hU⟩ : ∃ u : W, u = ∑ k ∈ Finset.range K, (((k : ℚ) + 1) * coef (j + 1) (k + 1)) • (D q o ^ k) ((D o q ^ (k + 1)) T)` from `⟨_, rfl⟩`. Establish `hZT' : D p q T' = D p o U`. Rewrite using `[hT', hproj, map_sum, Finset.sum_range_succ', hU, map_sum]`. Simplify using `only [map_smul, pow_zero, Module.End.one_apply, hpqT, smul_zero, add_zero]`.

Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[comm_pow_apply _ _ _ rZYq rYpYq, hZv, map_zero, zero_add, smul_smul, mul_comm]`. Establish `key : ∀ k : ℕ, coef (j + 1) k + coef (j + 1) (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + 2)) = -((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1))`. Introduce `k`. Use `coef_succ_mul (j + 1) k` as an intermediate fact.

Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `hXq_step : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) ((D o q ^ (k + 1)) T)) = (D q o ^ (k + 1)) ((D o q ^ (k + 1 + 1)) T) + (((k : ℚ) + 1) * ((k : ℚ) + 2)) • (D q o ^ k) ((D o q ^ (k + 1)) T)` using `fun k => by`. Rewrite using `[sl2_X_Ypow _ _ _ sXYq hHqYq _ _ (hHqv (k + 1)) k, ← pow_succ_apply' (D o q) (k + 1) T]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), coef (j + 1) k • D o q ((D q o ^ k) ((D o q ^ k) T)) = coef (j + 1) n • (D q o ^ n) ((D o q ^ (n + 1)) T) + ∑ k ∈ Finset.range n, (-((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1))) • (D q o ^ k) ((D o q ^ (k + 1)) T)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih, hXq_step n, Finset.sum_range_succ, ← key n]`. Use `module`. Establish `hXqT' : D o q T' = (-((j : ℚ) + 1)) • U`.

Rewrite using `[hT', hproj, map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[hS K, hXqK, map_zero, smul_zero, zero_add, hU, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Establish `hHpU : (D o o - D p p) U = (1 : ℚ) • U`. Rewrite using `[hU, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, eig_pow _ _ (-1) _ hHpYq _ (eig_pow _ _ 1 0 hHpXq T hHpT (k + 1)) k, smul_smul, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hXpU : (D o p ^ K) U = 0`. Apply `hB o ho p hp (2 * K + 1 : ℤ)` to reduce the goal to its premises. Rewrite using `[← LinearMap.sub_apply, eig_pow _ _ 2 1 hHpXp U hHpU K]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Establish `hP : (-D o q) * D o p = D o p * (-D o q)` using `by rw [neg_mul, mul_neg, rXqXp]`. Establish `hf : ∀ l : ℕ, D p q ((D p o ^ (l + 1)) ((D o p ^ (l + 1)) T')) = (D p o ^ (l + 1 + 1)) ((D o p ^ (l + 1)) U) + (((l : ℚ) + 1) * ((l : ℚ) + j + 2)) • (D p o ^ (l + 1)) ((D o p ^ l) U)`. Introduce `l`. Establish `e1` using `LinearMap.congr_fun (Commute.pow_right rZYp (l + 1)).eq ((D o p ^ (l + 1)) T')`. Simplify using `only [Module.End.mul_apply] at e1`.

Establish `c` using `LinearMap.congr_fun (Commute.pow_right rXqXp l).eq T'`. Simplify using `only [Module.End.mul_apply] at c`. Rewrite using `[e1, comm_pow_apply _ _ _ rZXp hP, hZT', LinearMap.neg_apply, c, hXqT', map_smul, neg_smul, neg_neg, sl2_Xpow_Y _ _ _ sXYp hHpXp U 1 hHpU l]`. Simplify using `only [map_add, map_smul]`. Rewrite using `[← pow_succ_apply2 (D p o) (l + 1)]`.

Use `push_cast`. Use `module`. Establish `hT5 : ∀ n : ℕ, D p q (∑ l ∈ Finset.range (n + 1), coef j l • (D p o ^ l) ((D o p ^ l) T')) = coef j n • (D p o ^ (n + 1)) ((D o p ^ n) U)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [hZT']`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, map_add, ih, map_smul, hf n, smul_add, smul_smul, coef_succ_mul, neg_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[← hT', hproj, hT5 K, hXpU, map_zero, smul_zero]`.
-/
theorem rankTwo : RankTwo := by
  intro W _ _ N K D hG hB o p q ho hp hq hop hoq hpq j T hoo hpp hqq hpqT
  have hpo := Ne.symm hop
  have hqo := Ne.symm hoq
  have hqp := Ne.symm hpq
  have rZXp : D p q * D o p - D o p * D p q = -D o q := by
    simpa [hqo] using hG p q o p hp hq ho hp
  have rZXq : D p q * D o q = D o q * D p q := by
    have := hG p q o q hp hq ho hq; simpa [hqo, hqp, sub_eq_zero] using this
  have rZYp : D p q * D p o = D p o * D p q := by
    have := hG p q p o hp hq hp ho; simpa [hqp, hop, sub_eq_zero] using this
  have rZYq : D p q * D q o - D q o * D p q = D p o := by
    simpa [hop] using hG p q q o hp hq hq ho
  have rXqXp : D o q * D o p = D o p * D o q := by
    have := hG o p o q ho hp ho hq
    exact (by simpa [hpo, hqo, sub_eq_zero] using this : D o p * D o q = D o q * D o p).symm
  have rYpYq : D p o * D q o = D q o * D p o := by
    have := hG p o q o hp ho hq ho; simpa [hoq, hop, sub_eq_zero] using this
  have sXYp : D o p * D p o - D p o * D o p = D o o - D p p := by simpa using hG o p p o ho hp hp ho
  have sXYq : D o q * D q o - D q o * D o q = D o o - D q q := by simpa using hG o q q o ho hq hq ho
  have hHpXp : (D o o - D p p) * D o p - D o p * (D o o - D p p) = (2 : ℚ) • D o p := by
    rw [comm_sub' _ _ _ (D o p) (-D o p) (by simpa [hpo] using hG o o o p ho ho ho hp)
      (by simpa [hpo] using hG p p o p hp hp ho hp), sub_neg_eq_add, two_smul]
  have hHqXq : (D o o - D q q) * D o q - D o q * (D o o - D q q) = (2 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) (-D o q) (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hqo] using hG q q o q hq hq ho hq), sub_neg_eq_add, two_smul]
  have hHqYq : (D o o - D q q) * D q o - D q o * (D o o - D q q) = (-2 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) (D q o) (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hoq] using hG q q q o hq hq hq ho), neg_smul, two_smul]; abel
  have hHpXq : (D o o - D p p) * D o q - D o q * (D o o - D p p) = (1 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) 0 (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hpo, hqp] using hG p p o q hp hp ho hq), sub_zero, one_smul]
  have hHpYq : (D o o - D p p) * D q o - D q o * (D o o - D p p) = (-1 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) 0 (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hpq, hop] using hG p p q o hp hp hq ho), sub_zero, neg_one_smul]
  have hHpT : (D o o - D p p) T = (0 : ℚ) • T := by simp [hoo, hpp]
  have hHqT : (D o o - D q q) T = (0 : ℚ) • T := by simp [hoo, hqq]
  have hZv : ∀ k : ℕ, D p q ((D o q ^ k) T) = 0 := fun k => by
    have c := LinearMap.congr_fun (Commute.pow_right rZXq k).eq T
    simp only [Module.End.mul_apply] at c
    rw [c, hpqT, map_zero]
  have hHqv : ∀ k : ℕ, (D o o - D q q) ((D o q ^ k) T) = ((2 : ℚ) * k) • (D o q ^ k) T := fun k => by
    rw [eig_pow _ _ 2 0 hHqXq T hHqT k]; congr 1; ring
  have hXqK : (D o q ^ (K + 1)) T = 0 := by
    apply hB o ho q hq (2 * K + 2 : ℤ)
    · rw [← LinearMap.sub_apply, hHqv]; congr 1; push_cast; ring
    · push_cast; omega
  have hproj : ∀ (i : ℕ) (X Y : Module.End ℚ W) (x : W),
      (proj K i X Y) x = ∑ k ∈ Finset.range (K + 1), coef i k • (Y ^ k) ((X ^ k) x) := by
    intro i X Y x; unfold proj; rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply, Module.End.mul_apply]
  obtain ⟨T', hT'⟩ : ∃ x : W, x = (proj K (j + 1) (D o q) (D q o)) T := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ u : W, u = ∑ k ∈ Finset.range K,
      (((k : ℚ) + 1) * coef (j + 1) (k + 1)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := ⟨_, rfl⟩

  have hZT' : D p q T' = D p o U := by
    rw [hT', hproj, map_sum, Finset.sum_range_succ', hU, map_sum]
    simp only [map_smul, pow_zero, Module.End.one_apply, hpqT, smul_zero, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [comm_pow_apply _ _ _ rZYq rYpYq, hZv, map_zero, zero_add, smul_smul, mul_comm]

  have key : ∀ k : ℕ, coef (j + 1) k + coef (j + 1) (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + 2)) =
      -((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1)) := by
    intro k; have := coef_succ_mul (j + 1) k; push_cast at this; linear_combination this
  have hXq_step : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) ((D o q ^ (k + 1)) T)) =
      (D q o ^ (k + 1)) ((D o q ^ (k + 1 + 1)) T) +
        (((k : ℚ) + 1) * ((k : ℚ) + 2)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := fun k => by
    rw [sl2_X_Ypow _ _ _ sXYq hHqYq _ _ (hHqv (k + 1)) k, ← pow_succ_apply' (D o q) (k + 1) T]
    congr 2; push_cast; ring
  have hS : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), coef (j + 1) k • D o q ((D q o ^ k) ((D o q ^ k) T)) =
      coef (j + 1) n • (D q o ^ n) ((D o q ^ (n + 1)) T) + ∑ k ∈ Finset.range n,
        (-((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1))) • (D q o ^ k) ((D o q ^ (k + 1)) T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hXq_step n, Finset.sum_range_succ, ← key n]
      module
  have hXqT' : D o q T' = (-((j : ℚ) + 1)) • U := by
    rw [hT', hproj, map_sum]
    simp only [map_smul]
    rw [hS K, hXqK, map_zero, smul_zero, zero_add, hU, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]

  have hHpU : (D o o - D p p) U = (1 : ℚ) • U := by
    rw [hU, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, eig_pow _ _ (-1) _ hHpYq _ (eig_pow _ _ 1 0 hHpXq T hHpT (k + 1)) k, smul_smul, smul_smul]
    congr 1; push_cast; ring
  have hXpU : (D o p ^ K) U = 0 := by
    apply hB o ho p hp (2 * K + 1 : ℤ)
    · rw [← LinearMap.sub_apply, eig_pow _ _ 2 1 hHpXp U hHpU K]; congr 1; push_cast; ring
    · push_cast; omega
  have hP : (-D o q) * D o p = D o p * (-D o q) := by rw [neg_mul, mul_neg, rXqXp]
  have hf : ∀ l : ℕ, D p q ((D p o ^ (l + 1)) ((D o p ^ (l + 1)) T')) =
      (D p o ^ (l + 1 + 1)) ((D o p ^ (l + 1)) U) +
        (((l : ℚ) + 1) * ((l : ℚ) + j + 2)) • (D p o ^ (l + 1)) ((D o p ^ l) U) := by
    intro l
    have e1 := LinearMap.congr_fun (Commute.pow_right rZYp (l + 1)).eq ((D o p ^ (l + 1)) T')
    simp only [Module.End.mul_apply] at e1
    have c := LinearMap.congr_fun (Commute.pow_right rXqXp l).eq T'
    simp only [Module.End.mul_apply] at c
    rw [e1, comm_pow_apply _ _ _ rZXp hP, hZT', LinearMap.neg_apply, c, hXqT', map_smul, neg_smul, neg_neg,
      sl2_Xpow_Y _ _ _ sXYp hHpXp U 1 hHpU l]
    simp only [map_add, map_smul]
    rw [← pow_succ_apply2 (D p o) (l + 1)]
    push_cast
    module
  have hT5 : ∀ n : ℕ, D p q (∑ l ∈ Finset.range (n + 1), coef j l • (D p o ^ l) ((D o p ^ l) T')) =
      coef j n • (D p o ^ (n + 1)) ((D o p ^ n) U) := by
    intro n
    induction n with
    | zero => simp [hZT']
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, map_smul, hf n, smul_add, smul_smul, coef_succ_mul, neg_smul]
      abel
  rw [← hT', hproj, hT5 K, hXpU, map_zero, smul_zero]

end GlobalTheory.LeviCut.RankTwoProof
