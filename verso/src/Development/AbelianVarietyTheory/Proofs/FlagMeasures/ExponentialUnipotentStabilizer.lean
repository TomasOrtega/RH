import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

namespace GlobalTheory.LoopV.ExpGroup

variable {K : Type} [Field K] {N : ℕ}

def fil (K : Type) [Field K] (N n : ℕ) : Submodule K (Matrix (Fin N) (Fin N) K) where
  carrier := {x | ∀ i j : Fin N, (j : ℕ) < i + n → x i j = 0}
  add_mem' := fun {a b} ha hb i j h => by simp [ha i j h, hb i j h]
  zero_mem' := fun i j _ => rfl
  smul_mem' := fun c a ha i j h => by simp [ha i j h]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `Nat.lt_or_ge (k : ℕ) (i + n) with hk | hk` into its components or cases. Rewrite using `[hx i k hk, zero_mul]`.

Rewrite using `[hy k j (by omega), mul_zero]`.
-/
theorem fil_mul {n m : ℕ} {x y : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N n)
    (hy : y ∈ fil K N m) : x * y ∈ fil K N (n + m) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases Nat.lt_or_ge (k : ℕ) (i + n) with hk | hk
  · rw [hx i k hk, zero_mul]
  · rw [hy k j (by omega), mul_zero]

/- English proof (translation)
Introduce `i j hij`. Conclude with `hx i j (by omega)`.
-/
theorem fil_mono {n m : ℕ} (h : n ≤ m) {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N m) :
    x ∈ fil K N n := by
  intro i j hij
  exact hx i j (by omega)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.zero_apply]`. Conclude with `hx i j (by have := j.isLt; omega)`.
-/
theorem eq_zero_of_fil {n : ℕ} (h : N ≤ n) {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N n) :
    x = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact hx i j (by have := j.isLt; omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Conclude with `h i j (Fin.le_iff_val_le_val.mpr (by omega))`. Introduce `h i j hij`. Conclude with `h i j (by have := Fin.le_iff_val_le_val.mp hij; omega)`.
-/
theorem strUp_iff {x : Matrix (Fin N) (Fin N) K} : StrUp x ↔ x ∈ fil K N 1 := by
  constructor
  · intro h i j hij
    exact h i j (Fin.le_iff_val_le_val.mpr (by omega))
  · intro h i j hij
    exact h i j (by have := Fin.le_iff_val_le_val.mp hij; omega)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `fil_mul ih hx`.
-/
theorem fil_pow {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N 1) (k : ℕ) :
    x ^ (k + 1) ∈ fil K N (k + 1) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ]
    exact fil_mul ih hx

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero`. Take `rfl : N = 0` from `by omega`. Use extensionality with `i j`. Conclude with `i.elim0`.

Consider the case `succ k => exact eq_zero_of_fil hk (fil_pow hx k)`.
-/
theorem pow_eq_zero {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N 1) {k : ℕ} (hk : N ≤ k) :
    x ^ k = 0 := by
  cases k with
  | zero =>
    obtain rfl : N = 0 := by omega
    ext i j
    exact i.elim0
  | succ k => exact eq_zero_of_fil hk (fil_pow hx k)

/- English proof (translation)
Establish `h0 : ∀ i, N ≤ i → ((i.factorial : K))⁻¹ • x ^ i = 0` using `fun i hi => by`. Rewrite using `[pow_eq_zero hx hi, smul_zero]`. Establish `e : ∑ i ∈ Finset.range (N + 2), ((i.factorial : K))⁻¹ • x ^ i = ∑ i ∈ Finset.range N, ((i.factorial : K))⁻¹ • x ^ i`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, h0 N le_rfl, h0 (N + 1) (Nat.le_succ N), add_zero, add_zero]`. Use `show _ = 1 + x + ∑ k ∈ Finset.range N, (((k + 1 + 1).factorial : K))⁻¹ • x ^ (k + 1 + 1)`.

Rewrite using `[expT, ← e, Finset.sum_range_succ', Finset.sum_range_succ']`. Simplify using `only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero, zero_add, pow_one]`. Normalize the expressions using the abelian group laws.
-/
theorem expT_eq {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N 1) :
    expT x = 1 + x + ∑ k ∈ Finset.range N, (((k + 2).factorial : K))⁻¹ • x ^ (k + 2) := by
  have h0 : ∀ i, N ≤ i → ((i.factorial : K))⁻¹ • x ^ i = 0 := fun i hi => by
    rw [pow_eq_zero hx hi, smul_zero]
  have e : ∑ i ∈ Finset.range (N + 2), ((i.factorial : K))⁻¹ • x ^ i
      = ∑ i ∈ Finset.range N, ((i.factorial : K))⁻¹ • x ^ i := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, h0 N le_rfl, h0 (N + 1) (Nat.le_succ N),
      add_zero, add_zero]
  show _ = 1 + x + ∑ k ∈ Finset.range N, (((k + 1 + 1).factorial : K))⁻¹ • x ^ (k + 1 + 1)
  rw [expT, ← e, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero,
    zero_add, pow_one]
  abel

/- English proof (translation)
Rewrite using `[IsNilpotent.exp_eq_sum (pow_eq_zero hx le_rfl), expT]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Rat.cast_smul_eq_qsmul K]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem expT_eq_exp_of_mem_fil_one [CharZero K] {x : Matrix (Fin N) (Fin N) K}
    (hx : x ∈ fil K N 1) : expT x = IsNilpotent.exp x := by
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero hx le_rfl), expT]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Rat.cast_smul_eq_qsmul K]
  push_cast
  rfl

/- English proof (translation)
Establish `hn : -x ∈ fil K N 1` using `neg_mem hx`. Rewrite using `[expT_eq_exp_of_mem_fil_one hx, expT_eq_exp_of_mem_fil_one hn]`. Conclude with `IsNilpotent.exp_mul_exp_neg_self ⟨N, pow_eq_zero hx le_rfl⟩`.
-/
theorem expT_mul_neg [CharZero K] {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ fil K N 1) :
    expT x * expT (-x) = 1 := by
  have hn : -x ∈ fil K N 1 := neg_mem hx
  rw [expT_eq_exp_of_mem_fil_one hx, expT_eq_exp_of_mem_fil_one hn]
  exact IsNilpotent.exp_mul_exp_neg_self ⟨N, pow_eq_zero hx le_rfl⟩

/- English proof (translation)
Establish `hd1 : d ∈ fil K N 1` using `fil_mono (by omega) hd`. Establish `hzd : z + d ∈ fil K N 1` using `add_mem hz hd1`. Establish `key : ∀ k : ℕ, (z + d) ^ (k + 1) - z ^ (k + 1) ∈ fil K N (n + 1 + k)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hd`. Consider the case `succ k ih`. Establish `e : (z + d) ^ (k + 1 + 1) - z ^ (k + 1 + 1) = ((z + d) ^ (k + 1) - z ^ (k + 1)) * (z + d) + z ^ (k + 1) * d`. Rewrite using `[pow_succ (z + d) (k + 1), pow_succ z (k + 1)]`. Use `noncomm_ring`.

Rewrite using `[e]`. Conclude with `add_mem (fil_mono (by omega) (fil_mul ih hzd)) (fil_mono (by omega) (fil_mul (fil_pow hz k) hd))`. Establish `e2 : expT (z + d) - expT z - d = ∑ k ∈ Finset.range N, ((k + 2).factorial : K)⁻¹ • ((z + d) ^ (k + 2) - z ^ (k + 2))`. Rewrite using `[expT_eq hzd, expT_eq hz]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (fil_mono (by omega) (key (k + 1)))`.
-/
theorem expT_add_sub {n : ℕ} {z d : Matrix (Fin N) (Fin N) K} (hz : z ∈ fil K N 1)
    (hd : d ∈ fil K N (n + 1)) : expT (z + d) - expT z - d ∈ fil K N (n + 2) := by
  have hd1 : d ∈ fil K N 1 := fil_mono (by omega) hd
  have hzd : z + d ∈ fil K N 1 := add_mem hz hd1
  have key : ∀ k : ℕ, (z + d) ^ (k + 1) - z ^ (k + 1) ∈ fil K N (n + 1 + k) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      have e : (z + d) ^ (k + 1 + 1) - z ^ (k + 1 + 1)
          = ((z + d) ^ (k + 1) - z ^ (k + 1)) * (z + d) + z ^ (k + 1) * d := by
        rw [pow_succ (z + d) (k + 1), pow_succ z (k + 1)]
        noncomm_ring
      rw [e]
      exact add_mem (fil_mono (by omega) (fil_mul ih hzd)) (fil_mono (by omega) (fil_mul (fil_pow hz k) hd))
  have e2 : expT (z + d) - expT z - d = ∑ k ∈ Finset.range N,
      ((k + 2).factorial : K)⁻¹ • ((z + d) ^ (k + 2) - z ^ (k + 2)) := by
    rw [expT_eq hzd, expT_eq hz]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [e2]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (fil_mono (by omega) (key (k + 1)))

def lieSub (Z : Matrix (Fin N) (Fin N) K) : Submodule K (Matrix (Fin N) (Fin N) K) where
  carrier := lieU Z
  add_mem' := fun {a b} ha hb => ⟨fun i j h => by simp [ha.1 i j h, hb.1 i j h],
    fun i j h => by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, ha.2 i j h, hb.2 i j h, add_zero]⟩
  zero_mem' := ⟨fun i j _ => rfl, fun i j _ => by simp⟩
  smul_mem' := fun c a ha => ⟨fun i j h => by simp [ha.1 i j h],
    fun i j h => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, ha.2 i j h, smul_zero]⟩

/- English proof (translation)
Establish `hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate)` using `hx`. Establish `hy' : StrUp y ∧ StrLo (Z * y * Z.adjugate)` using `hy`. Use `show StrUp (x * y) ∧ StrLo (Z * (x * y) * Z.adjugate)`. Prove the components needed by the constructor for the conclusion. Conclude with `strUp_iff.mpr (fil_mono (by omega) (fil_mul (strUp_iff.mp hx'.1) (strUp_iff.mp hy'.1)))`.

Establish `key : (Z * x * Z.adjugate) * (Z * y * Z.adjugate) = Z.det • (Z * (x * y) * Z.adjugate)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul]`. Simplify using `only [Matrix.mul_assoc]`. Introduce `i j hij`.

Establish `h1` using `congrFun (congrFun key i) j`. Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]`. Establish `h2 : ∑ k, (Z * x * Z.adjugate) i k * (Z * y * Z.adjugate) k j = 0` using `Finset.sum_eq_zero fun k _ => by`. Break down `le_or_gt i k with hk | hk` into its components or cases. Rewrite using `[hx'.2 i k hk, zero_mul]`.

Rewrite using `[hy'.2 k j (hk.le.trans hij), mul_zero]`. Rewrite `h1` using `[h2]`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_left hZ`.
-/
theorem lie_mul {Z x y : Matrix (Fin N) (Fin N) K} (hZ : Z.det ≠ 0) (hx : x ∈ lieSub Z)
    (hy : y ∈ lieSub Z) : x * y ∈ lieSub Z := by
  have hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate) := hx
  have hy' : StrUp y ∧ StrLo (Z * y * Z.adjugate) := hy
  show StrUp (x * y) ∧ StrLo (Z * (x * y) * Z.adjugate)
  constructor
  · exact strUp_iff.mpr (fil_mono (by omega) (fil_mul (strUp_iff.mp hx'.1) (strUp_iff.mp hy'.1)))
  · have key : (Z * x * Z.adjugate) * (Z * y * Z.adjugate) = Z.det • (Z * (x * y) * Z.adjugate) := by
      calc (Z * x * Z.adjugate) * (Z * y * Z.adjugate)
          = Z * x * (Z.adjugate * Z) * y * Z.adjugate := by simp only [Matrix.mul_assoc]
        _ = Z.det • (Z * (x * y) * Z.adjugate) := by
          rw [Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
    intro i j hij
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h1
    have h2 : ∑ k, (Z * x * Z.adjugate) i k * (Z * y * Z.adjugate) k j = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rcases le_or_gt i k with hk | hk
        · rw [hx'.2 i k hk, zero_mul]
        · rw [hy'.2 k j (hk.le.trans hij), mul_zero]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hZ

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `lie_mul hZ ih hx`.
-/
theorem lie_pow {Z x : Matrix (Fin N) (Fin N) K} (hZ : Z.det ≠ 0) (hx : x ∈ lieSub Z) (k : ℕ) :
    x ^ (k + 1) ∈ lieSub Z := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ]
    exact lie_mul hZ ih hx

/- English proof (translation)
Establish `hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate)` using `hx`. Establish `hx1 : x ∈ fil K N 1` using `strUp_iff.mp hx'.1`. Rewrite using `[expT_eq hx1, show ∀ p q r : Matrix (Fin N) (Fin N) K, p + q + r - p = q + r from fun p q r => by abel]`. Conclude with `add_mem hx (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lie_pow hZ hx (k + 1)))`.
-/
theorem lie_expT {Z x : Matrix (Fin N) (Fin N) K} (hZ : Z.det ≠ 0) (hx : x ∈ lieSub Z) :
    expT x - 1 ∈ lieSub Z := by
  have hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate) := hx
  have hx1 : x ∈ fil K N 1 := strUp_iff.mp hx'.1
  rw [expT_eq hx1, show ∀ p q r : Matrix (Fin N) (Fin N) K, p + q + r - p = q + r from
    fun p q r => by abel]
  exact add_mem hx (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lie_pow hZ hx (k + 1)))

variable [NumberField K]

def ent (K : Type) [Field K] [NumberField K] (N : ℕ) (J : Ideal (𝓞 K)) :
    AddSubgroup (Matrix (Fin N) (Fin N) K) where
  carrier := {x | EntIn J x}
  add_mem' := fun {a b} ha hb i j => by
    obtain ⟨o, ho, e⟩ := ha i j
    obtain ⟨o', ho', e'⟩ := hb i j
    exact ⟨o + o', add_mem ho ho', by simp [← e, ← e']⟩
  zero_mem' := fun i j => ⟨0, zero_mem _, by simp⟩
  neg_mem' := fun {a} ha i j => by
    obtain ⟨o, ho, e⟩ := ha i j
    exact ⟨-o, neg_mem ho, by simp [← e]⟩

/- English proof (translation)
Establish `hx' : ∀ i j, ∃ o ∈ J, ((o : 𝓞 K) : K) = x i j` using `hx`. Establish `hy' : ∀ i j, ∃ o ∈ J', ((o : 𝓞 K) : K) = y i j` using `hy`. Use `choose a ha ea using hx'`. Use `choose b hb eb using hy'`. Use `show ∀ i j, ∃ o ∈ J, ((o : 𝓞 K) : K) = (x * y) i j`.

Introduce `i j`. Use `⟨∑ k, a i k * b k j, Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha i k), ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, ← ea, ← eb]`.
-/
theorem ent_mul {J J' : Ideal (𝓞 K)} {x y : Matrix (Fin N) (Fin N) K} (hx : x ∈ ent K N J)
    (hy : y ∈ ent K N J') : x * y ∈ ent K N J := by
  have hx' : ∀ i j, ∃ o ∈ J, ((o : 𝓞 K) : K) = x i j := hx
  have hy' : ∀ i j, ∃ o ∈ J', ((o : 𝓞 K) : K) = y i j := hy
  choose a ha ea using hx'
  choose b hb eb using hy'
  show ∀ i j, ∃ o ∈ J, ((o : 𝓞 K) : K) = (x * y) i j
  intro i j
  refine ⟨∑ k, a i k * b k j, Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha i k), ?_⟩
  simp [Matrix.mul_apply, ← ea, ← eb]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `ent_mul ih hx`.
-/
theorem ent_pow {J : Ideal (𝓞 K)} {x : Matrix (Fin N) (Fin N) K} (hx : x ∈ ent K N J) (k : ℕ) :
    x ^ (k + 1) ∈ ent K N J := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ]
    exact ent_mul ih hx

/- English proof (translation)
Establish `hx' : ∀ i j, ∃ o ∈ Ideal.span {(c : 𝓞 K)} * I, ((o : 𝓞 K) : K) = x i j` using `hx`. Use `choose o ho eo using hx'`. Establish `h2 : ∀ i j, ∃ w ∈ I, (c : 𝓞 K) * w = o i j` using `fun i j => Ideal.mem_span_singleton_mul.mp (ho i j)`. Use `choose w hw ew using h2`. Use `⟨fun i j => ((w i j : 𝓞 K) : K), ?_, ?_⟩` and prove the remaining obligations.

Use `show ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = ((w i j : 𝓞 K) : K)`. Conclude with `fun i j => ⟨w i j, hw i j, rfl⟩`. Use extensionality with `i j show x i j = c • ((w i j : 𝓞 K) : K)`. Rewrite using `[nsmul_eq_mul, ← eo, ← ew]`. Simplify using the standard rewrite rules.
-/
theorem ent_div {I : Ideal (𝓞 K)} {c : ℕ} {x : Matrix (Fin N) (Fin N) K}
    (hx : x ∈ ent K N (Ideal.span {(c : 𝓞 K)} * I)) : ∃ x' ∈ ent K N I, x = c • x' := by
  have hx' : ∀ i j, ∃ o ∈ Ideal.span {(c : 𝓞 K)} * I, ((o : 𝓞 K) : K) = x i j := hx
  choose o ho eo using hx'
  have h2 : ∀ i j, ∃ w ∈ I, (c : 𝓞 K) * w = o i j := fun i j =>
    Ideal.mem_span_singleton_mul.mp (ho i j)
  choose w hw ew using h2
  refine ⟨fun i j => ((w i j : 𝓞 K) : K), ?_, ?_⟩
  · show ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = ((w i j : 𝓞 K) : K)
    exact fun i j => ⟨w i j, hw i j, rfl⟩
  · ext i j
    show x i j = c • ((w i j : 𝓞 K) : K)
    rw [nsmul_eq_mul, ← eo, ← ew]
    simp

/- English proof (translation)
Take `⟨a, ha, hxa⟩` from `ent_div hx`. Rewrite using `[expT_eq hu, show ∀ p q r : Matrix (Fin N) (Fin N) K, p + q + r - p = q + r from fun p q r => by abel]`. Use `add_mem hx (AddSubgroup.sum_mem _ fun k _ => ?_)` and prove the remaining obligations. Break down `Nat.lt_or_ge (k + 2) N with hk | hk` into its components or cases. Take `⟨m, hm⟩` from `Nat.factorial_dvd_factorial hk.le`.

Establish `hp : a ^ (k + 1 + 1) ∈ ent K N I` using `ent_pow ha (k + 1)`. Establish `hp' : ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = (a ^ (k + 2)) i j` using `hp`. Use `show ∀ i j, ∃ o ∈ Ideal.span {(N.factorial : 𝓞 K)} * I, ((o : 𝓞 K) : K) = (((k + 2).factorial : K)⁻¹ • x ^ (k + 2)) i j`. Introduce `i j`. Take `⟨b, hb, eb⟩` from `hp' i j`.

Use `⟨(N.factorial : 𝓞 K) * ((m : 𝓞 K) * (N.factorial : 𝓞 K) ^ k * b), Ideal.mem_span_singleton_mul.mpr ⟨_, I.mul_mem_left _ hb, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hf : ((k + 2).factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Establish `hxa' : x = (N.factorial : K) • a`. Use extensionality with `i' j'`. Rewrite using `[hxa]`.

Use `show N.factorial • a i' j' = (N.factorial : K) * a i' j'`. Rewrite using `[nsmul_eq_mul]`. Rewrite using `[hxa', smul_pow]`. Use `show _ = ((k + 2).factorial : K)⁻¹ * ((N.factorial : K) ^ (k + 2) * (a ^ (k + 2)) i j)`. Rewrite using `[← eb, hm]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[pow_eq_zero hu hk, smul_zero]`. Conclude with `zero_mem _`.
-/
theorem ent_expT {I : Ideal (𝓞 K)} {x : Matrix (Fin N) (Fin N) K} (hu : x ∈ fil K N 1)
    (hx : x ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I)) :
    expT x - 1 ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) := by
  obtain ⟨a, ha, hxa⟩ := ent_div hx
  rw [expT_eq hu, show ∀ p q r : Matrix (Fin N) (Fin N) K, p + q + r - p = q + r from
    fun p q r => by abel]
  refine add_mem hx (AddSubgroup.sum_mem _ fun k _ => ?_)
  rcases Nat.lt_or_ge (k + 2) N with hk | hk
  · obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk.le
    have hp : a ^ (k + 1 + 1) ∈ ent K N I := ent_pow ha (k + 1)
    have hp' : ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = (a ^ (k + 2)) i j := hp
    show ∀ i j, ∃ o ∈ Ideal.span {(N.factorial : 𝓞 K)} * I,
      ((o : 𝓞 K) : K) = (((k + 2).factorial : K)⁻¹ • x ^ (k + 2)) i j
    intro i j
    obtain ⟨b, hb, eb⟩ := hp' i j
    refine ⟨(N.factorial : 𝓞 K) * ((m : 𝓞 K) * (N.factorial : 𝓞 K) ^ k * b),
      Ideal.mem_span_singleton_mul.mpr ⟨_, I.mul_mem_left _ hb, rfl⟩, ?_⟩
    have hf : ((k + 2).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hxa' : x = (N.factorial : K) • a := by
      ext i' j'
      rw [hxa]
      show N.factorial • a i' j' = (N.factorial : K) * a i' j'
      rw [nsmul_eq_mul]
    rw [hxa', smul_pow]
    show _ = ((k + 2).factorial : K)⁻¹ * ((N.factorial : K) ^ (k + 2) * (a ^ (k + 2)) i j)
    rw [← eb, hm]
    push_cast
    field_simp
    ring
  · rw [pow_eq_zero hu hk, smul_zero]
    exact zero_mem _

/- English proof (translation)
Establish `hu0 : StrUp u ∧ StrLo (Z * u * Z.adjugate)` using `hu`. Establish `hu1 : u ∈ fil K N 1` using `strUp_iff.mp hu0.1`. Establish `step : ∀ n : ℕ, ∃ z ∈ lieSub Z, z ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) ∧ z ∈ fil K N 1 ∧ 1 + u - expT z ∈ fil K N (n + 1)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Use `⟨0, zero_mem _, zero_mem _, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[expT_eq (zero_mem _)]`. Simplify using `using hu1`. Consider the case `succ n ih`.

Take `⟨z, hzl, hze, hzf, hd⟩` from `ih`. Establish `e : 1 + u - expT z = u - (expT z - 1)` using `by abel`. Use `⟨z + (1 + u - expT z), add_mem hzl ?_, add_mem hze ?_, add_mem hzf (fil_mono (by omega) hd), ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `sub_mem hu (lie_expT hZ hzl)`.

Rewrite using `[e]`. Conclude with `sub_mem hu' (ent_expT hzf hze)`. Establish `h` using `expT_add_sub hzf hd`. Establish `e2 : 1 + u - expT (z + (1 + u - expT z)) = -(expT (z + (1 + u - expT z)) - expT z - (1 + u - expT z))` using `by abel`. Rewrite using `[e2]`.

Conclude with `neg_mem h`. Take `⟨z, hzl, hze, -, hz⟩` from `step N`. Conclude with `⟨z, hzl, hze, sub_eq_zero.mp (eq_zero_of_fil (by omega) hz)⟩`.
-/
theorem exists_expT {I : Ideal (𝓞 K)} {Z u : Matrix (Fin N) (Fin N) K} (hZ : Z.det ≠ 0)
    (hu : u ∈ lieSub Z) (hu' : u ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I)) :
    ∃ z ∈ lieSub Z, z ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) ∧ 1 + u = expT z := by
  have hu0 : StrUp u ∧ StrLo (Z * u * Z.adjugate) := hu
  have hu1 : u ∈ fil K N 1 := strUp_iff.mp hu0.1
  have step : ∀ n : ℕ, ∃ z ∈ lieSub Z, z ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) ∧
      z ∈ fil K N 1 ∧ 1 + u - expT z ∈ fil K N (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, zero_mem _, zero_mem _, zero_mem _, ?_⟩
      rw [expT_eq (zero_mem _)]
      simpa using hu1
    | succ n ih =>
      obtain ⟨z, hzl, hze, hzf, hd⟩ := ih
      have e : 1 + u - expT z = u - (expT z - 1) := by abel
      refine ⟨z + (1 + u - expT z), add_mem hzl ?_, add_mem hze ?_,
        add_mem hzf (fil_mono (by omega) hd), ?_⟩
      · rw [e]
        exact sub_mem hu (lie_expT hZ hzl)
      · rw [e]
        exact sub_mem hu' (ent_expT hzf hze)
      · have h := expT_add_sub hzf hd
        have e2 : 1 + u - expT (z + (1 + u - expT z))
            = -(expT (z + (1 + u - expT z)) - expT z - (1 + u - expT z)) := by abel
        rw [e2]
        exact neg_mem h
  obtain ⟨z, hzl, hze, -, hz⟩ := step N
  exact ⟨z, hzl, hze, sub_eq_zero.mp (eq_zero_of_fil (by omega) hz)⟩

omit [NumberField K] in
/- English proof (translation)
Establish `hu' : StrUp u ∧ StrLo (Z * u * Z.adjugate)` using `hu`. Establish `hZu : IsUnit Z.det` using `isUnit_iff_ne_zero.mpr hZ`. Establish `e : Z * (1 + u) * Z⁻¹ = 1 + (Z.det)⁻¹ • (Z * u * Z.adjugate)`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hZu, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]`. Use `show IsUpUni (1 + u) ∧ IsLoUni (Z * (1 + u) * Z⁻¹)`.

Prove the components needed by the constructor for the conclusion. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne h.ne', hu'.1 i j h.le, add_zero]`.

Introduce and unpack `rfl`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, hu'.1 i i le_rfl, add_zero]`. Rewrite using `[e]`. Introduce `i j`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, hu'.2 i j h.le, smul_zero, Matrix.one_apply_ne h.ne, add_zero]`. Introduce and unpack `rfl`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, hu'.2 i i le_rfl, smul_zero, Matrix.one_apply_eq, add_zero]`.
-/
theorem one_add_mem_stabU {Z u : Matrix (Fin N) (Fin N) K} (hZ : Z.det ≠ 0) (hu : u ∈ lieSub Z) :
    1 + u ∈ stabU Z := by
  have hu' : StrUp u ∧ StrLo (Z * u * Z.adjugate) := hu
  have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  have e : Z * (1 + u) * Z⁻¹ = 1 + (Z.det)⁻¹ • (Z * u * Z.adjugate) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hZu,
      Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]
  show IsUpUni (1 + u) ∧ IsLoUni (Z * (1 + u) * Z⁻¹)
  constructor
  · intro i j
    constructor
    · intro h
      rw [Matrix.add_apply, Matrix.one_apply_ne h.ne', hu'.1 i j h.le, add_zero]
    · rintro rfl
      rw [Matrix.add_apply, Matrix.one_apply_eq, hu'.1 i i le_rfl, add_zero]
  · rw [e]
    intro i j
    constructor
    · intro h
      rw [Matrix.add_apply, Matrix.smul_apply, hu'.2 i j h.le, smul_zero, Matrix.one_apply_ne h.ne,
        add_zero]
    · rintro rfl
      rw [Matrix.add_apply, Matrix.smul_apply, hu'.2 i i le_rfl, smul_zero, Matrix.one_apply_eq,
        add_zero]

/- English proof (translation)
Introduce `K _ _ N Z I hZ`. Use `⟨fun x hx hxe => ?_, fun x hx y hy hxe hye => ?_⟩` and prove the remaining obligations. Establish `hxl : x ∈ lieSub Z` using `hx`. Establish `hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate)` using `hx`. Establish `hxe' : x ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I)` using `hxe`.

Establish `hx1 : x ∈ fil K N 1` using `strUp_iff.mp hx'.1`. Use `⟨?_, ?_, expT_mul_neg hx1⟩` and prove the remaining obligations. Establish `h` using `one_add_mem_stabU hZ (lie_expT hZ hxl)`. Rewrite `h` using `[show 1 + (expT x - 1) = expT x by abel]`. Then use the resulting hypothesis. Establish `h : ∀ i j, ∃ o ∈ Ideal.span {(N.factorial : 𝓞 K)} * I, ((o : 𝓞 K) : K) = (expT x - 1) i j` using `ent_expT hx1 hxe'`.

Introduce `i j`. Take `⟨o, ho, e⟩` from `h i j`. Establish `hle : Ideal.span {(N.factorial : 𝓞 K)} * I ≤ I` using `Ideal.mul_le_right`. Conclude with `⟨o, hle ho, e⟩`. Establish `hxl : x ∈ lieSub Z` using `hx`.

Establish `hyl : y ∈ lieSub Z` using `hy`. Establish `hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate)` using `hx`. Establish `hy' : StrUp y ∧ StrLo (Z * y * Z.adjugate)` using `hy`. Establish `hxe' : x ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I)` using `hxe`. Establish `hye' : y ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I)` using `hye`.

Establish `hx1 : x ∈ fil K N 1` using `strUp_iff.mp hx'.1`. Establish `hy1 : y ∈ fil K N 1` using `strUp_iff.mp hy'.1`. Establish `ex` using `lie_expT hZ hxl`. Establish `ey` using `lie_expT hZ hyl`. Establish `fx` using `ent_expT hx1 hxe'`.

Establish `fy` using `ent_expT hy1 hye'`. Establish `e : expT x * expT y = 1 + ((expT x - 1) + (expT y - 1) + (expT x - 1) * (expT y - 1))` using `by noncomm_ring`. Take `⟨z, hzl, hze, hz⟩` from `exists_expT hZ (add_mem (add_mem ex ey) (lie_mul hZ ex ey)) (add_mem (add_mem fx fy) (ent_mul fx fy))`. Conclude with `⟨z, hzl, hze, e.trans hz⟩`.
-/
theorem exp_group : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (Z : Matrix (Fin N) (Fin N) K) (I : Ideal (𝓞 K)), Z.det ≠ 0 → (∀ x ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → expT x ∈ stabU Z ∧ EntIn I (expT x - 1) ∧ expT x * expT (-x) = 1) ∧ ∀ x ∈ lieU Z, ∀ y ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) y → ∃ z ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) z ∧ expT x * expT y = expT z := by
  intro K _ _ N Z I hZ
  refine ⟨fun x hx hxe => ?_, fun x hx y hy hxe hye => ?_⟩
  · have hxl : x ∈ lieSub Z := hx
    have hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate) := hx
    have hxe' : x ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) := hxe
    have hx1 : x ∈ fil K N 1 := strUp_iff.mp hx'.1
    refine ⟨?_, ?_, expT_mul_neg hx1⟩
    · have h := one_add_mem_stabU hZ (lie_expT hZ hxl)
      rwa [show 1 + (expT x - 1) = expT x by abel] at h
    · have h : ∀ i j, ∃ o ∈ Ideal.span {(N.factorial : 𝓞 K)} * I,
          ((o : 𝓞 K) : K) = (expT x - 1) i j := ent_expT hx1 hxe'
      intro i j
      obtain ⟨o, ho, e⟩ := h i j
      have hle : Ideal.span {(N.factorial : 𝓞 K)} * I ≤ I := Ideal.mul_le_right
      exact ⟨o, hle ho, e⟩
  · have hxl : x ∈ lieSub Z := hx
    have hyl : y ∈ lieSub Z := hy
    have hx' : StrUp x ∧ StrLo (Z * x * Z.adjugate) := hx
    have hy' : StrUp y ∧ StrLo (Z * y * Z.adjugate) := hy
    have hxe' : x ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) := hxe
    have hye' : y ∈ ent K N (Ideal.span {(N.factorial : 𝓞 K)} * I) := hye
    have hx1 : x ∈ fil K N 1 := strUp_iff.mp hx'.1
    have hy1 : y ∈ fil K N 1 := strUp_iff.mp hy'.1
    have ex := lie_expT hZ hxl
    have ey := lie_expT hZ hyl
    have fx := ent_expT hx1 hxe'
    have fy := ent_expT hy1 hye'
    have e : expT x * expT y
        = 1 + ((expT x - 1) + (expT y - 1) + (expT x - 1) * (expT y - 1)) := by noncomm_ring
    obtain ⟨z, hzl, hze, hz⟩ := exists_expT hZ (add_mem (add_mem ex ey) (lie_mul hZ ex ey))
      (add_mem (add_mem fx fy) (ent_mul fx fy))
    exact ⟨z, hzl, hze, e.trans hz⟩

end GlobalTheory.LoopV.ExpGroup
