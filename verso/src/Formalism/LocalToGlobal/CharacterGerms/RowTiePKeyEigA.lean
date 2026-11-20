import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj

section Lim

variable {C : Type} [Field C] {V : VF C} {n : ℕ}

def MT (V : VF C) (A : ℕ → Matrix (Fin n) (Fin n) C) (B : Matrix (Fin n) (Fin n) C) : Prop :=
  ∀ i j, Tends V (fun k => A k i j) (B i j)

def IntM (V : VF C) (A : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, V.Ge 0 (A i j)

/- English proof (translation)
Introduce `w` and use `⟨0, fun n _ => by show ((w : ℝ) : WithTop ℝ) ≤ V.v (x - x) rw [sub_self, AddValuation.map_zero] exact le_top⟩`.
-/
private theorem tends_const' (x : C) : Tends V (fun _ => x) x := fun w => ⟨0, fun n _ => by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (x - x)
  rw [sub_self, AddValuation.map_zero]
  exact le_top⟩

/- English proof (translation)
Introduce `i j` and use `tends_const' _`.
-/
theorem MT.const (B : Matrix (Fin n) (Fin n) C) : MT V (fun _ => B) B :=
  fun i j => tends_const' _

variable {A A' : ℕ → Matrix (Fin n) (Fin n) C} {B B' : Matrix (Fin n) (Fin n) C}

/- English proof (translation)
Introduce `i j` and use `(h i j).add (h' i j)`.
-/
theorem MT.add (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k + A' k) (B + B') :=
  fun i j => (h i j).add (h' i j)

/- English proof (translation)
Introduce `i j` and use `(h i j).sub (h' i j)`.
-/
theorem MT.sub (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k - A' k) (B - B') :=
  fun i j => (h i j).sub (h' i j)

/- English proof (translation)
Introduce `i j` and use `(tends_const' c).mul (h i j)`.
-/
theorem MT.smul (c : C) (h : MT V A B) : MT V (fun k => c • A k) (c • B) :=
  fun i j => (tends_const' c).mul (h i j)

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.mul_apply]`. Conclude with `Tends.sum Finset.univ (fun l _ => (h i l).mul (h' l j))`.
-/
theorem MT.mul (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k * A' k) (B * B') := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Tends.sum Finset.univ (fun l _ => (h i l).mul (h' l j))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using MT.const (V := V) (1 : Matrix (Fin n) (Fin n) C)`. Consider the case `succ m ih => simpa only [pow_succ] using ih.mul h`.
-/
theorem MT.pow (h : MT V A B) (m : ℕ) : MT V (fun k => A k ^ m) (B ^ m) := by
  induction m with
  | zero => simpa using MT.const (V := V) (1 : Matrix (Fin n) (Fin n) C)
  | succ m ih => simpa only [pow_succ] using ih.mul h

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => (h i j).unique (h' i j)`.
-/
theorem MT.unique (h : MT V A B) (h' : MT V A B') : B = B' :=
  Matrix.ext fun i j => (h i j).unique (h' i j)

/- English proof (translation)
Introduce `i j w`. Take `⟨n0, hn0⟩` from `h i j w`. Conclude with `⟨n0, fun m hm => hn0 (m + 1) (by omega)⟩`.
-/
theorem MT.shift (h : MT V A B) : MT V (fun k => A (k + 1)) B := by
  intro i j w
  obtain ⟨n0, hn0⟩ := h i j w
  exact ⟨n0, fun m hm => hn0 (m + 1) (by omega)⟩

/- English proof (translation)
Introduce `i j` and use `(h i j).ge0 (fun k => hA k i j)`.
-/
theorem IntM.of_MT (h : MT V A B) (hA : ∀ k, IntM V (A k)) : IntM V B :=
  fun i j => (h i j).ge0 (fun k => hA k i j)

/- English proof (translation)
Introduce `i j`. Use `show ((0 : ℝ) : WithTop ℝ) ≤ V.v (∑ l, X i l * Y l j)`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[AddValuation.map_mul]`.

Establish `h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (X i l)` using `hX i l`. Establish `h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (Y l j)` using `hY l j`. Simplify using `using add_le_add h1 h2`.
-/
theorem IntM.mul {X Y : Matrix (Fin n) (Fin n) C} (hX : IntM V X) (hY : IntM V Y) : IntM V (X * Y) := by
  intro i j
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v (∑ l, X i l * Y l j)
  apply AddValuation.map_le_sum
  intro l _
  rw [AddValuation.map_mul]
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (X i l) := hX i l
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (Y l j) := hY l j
  simpa using add_le_add h1 h2

/- English proof (translation)
Use `show ((k : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) ^ k)`. Rewrite using `[AddValuation.map_pow, V.v_l, nsmul_one]`. Simplify using the standard rewrite rules.
-/
theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  show ((k : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) ^ k)
  rw [AddValuation.map_pow, V.v_l, nsmul_one]
  simp

end Lim

section Key

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

/- English proof (translation)
Introduce `i j w`. Take `⟨n0, hn0⟩` from `K.P_lim ⌈w⌉₊ i j`. Use `⟨n0, fun n hn => ?_⟩` and prove the remaining obligations. Establish `h` using `hn0 n hn`. Use `show (w : WithTop ℝ) ≤ _`.

Conclude with `le_trans (WithTop.coe_le_coe.mpr (Nat.le_ceil w)) h`.
-/
theorem hPT : MT V (fun k => K.ρ (K.ε ^ V.l ^ k)) K.P := by
  intro i j w
  obtain ⟨n0, hn0⟩ := K.P_lim ⌈w⌉₊ i j
  refine ⟨n0, fun n hn => ?_⟩
  have h := hn0 n hn
  show (w : WithTop ℝ) ≤ _
  exact le_trans (WithTop.coe_le_coe.mpr (Nat.le_ceil w)) h

/- English proof (translation)
Rewrite using `[← map_mul, mul_comm, map_mul]`.
-/
theorem ρ_comm (x y : O) : K.ρ x * K.ρ y = K.ρ y * K.ρ x := by
  rw [← map_mul, mul_comm, map_mul]

/- English proof (translation)
Establish `e : (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) = fun k => K.ρ x * K.ρ (K.ε ^ V.l ^ k)`. Use function extensionality and compare the values at `fun k => ρ_comm K _ _`. Establish `h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) (K.P * K.ρ x)` using `(hPT K).mul (MT.const _)`. Rewrite `h1` using `[e]`. Conclude with `h1.unique ((MT.const (K.ρ x)).mul (hPT K))`.
-/
theorem P_comm (x : O) : K.P * K.ρ x = K.ρ x * K.P := by
  have e : (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) = fun k => K.ρ x * K.ρ (K.ε ^ V.l ^ k) :=
    funext fun k => ρ_comm K _ _
  have h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) (K.P * K.ρ x) := (hPT K).mul (MT.const _)
  rw [e] at h1
  exact h1.unique ((MT.const (K.ρ x)).mul (hPT K))

/- English proof (translation)
Rewrite using `[map_mul, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]`.
-/
theorem ρ_natmul (m : ℕ) (y : O) : K.ρ ((m : O) * y) = (m : C) • K.ρ y := by
  rw [map_mul, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
The claim follows from `IntM.of_MT (hPT K) (fun k i j => K.ρ_int _ i j)`.
-/
theorem P_int : IntM V K.P :=
  IntM.of_MT (hPT K) (fun k i j => K.ρ_int _ i j)

/- English proof (translation)
Take `⟨y, hy⟩` from `K.ε_idem`. Establish `hd : ((V.l : ℕ) : O) ∣ K.ε ^ 2 - K.ε` using `⟨y, by rw [pow_two]; exact hy⟩`. Establish `hk : ∀ k : ℕ, ∃ z : O, (K.ε ^ 2) ^ V.l ^ k - K.ε ^ V.l ^ k = ((V.l ^ (k + 1) : ℕ) : O) * z`. Introduce `k`. Take `⟨z, hz⟩` from `dvd_sub_pow_of_dvd_sub hd k`.

Conclude with `⟨z, by rw [hz, Nat.cast_pow]⟩`. Use `choose z hz using hk`. Establish `e : ∀ k, K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k) = ((V.l ^ (k + 1) : ℕ) : C) • K.ρ (z k)`. Introduce `k`. Rewrite using `[← ρ_natmul K, ← hz k, map_sub, pow_right_comm, pow_two, map_mul]`.

Establish `h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) (K.P * K.P - K.P)` using `((hPT K).mul (hPT K)).sub (hPT K)`. Establish `h0 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) 0`. Introduce `i j w`. Use `⟨⌈w⌉₊, fun k hk => ?_⟩` and prove the remaining obligations. Use `show (w : WithTop ℝ) ≤ V.v ((0 : Matrix (Fin n) (Fin n) C) i j - (K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) i j)`.

Rewrite using `[e k, Matrix.zero_apply, zero_sub, AddValuation.map_neg, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul]`. Establish `h2 : (((k + 1 : ℕ) : ℝ) : WithTop ℝ) ≤ V.v (((V.l ^ (k + 1) : ℕ) : C))`. Use `ge_lpow (V := V) (k + 1)` as an intermediate fact. Rewrite using `[Nat.cast_pow]`. Conclude with `this`.

Establish `h3 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (K.ρ (z k) i j)` using `K.ρ_int _ i j`. Establish `h4r : w ≤ ((k + 1 : ℕ) : ℝ)` using `(Nat.le_ceil w).trans (by exact_mod_cast (by omega : ⌈w⌉₊ ≤ k + 1))`. Establish `h4 : (w : WithTop ℝ) ≤ (((k + 1 : ℕ) : ℝ) : WithTop ℝ)` using `WithTop.coe_le_coe.mpr h4r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[WithTop.coe_zero, add_zero]`.

Use `_ ≤ _ := add_le_add h2 h3`. Conclude with `sub_eq_zero.mp (h1.unique h0)`.
-/
theorem P_idem : K.P * K.P = K.P := by
  obtain ⟨y, hy⟩ := K.ε_idem
  have hd : ((V.l : ℕ) : O) ∣ K.ε ^ 2 - K.ε := ⟨y, by rw [pow_two]; exact hy⟩
  have hk : ∀ k : ℕ, ∃ z : O,
      (K.ε ^ 2) ^ V.l ^ k - K.ε ^ V.l ^ k = ((V.l ^ (k + 1) : ℕ) : O) * z := by
    intro k
    obtain ⟨z, hz⟩ := dvd_sub_pow_of_dvd_sub hd k
    exact ⟨z, by rw [hz, Nat.cast_pow]⟩
  choose z hz using hk
  have e : ∀ k, K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k) =
      ((V.l ^ (k + 1) : ℕ) : C) • K.ρ (z k) := by
    intro k
    rw [← ρ_natmul K, ← hz k, map_sub, pow_right_comm, pow_two, map_mul]
  have h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k))
      (K.P * K.P - K.P) := ((hPT K).mul (hPT K)).sub (hPT K)
  have h0 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) 0 := by
    intro i j w
    refine ⟨⌈w⌉₊, fun k hk => ?_⟩
    show (w : WithTop ℝ) ≤ V.v ((0 : Matrix (Fin n) (Fin n) C) i j -
      (K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) i j)
    rw [e k, Matrix.zero_apply, zero_sub, AddValuation.map_neg, Matrix.smul_apply, smul_eq_mul,
      AddValuation.map_mul]
    have h2 : (((k + 1 : ℕ) : ℝ) : WithTop ℝ) ≤ V.v (((V.l ^ (k + 1) : ℕ) : C)) := by
      have := ge_lpow (V := V) (k + 1)
      rw [Nat.cast_pow]
      exact this
    have h3 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (K.ρ (z k) i j) := K.ρ_int _ i j
    have h4r : w ≤ ((k + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil w).trans (by exact_mod_cast (by omega : ⌈w⌉₊ ≤ k + 1))
    have h4 : (w : WithTop ℝ) ≤ (((k + 1 : ℕ) : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.mpr h4r
    calc (w : WithTop ℝ) ≤ (((k + 1 : ℕ) : ℝ) : WithTop ℝ) := h4
      _ = (((k + 1 : ℕ) : ℝ) : WithTop ℝ) + ((0 : ℝ) : WithTop ℝ) := by
        rw [WithTop.coe_zero, add_zero]
      _ ≤ _ := add_le_add h2 h3
  exact sub_eq_zero.mp (h1.unique h0)

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (K.ρ x), ← P_comm K x, Matrix.mul_assoc K.P (K.ρ x), ← Matrix.mul_assoc K.P K.P, P_idem K, ← map_mul]`.
-/
theorem S_mul (x y : O) : K.P * K.ρ x * (K.P * K.ρ y) = K.P * K.ρ (x * y) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K.ρ x), ← P_comm K x, Matrix.mul_assoc K.P (K.ρ x),
    ← Matrix.mul_assoc K.P K.P, P_idem K, ← map_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, ih, S_mul, ← pow_succ]`.
-/
theorem S_pow (x : O) (m : ℕ) : (K.P * K.ρ x) ^ (m + 1) = K.P * K.ρ (x ^ (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, S_mul, ← pow_succ]

def Acl : Set (Matrix (Fin n) (Fin n) C) := {B | ∃ s : ℕ → O, MT V (fun k => K.P * K.ρ (s k)) B}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => x, MT.const _⟩`.
-/
theorem S_mem (x : O) : K.P * K.ρ x ∈ Acl K :=
  ⟨fun _ => x, MT.const _⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Take `⟨s', hs'⟩` from `hB'`. Use `⟨fun k => s k + s' k, ?_⟩` and prove the remaining obligations. Simplify `hs.add hs'` using `only [map_add, Matrix.mul_add]`.
-/
theorem add_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B + B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k + s' k, ?_⟩
  simpa only [map_add, Matrix.mul_add] using hs.add hs'

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Use `⟨fun k => -s k, ?_⟩` and prove the remaining obligations. Simplify `(MT.const (V := V) (0 : Matrix (Fin n) (Fin n) C)).sub hs` using `only [map_neg, Matrix.mul_neg, zero_sub]`.
-/
theorem neg_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : -B ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  refine ⟨fun k => -s k, ?_⟩
  simpa only [map_neg, Matrix.mul_neg, zero_sub] using (MT.const (V := V) (0 : Matrix (Fin n) (Fin n) C)).sub hs

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Take `⟨s', hs'⟩` from `hB'`. Use `⟨fun k => s k - s' k, ?_⟩` and prove the remaining obligations. Simplify `hs.sub hs'` using `only [map_sub, Matrix.mul_sub]`.
-/
theorem sub_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B - B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k - s' k, ?_⟩
  simpa only [map_sub, Matrix.mul_sub] using hs.sub hs'

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Take `⟨s', hs'⟩` from `hB'`. Use `⟨fun k => s k * s' k, ?_⟩` and prove the remaining obligations. Simplify `hs.mul hs'` using `only [S_mul K]`.
-/
theorem mul_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B * B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k * s' k, ?_⟩
  simpa only [S_mul K] using hs.mul hs'

/- English proof (translation)
Use `⟨fun _ => 1, ?_⟩` and prove the remaining obligations. Simplify `MT.const (V := V) K.P` using `only [map_one, Matrix.mul_one]`.
-/
theorem P_mem : K.P ∈ Acl K := by
  refine ⟨fun _ => 1, ?_⟩
  simpa only [map_one, Matrix.mul_one] using MT.const (V := V) K.P

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hB`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Conclude with `mul_mem K ih hB`.
-/
theorem pow_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (m : ℕ) : B ^ (m + 1) ∈ Acl K := by
  induction m with
  | zero => simpa using hB
  | succ m ih =>
    rw [pow_succ]
    exact mul_mem K ih hB

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Take `⟨s', hs'⟩` from `hB'`. Establish `e : (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) = fun k => K.P * K.ρ (s' k) * (K.P * K.ρ (s k))`. Use function extensionality and compare the values at `k`. Rewrite using `[S_mul, S_mul, mul_comm (s k)]`.

Establish `h1 : MT V (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) (B * B')` using `hs.mul hs'`. Rewrite `h1` using `[e]`. Conclude with `h1.unique (hs'.mul hs)`.
-/
theorem comm_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B * B' = B' * B := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  have e : (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) =
      fun k => K.P * K.ρ (s' k) * (K.P * K.ρ (s k)) := by
    funext k
    rw [S_mul, S_mul, mul_comm (s k)]
  have h1 : MT V (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) (B * B') := hs.mul hs'
  rw [e] at h1
  exact h1.unique (hs'.mul hs)

/- English proof (translation)
Take `⟨s, hs⟩` from `hB`. Conclude with `IntM.of_MT hs (fun k => IntM.mul (P_int K) (fun i j => K.ρ_int _ i j))`.
-/
theorem int_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : IntM V B := by
  obtain ⟨s, hs⟩ := hB
  exact IntM.of_MT hs (fun k => IntM.mul (P_int K) (fun i j => K.ρ_int _ i j))

/- English proof (translation)
Establish `hA' : ∀ k : ℕ, ∃ m : O, ∀ i j, V.Ge k (A k i j - (K.P * K.ρ m) i j)`. Introduce `k`. Take `⟨s, hs⟩` from `hA k`. Establish `hN : ∀ i j, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge k (A k i j - (K.P * K.ρ (s m)) i j)` using `fun i j => hs i j k`. Use `choose N hN using hN`.

Use `⟨s (Finset.univ.sup fun p : Fin n × Fin n => N p.1 p.2), fun i j => hN i j _ ?_⟩` and prove the remaining obligations. Conclude with `Finset.le_sup (f := fun p : Fin n × Fin n => N p.1 p.2) (Finset.mem_univ (i, j))`. Use `choose t ht using hA'`. Use `⟨t, fun i j w => ?_⟩` and prove the remaining obligations. Take `⟨n0, hn0⟩` from `h i j w`.

Use `⟨max n0 ⌈w⌉₊, fun k hk => ?_⟩` and prove the remaining obligations. Establish `h1 : V.Ge w (B i j - A k i j)` using `hn0 k (le_of_max_le_left hk)`. Establish `h2 : V.Ge k (A k i j - (K.P * K.ρ (t k)) i j)` using `ht k i j`. Establish `h2' : (w : WithTop ℝ) ≤ V.v (A k i j - (K.P * K.ρ (t k)) i j)` using `le_trans (WithTop.coe_le_coe.mpr ((Nat.le_ceil w).trans (by exact_mod_cast le_of_max_le_right hk))) h2`. Use `show (w : WithTop ℝ) ≤ V.v (B i j - (K.P * K.ρ (t k)) i j)`.

Establish `e : B i j - (K.P * K.ρ (t k)) i j = (B i j - A k i j) + (A k i j - (K.P * K.ρ (t k)) i j)` using `by ring`. Rewrite using `[e]`. Conclude with `le_trans (le_min h1 h2') (V.v.map_add _ _)`.
-/
theorem closed_mem {A : ℕ → Matrix (Fin n) (Fin n) C} {B : Matrix (Fin n) (Fin n) C} (hA : ∀ k, A k ∈ Acl K)
    (h : MT V A B) : B ∈ Acl K := by
  have hA' : ∀ k : ℕ, ∃ m : O, ∀ i j, V.Ge k (A k i j - (K.P * K.ρ m) i j) := by
    intro k
    obtain ⟨s, hs⟩ := hA k
    have hN : ∀ i j, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge k (A k i j - (K.P * K.ρ (s m)) i j) :=
      fun i j => hs i j k
    choose N hN using hN
    refine ⟨s (Finset.univ.sup fun p : Fin n × Fin n => N p.1 p.2), fun i j => hN i j _ ?_⟩
    exact Finset.le_sup (f := fun p : Fin n × Fin n => N p.1 p.2) (Finset.mem_univ (i, j))
  choose t ht using hA'
  refine ⟨t, fun i j w => ?_⟩
  obtain ⟨n0, hn0⟩ := h i j w
  refine ⟨max n0 ⌈w⌉₊, fun k hk => ?_⟩
  have h1 : V.Ge w (B i j - A k i j) := hn0 k (le_of_max_le_left hk)
  have h2 : V.Ge k (A k i j - (K.P * K.ρ (t k)) i j) := ht k i j
  have h2' : (w : WithTop ℝ) ≤ V.v (A k i j - (K.P * K.ρ (t k)) i j) :=
    le_trans (WithTop.coe_le_coe.mpr
      ((Nat.le_ceil w).trans (by exact_mod_cast le_of_max_le_right hk))) h2
  show (w : WithTop ℝ) ≤ V.v (B i j - (K.P * K.ρ (t k)) i j)
  have e : B i j - (K.P * K.ρ (t k)) i j =
      (B i j - A k i j) + (A k i j - (K.P * K.ρ (t k)) i j) := by ring
  rw [e]
  exact le_trans (le_min h1 h2') (V.v.map_add _ _)

end Key

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
