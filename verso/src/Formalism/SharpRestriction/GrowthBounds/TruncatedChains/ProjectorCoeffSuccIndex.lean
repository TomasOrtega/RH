import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc

noncomputable section

open Finset
open scoped Nat

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def dn (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (c + k + 1) * dn c k

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [dn]`. Consider the case `succ k ih`. Establish `h` using `Nat.add_one_mul_choose_eq (c + k) k`. Rewrite using `[dn, ih, Nat.factorial_succ, show c + (k + 1) = c + k + 1 by omega, ← mul_assoc, h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dn_eq (c k : ℕ) : dn c k = (c + k).choose k * k ! := by
  induction k with
  | zero => simp [dn]
  | succ k ih =>
    have h := Nat.add_one_mul_choose_eq (c + k) k
    rw [dn, ih, Nat.factorial_succ, show c + (k + 1) = c + k + 1 by omega, ← mul_assoc, h]
    ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [dn]`. Consider the case `succ k ih`. Simplify using `only [dn] at ih ⊢`. Rewrite using `[← ih]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dn_shift (c k : ℕ) : (c + 1) * dn (c + 1) k = dn c (k + 1) := by
  induction k with
  | zero => simp [dn]
  | succ k ih =>
    simp only [dn] at ih ⊢
    rw [← ih]
    ring

/- English proof (translation)
Rewrite using `[dn_eq]`. Conclude with `Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.factorial_pos k)`.
-/
theorem dn_pos (c k : ℕ) : 0 < dn c k := by
  rw [dn_eq]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.factorial_pos k)

section Coef

variable (K : Type*) [Field K] [CharZero K]

def al (c k : ℕ) : K := (-1) ^ k / ((dn c k : K) * (k ! : K))

/- English proof (translation)
Establish `h1 : (dn (c + 1) j : K) ≠ 0` using `by exact_mod_cast (dn_pos _ _).ne'`. Establish `h2 : (j ! : K) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos j).ne'`. Establish `h3 : (c : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero c`. Establish `h4 : (j : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero j`. Unfold `al`.

Rewrite using `[← dn_shift c j, Nat.factorial_succ]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem projector_coeff_succ_index (c j : ℕ) : al K c (j + 1) * ((j : K) + 1) = - al K (c + 1) j / ((c : K) + 1) := by
  have h1 : (dn (c + 1) j : K) ≠ 0 := by exact_mod_cast (dn_pos _ _).ne'
  have h2 : (j ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : (c : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero c
  have h4 : (j : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero j
  unfold al
  rw [← dn_shift c j, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `key : ((c : K) + j + 1) * (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K)`. Use `dn_shift c j` as an intermediate fact. Simplify using `only [dn] at this`. Conclude with `this.symm` after adjusting the coercions. Establish `hc : (c : K) + j + 1 ≠ 0`.

Use `Nat.cast_add_one_ne_zero (R := K) (c + j)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hd : (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K) / ((c : K) + j + 1)`. Rewrite using `[eq_div_iff hc, mul_comm, key]`.

Establish `h1 : (dn (c + 1) j : K) ≠ 0` using `by exact_mod_cast (dn_pos _ _).ne'`. Establish `h2 : (j ! : K) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos j).ne'`. Establish `h3 : (c : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero c`. Unfold `al`. Rewrite using `[hd]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem projector_coeff_succ_level (c j : ℕ) : al K c j = al K (c + 1) j * ((c : K) + j + 1) / ((c : K) + 1) := by
  have key : ((c : K) + j + 1) * (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K) := by
    have := dn_shift c j
    simp only [dn] at this
    exact_mod_cast this.symm
  have hc : (c : K) + j + 1 ≠ 0 := by
    have := Nat.cast_add_one_ne_zero (R := K) (c + j)
    push_cast at this
    exact this
  have hd : (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K) / ((c : K) + j + 1) := by
    rw [eq_div_iff hc, mul_comm, key]
  have h1 : (dn (c + 1) j : K) ≠ 0 := by exact_mod_cast (dn_pos _ _).ne'
  have h2 : (j ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : (c : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero c
  unfold al
  rw [hd]
  field_simp

end Coef

section Ring

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def P (f e : Module.End K V) (c T : ℕ) : Module.End K V :=
  ∑ k ∈ Finset.range (T + 1), al K c k • (f ^ k * e ^ k)

/- English proof (translation)
Unfold `pf P`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Unfold `divPowE`. Rewrite using `[smul_mul_smul_comm, smul_smul]`. Use `congr 1`.

Establish `h1 : (((c + k).choose k : ℕ) : K) ≠ 0` using `by exact_mod_cast (Nat.choose_pos (by omega)).ne'`. Establish `h2 : (k ! : K) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos k).ne'`. Unfold `al`. Rewrite using `[dn_eq]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem pf_eq_P {n : ℕ} (E : GLOps n K V) (a b : Fin n) (c T : ℕ) : pf E a b c T = P (E b a) (E a b) c T := by
  unfold pf P
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold divPowE
  rw [smul_mul_smul_comm, smul_smul]
  congr 1
  have h1 : (((c + k).choose k : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h2 : (k ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  unfold al
  rw [dn_eq]
  push_cast
  field_simp

/- English proof (translation)
Establish `hA : ∑ k ∈ Finset.range (T + 1), al K s k • t k = ∑ k ∈ Finset.range T, al K s k • t k`. Rewrite using `[Finset.sum_range_succ, hT, smul_zero, add_zero]`. Establish `hR : ∑ k ∈ Finset.range (T + 1), al K (s + 1) k • t k = ∑ k ∈ Finset.range T, al K (s + 1) k • t k`. Rewrite using `[Finset.sum_range_succ, hT, smul_zero, add_zero]`. Establish `hB : ∑ k ∈ Finset.range (T + 1), al K s k • (((k : K) * (γ + k)) • t (k - 1)) = ∑ j ∈ Finset.range T, (al K s (j + 1) * (((j : K) + 1) * (γ + j + 1))) • t j`.

Rewrite using `[Finset.sum_range_succ']`. Establish `h0 : al K s 0 • ((((0 : ℕ) : K) * (γ + ((0 : ℕ) : K))) • t (0 - 1)) = 0` using `by simp`. Rewrite using `[h0, add_zero]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, Nat.add_sub_cancel]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [smul_add, Finset.sum_add_distrib]`. Rewrite using `[hA, hB, hR, Finset.smul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul]`. Use `congr 1`. Establish `h1` using `projector_coeff_succ_index K s j`. Establish `h2` using `projector_coeff_succ_level K s j`.

Establish `hs : (s : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero s`. Establish `h3 : al K s (j + 1) * (((j : K) + 1) * (γ + j + 1)) = al K s (j + 1) * ((j : K) + 1) * (γ + j + 1)` using `by ring`. Rewrite using `[h2, h3, h1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele (t : ℕ → V) (s T : ℕ) (γ : K) (hT : t T = 0) :
    ∑ k ∈ Finset.range (T + 1), al K s k • (t k + ((k : K) * (γ + k)) • t (k - 1)) =
      (((s : K) - γ) / ((s : K) + 1)) • ∑ k ∈ Finset.range (T + 1), al K (s + 1) k • t k := by
  have hA : ∑ k ∈ Finset.range (T + 1), al K s k • t k = ∑ k ∈ Finset.range T, al K s k • t k := by
    rw [Finset.sum_range_succ, hT, smul_zero, add_zero]
  have hR : ∑ k ∈ Finset.range (T + 1), al K (s + 1) k • t k =
      ∑ k ∈ Finset.range T, al K (s + 1) k • t k := by
    rw [Finset.sum_range_succ, hT, smul_zero, add_zero]
  have hB : ∑ k ∈ Finset.range (T + 1), al K s k • (((k : K) * (γ + k)) • t (k - 1)) =
      ∑ j ∈ Finset.range T, (al K s (j + 1) * (((j : K) + 1) * (γ + j + 1))) • t j := by
    rw [Finset.sum_range_succ']
    have h0 : al K s 0 • ((((0 : ℕ) : K) * (γ + ((0 : ℕ) : K))) • t (0 - 1)) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, Nat.add_sub_cancel]
    congr 1
    push_cast
    ring
  simp only [smul_add, Finset.sum_add_distrib]
  rw [hA, hB, hR, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, ← add_smul]
  congr 1
  have h1 := projector_coeff_succ_index K s j
  have h2 := projector_coeff_succ_level K s j
  have hs : (s : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero s
  have h3 : al K s (j + 1) * (((j : K) + 1) * (γ + j + 1)) =
      al K s (j + 1) * ((j : K) + 1) * (γ + j + 1) := by ring
  rw [h2, h3, h1]
  field_simp
  ring

section Rank1

variable {e f h : Module.End K V}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Establish `key : h (e ((e ^ k) x)) = e (h ((e ^ k) x)) + (2 : K) • e ((e ^ k) x)`. Use `LinearMap.congr_fun hhe ((e ^ k) x)` as an intermediate fact.

Rewrite `this` using `[Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]`. Conclude with `this`. Rewrite using `[pow_succ', Module.End.mul_apply, key, ih, map_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_pow (hhe : h * e = e * h + (2 : K) • e) {x : V} {c : K} (hx : h x = c • x) (k : ℕ) :
    h ((e ^ k) x) = (c + 2 * k) • (e ^ k) x := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have key : h (e ((e ^ k) x)) = e (h ((e ^ k) x)) + (2 : K) • e ((e ^ k) x) := by
      have := LinearMap.congr_fun hhe ((e ^ k) x)
      rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      exact this
    rw [pow_succ', Module.End.mul_apply, key, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Establish `key : h (f ((f ^ k) x)) = f (h ((f ^ k) x)) - (2 : K) • f ((f ^ k) x)`. Use `LinearMap.congr_fun hhf ((f ^ k) x)` as an intermediate fact.

Rewrite `this` using `[Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]`. Conclude with `this`. Rewrite using `[pow_succ', Module.End.mul_apply, key, ih, map_smul, ← sub_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hF_pow (hhf : h * f = f * h - (2 : K) • f) {x : V} {c : K} (hx : h x = c • x) (k : ℕ) :
    h ((f ^ k) x) = (c - 2 * k) • (f ^ k) x := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have key : h (f ((f ^ k) x)) = f (h ((f ^ k) x)) - (2 : K) • f ((f ^ k) x) := by
      have := LinearMap.congr_fun hhf ((f ^ k) x)
      rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      exact this
    rw [pow_succ', Module.End.mul_apply, key, ih, map_smul, ← sub_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `hef' : ∀ y, e (f y) = f (e y) + h y` using `fun y => by`. Use `LinearMap.congr_fun hef y` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply]`. Conclude with `this`. Establish `hp : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y)` using `fun n y => by`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Proceed by induction on `k with`. Consider the case `zero => simp [hef', hv]`. Consider the case `succ k ih`. Establish `hfk` using `hF_pow hhf hv (k + 1)`.

Rewrite using `[hp (k + 1) v, hef', ih, hfk, map_add, map_smul, ← hp (k + 1) (e v), ← hp k v, add_assoc, ← add_smul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lemA (hef : e * f = f * e + h) (hhf : h * f = f * h - (2 : K) • f) {v : V} {c : K} (hv : h v = c • v)
    (k : ℕ) : e ((f ^ (k + 1)) v) = (f ^ (k + 1)) (e v) + (((k : K) + 1) * (c - k)) • (f ^ k) v := by
  have hef' : ∀ y, e (f y) = f (e y) + h y := fun y => by
    have := LinearMap.congr_fun hef y
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply] at this
    exact this
  have hp : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero => simp [hef', hv]
  | succ k ih =>
    have hfk := hF_pow hhf hv (k + 1)
    rw [hp (k + 1) v, hef', ih, hfk, map_add, map_smul, ← hp (k + 1) (e v), ← hp k v,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/- English proof (translation)
Establish `hef' : ∀ y, e (f y) = f (e y) + h y` using `fun y => by`. Use `LinearMap.congr_fun hef y` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply]`. Conclude with `this`. Establish `hp : ∀ (n : ℕ) (y : V), (e ^ (n + 1)) y = e ((e ^ n) y)` using `fun n y => by`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Proceed by induction on `k with`. Consider the case `zero => simp [hef', hv]`. Consider the case `succ k ih`. Establish `hek` using `hE_pow hhe hv (k + 1)`.

Rewrite using `[hp (k + 1) (f v), ih, map_add, map_smul, hef', hek, ← hp (k + 1) v, ← hp k v, add_assoc, ← add_smul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lemB (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e) {v : V} {c : K} (hv : h v = c • v)
    (k : ℕ) : (e ^ (k + 1)) (f v) = f ((e ^ (k + 1)) v) + (((k : K) + 1) * (c + k)) • (e ^ k) v := by
  have hef' : ∀ y, e (f y) = f (e y) + h y := fun y => by
    have := LinearMap.congr_fun hef y
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply] at this
    exact this
  have hp : ∀ (n : ℕ) (y : V), (e ^ (n + 1)) y = e ((e ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero => simp [hef', hv]
  | succ k ih =>
    have hek := hE_pow hhe hv (k + 1)
    rw [hp (k + 1) (f v), ih, map_add, map_smul, hef', hek, ← hp (k + 1) v, ← hp k v,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/- English proof (translation)
Simplify using `only [P, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]`.
-/
theorem P_apply (f e : Module.End K V) (c T : ℕ) (y : V) :
    P f e c T y = ∑ k ∈ Finset.range (T + 1), al K c k • (f ^ k) ((e ^ k) y) := by
  simp only [P, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]

/- English proof (translation)
Establish `hk : ∀ k : ℕ, e ((f ^ k) ((e ^ k) x)) = (f ^ k) ((e ^ k) (e x)) + ((k : K) * ((c + 1) + k)) • (f ^ (k - 1)) ((e ^ (k - 1)) (e x))`. Introduce `k`. Break down `k with _ | j` into its components or cases. Simplify using the standard rewrite rules. Establish `h1` using `lemA hef hhf (hE_pow hhe hx (j + 1)) j`.

Establish `h2 : e ((e ^ (j + 1)) x) = (e ^ (j + 1)) (e x)`. Rewrite using `[← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]`. Establish `h3 : (e ^ (j + 1)) x = (e ^ j) (e x)` using `by rw [pow_succ, Module.End.mul_apply]`. Rewrite using `[h1, h2, Nat.add_sub_cancel, ← h3]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ht` using `tele (fun j => (f ^ j) ((e ^ j) (e x))) s T (c + 1) (by simp [he])`. Rewrite using `[P_apply, P_apply, map_sum, show (s : K) - c - 1 = (s : K) - (c + 1) by ring, ← ht]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hk]`.
-/
theorem R1 (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e) (hhf : h * f = f * h - (2 : K) • f)
    {x : V} {c : K} (hx : h x = c • x) (s T : ℕ) (he : e ^ T = 0) :
    e (P f e s T x) = (((s : K) - c - 1) / ((s : K) + 1)) • P f e (s + 1) T (e x) := by
  have hk : ∀ k : ℕ, e ((f ^ k) ((e ^ k) x)) =
      (f ^ k) ((e ^ k) (e x)) + ((k : K) * ((c + 1) + k)) • (f ^ (k - 1)) ((e ^ (k - 1)) (e x)) := by
    intro k
    rcases k with _ | j
    · simp
    · have h1 := lemA hef hhf (hE_pow hhe hx (j + 1)) j
      have h2 : e ((e ^ (j + 1)) x) = (e ^ (j + 1)) (e x) := by
        rw [← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]
      have h3 : (e ^ (j + 1)) x = (e ^ j) (e x) := by rw [pow_succ, Module.End.mul_apply]
      rw [h1, h2, Nat.add_sub_cancel, ← h3]
      congr 2
      push_cast
      ring
  have ht := tele (fun j => (f ^ j) ((e ^ j) (e x))) s T (c + 1) (by simp [he])
  rw [P_apply, P_apply, map_sum, show (s : K) - c - 1 = (s : K) - (c + 1) by ring, ← ht]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hk]

/- English proof (translation)
Establish `hpf : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = (f ^ n) (f y)` using `fun n y => by`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Establish `hpf' : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y)` using `fun n y => by`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `key : ∀ k : ℕ, (f ^ k) ((e ^ k) (f z)) = (f ^ (k + 1)) ((e ^ k) z) + ((k : K) * ((c - 1) + k)) • (f ^ (k - 1 + 1)) ((e ^ (k - 1)) z)`.

Introduce `k`. Consider the cases of `k with`. Consider the case `zero => simp`. Consider the case `succ j`. Rewrite using `[lemB hef hhe hz j, map_add, map_smul, ← hpf (j + 1), Nat.add_sub_cancel]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ht` using `tele (fun k => (f ^ (k + 1)) ((e ^ k) z)) s T (c - 1) (by show (f ^ (T + 1)) ((e ^ T) z) = 0; rw [he]; simp)`. Use `beta_reduce at ht`.

Rewrite using `[P_apply, P_apply, map_sum]`. Simplify using `only [key, map_smul, ← hpf']`. Rewrite using `[ht]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sl2_projector_apply_f_eq_smul_f_projector_succ (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e)
    {z : V} {c : K} (hz : h z = c • z) (s T : ℕ) (he : e ^ T = 0) :
    P f e s T (f z) = (((s : K) + 1 - c) / ((s : K) + 1)) • f (P f e (s + 1) T z) := by
  have hpf : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = (f ^ n) (f y) := fun n y => by
    rw [pow_succ, Module.End.mul_apply]
  have hpf' : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  have key : ∀ k : ℕ, (f ^ k) ((e ^ k) (f z)) = (f ^ (k + 1)) ((e ^ k) z) +
      ((k : K) * ((c - 1) + k)) • (f ^ (k - 1 + 1)) ((e ^ (k - 1)) z) := by
    intro k
    cases k with
    | zero => simp
    | succ j =>
      rw [lemB hef hhe hz j, map_add, map_smul, ← hpf (j + 1), Nat.add_sub_cancel]
      congr 2
      push_cast
      ring
  have ht := tele (fun k => (f ^ (k + 1)) ((e ^ k) z)) s T (c - 1)
    (by show (f ^ (T + 1)) ((e ^ T) z) = 0; rw [he]; simp)
  beta_reduce at ht
  rw [P_apply, P_apply, map_sum]
  simp only [key, map_smul, ← hpf']
  rw [ht]
  congr 1
  ring

end Rank1

end Ring

end Formalism.MainNotions.G.ExtremalProjector
