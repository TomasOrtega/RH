import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Lemmata.GeneralBFactSecondLast.Imports

open Finset

noncomputable section

namespace Formalism.FrobeniusOrbits.ThickExists

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second_last.goal1 .. | (apply Bl.general_b_fact_second_last.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_last.goal1 <;> assumption)`.
-/
lemma coeff_zero (B : ℤ) : ∀ {S : ℕ} (c : Fin S → ℤ), (∀ m, |c m| < B) →
    ∑ m, c m * B ^ (m : ℕ) = 0 → ∀ m, c m = 0 := by
  first | exact Bl.general_b_fact_second_last.goal1 .. | (apply Bl.general_b_fact_second_last.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_last.goal1 <;> assumption)

/- English proof (translation)
Introduce `S`. Proceed by induction on `S with`. Consider the case `zero => intro v _`. Simplify using `[Behrend.map_apply]`. Consider the case `succ S ih`.

Introduce `v hv`. Establish `h1` using `ih (fun m => v m.succ) (fun m => hv _)`. Establish `hsplit : Behrend.map B v = v 0 + B * Behrend.map B (fun m : Fin S => v m.succ)`. Simplify using `only [Behrend.map_apply]`. Rewrite using `[Fin.sum_univ_succ, Finset.mul_sum]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.val_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, pow_succ]`. Establish `h2 : B * (Behrend.map B (fun m : Fin S => v m.succ) + 1) ≤ B * B ^ S` using `Nat.mul_le_mul_left B h1`. Establish `h3` using `hv 0`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma map_lt (B : ℕ) : ∀ {S : ℕ} (v : Fin S → ℕ), (∀ m, v m < B) → Behrend.map B v < B ^ S := by
  intro S
  induction S with
  | zero => intro v _; simp [Behrend.map_apply]
  | succ S ih =>
    intro v hv
    have h1 := ih (fun m => v m.succ) (fun m => hv _)
    have hsplit : Behrend.map B v = v 0 + B * Behrend.map B (fun m : Fin S => v m.succ) := by
      simp only [Behrend.map_apply]
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · simp
      · refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Fin.val_succ, pow_succ]
        ring
    rw [hsplit, pow_succ]
    have h2 : B * (Behrend.map B (fun m : Fin S => v m.succ) + 1) ≤ B * B ^ S :=
      Nat.mul_le_mul_left B h1
    have h3 := hv 0
    nlinarith

/- English proof (translation)
Establish `hA : ∑ m, (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2) = 0`. Establish `e : ∀ m, 2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2 = v₂ m ^ 2 - v₁ m ^ 2` using `fun m => by ring`. Rewrite using `[Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₂, h₁, sub_self]`. Establish `hB : ∑ m, (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) = 0`. Establish `e : ∀ m, 2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2 = v₃ m ^ 2 - v₁ m ^ 2` using `fun m => by ring`.

Rewrite using `[Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₃, h₁, sub_self]`. Establish `hW : ∑ m, i * (i - j) * (v₃ m - v₁ m) ^ 2 = 0`. Establish `e : ∀ m, i * (i - j) * (v₃ m - v₁ m) ^ 2 = j ^ 2 * (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2) - i * j * (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2)` using `fun m => by`. Take the linear combination `(-(2 * j * v₁ m + j * (v₂ m - v₁ m) + i * (v₃ m - v₁ m))) * h m`. Rewrite using `[Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB, mul_zero, mul_zero, sub_zero]`.

Distinguish the cases in `hi : i = 0`. Use function extensionality and compare the values at `m`. Establish `h'` using `h m`. Rewrite `h'` using `[hi, zero_mul]`. Establish `h''` using `(mul_eq_zero.mp h').resolve_left hj`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : i * (i - j) ≠ 0` using `mul_ne_zero hi (sub_ne_zero.mpr hij)`. Rewrite `hW` using `[← Finset.mul_sum]`. Establish `hs0` using `(mul_eq_zero.mp hW).resolve_left hne`. Establish `hw0 : ∀ m, v₃ m - v₁ m = 0`.

Introduce `m`. Establish `h'` using `(Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (v₃ m - v₁ m))).mp hs0 m (Finset.mem_univ m)`. Conclude with `(pow_eq_zero_iff two_ne_zero).mp h'`. Use function extensionality and compare the values at `m`. Establish `h'` using `h m`.

Rewrite `h'` using `[hw0 m, mul_zero]`. Establish `h''` using `(mul_eq_zero.mp h').resolve_left hj`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sphere_rel {S : ℕ} (v₁ v₂ v₃ : Fin S → ℤ) (k : ℤ) (h₁ : ∑ m, v₁ m ^ 2 = k)
    (h₂ : ∑ m, v₂ m ^ 2 = k) (h₃ : ∑ m, v₃ m ^ 2 = k) (i j : ℤ) (hj : j ≠ 0) (hij : i ≠ j)
    (h : ∀ m, j * (v₂ m - v₁ m) = i * (v₃ m - v₁ m)) : v₂ = v₁ := by
  have hA : ∑ m, (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2 = v₂ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₂, h₁, sub_self]
  have hB : ∑ m, (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2 = v₃ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₃, h₁, sub_self]
  have hW : ∑ m, i * (i - j) * (v₃ m - v₁ m) ^ 2 = 0 := by
    have e : ∀ m, i * (i - j) * (v₃ m - v₁ m) ^ 2
        = j ^ 2 * (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2)
          - i * j * (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) := fun m => by
      linear_combination (-(2 * j * v₁ m + j * (v₂ m - v₁ m) + i * (v₃ m - v₁ m))) * h m
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hA, hB, mul_zero, mul_zero, sub_zero]
  by_cases hi : i = 0
  · funext m
    have h' := h m
    rw [hi, zero_mul] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith
  · have hne : i * (i - j) ≠ 0 := mul_ne_zero hi (sub_ne_zero.mpr hij)
    rw [← Finset.mul_sum] at hW
    have hs0 := (mul_eq_zero.mp hW).resolve_left hne
    have hw0 : ∀ m, v₃ m - v₁ m = 0 := by
      intro m
      have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (v₃ m - v₁ m))).mp hs0 m
        (Finset.mem_univ m)
      exact (pow_eq_zero_iff two_ne_zero).mp h'
    funext m
    have h' := h m
    rw [hw0 m, mul_zero] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith

/- English proof (translation)
Rewrite using `[Behrend.map_apply, Nat.cast_sum]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, Nat.cast_pow]`.
-/
lemma cast_map (B : ℕ) {S : ℕ} (v : Fin S → ℕ) :
    ((Behrend.map B v : ℕ) : ℤ) = ∑ m, (v m : ℤ) * (B : ℤ) ^ (m : ℕ) := by
  rw [Behrend.map_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.cast_mul, Nat.cast_pow]

/- English proof (translation)
Simplify using `only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv`. Conclude with `hv`.
-/
private lemma sphere_mem_lemma {S d k : ℕ} {v : Fin S → ℕ} (hv : v ∈ Behrend.sphere S d k) :
    (∀ i, v i < d) ∧ ∑ i, v i ^ 2 = k := by
  simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv
  exact hv

/- English proof (translation)
Unfold `NoRel`. Introduce `s₁ hs₁ s₂ hs₂ s₃ hs₃ h12 h13 h23 i j hi0 hiL hj0 hjL hij heq`. Rewrite `hs₁`, `hs₂`, `hs₃` using `[Finset.mem_image]`. Take `⟨v₁, hv₁, rfl⟩` from `hs₁`. Take `⟨v₂, hv₂, rfl⟩` from `hs₂`.

Take `⟨v₃, hv₃, rfl⟩` from `hs₃`. Take `⟨hb₁, hq₁⟩` from `sphere_mem_lemma hv₁`. Take `⟨hb₂, hq₂⟩` from `sphere_mem_lemma hv₂`. Take `⟨hb₃, hq₃⟩` from `sphere_mem_lemma hv₃`. Rewrite `heq` using `[cast_map, cast_map, cast_map]`.

Take `⟨B, hB⟩ : ∃ B : ℤ, B = ((4 * L * d : ℕ) : ℤ)` from `⟨_, rfl⟩`. Rewrite `heq` using `[← hB]`. Establish `hL' : (1 : ℤ) ≤ L` using `by exact_mod_cast hL`. Take `⟨hi1, hi2⟩` from `abs_le.mp hiL`. Take `⟨hj1, hj2⟩` from `abs_le.mp hjL`.

Establish `hbound : ∀ m : Fin S, |j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)| < B`. Introduce `m`. Establish `a1 : (v₁ m : ℤ) < d` using `by exact_mod_cast hb₁ m`. Establish `a2 : (v₂ m : ℤ) < d` using `by exact_mod_cast hb₂ m`. Establish `a3 : (v₃ m : ℤ) < d` using `by exact_mod_cast hb₃ m`.

Establish `z1 : (0 : ℤ) ≤ v₁ m` using `by positivity`. Establish `z2 : (0 : ℤ) ≤ v₂ m` using `by positivity`. Establish `z3 : (0 : ℤ) ≤ v₃ m` using `by positivity`. Establish `hdpos : (1 : ℤ) ≤ d` using `by omega`. Establish `f1 : (0 : ℤ) ≤ L - j` using `by linarith`.

Establish `f2 : (0 : ℤ) ≤ L + j` using `by linarith`. Establish `f3 : (0 : ℤ) ≤ L - i` using `by linarith`. Establish `f4 : (0 : ℤ) ≤ L + i` using `by linarith`. Establish `g1 : (0 : ℤ) ≤ d + ((v₂ m : ℤ) - v₁ m)` using `by linarith`. Establish `g2 : (0 : ℤ) ≤ d - ((v₂ m : ℤ) - v₁ m)` using `by linarith`.

Establish `g3 : (0 : ℤ) ≤ d + ((v₃ m : ℤ) - v₁ m)` using `by linarith`. Establish `g4 : (0 : ℤ) ≤ d - ((v₃ m : ℤ) - v₁ m)` using `by linarith`. Establish `hLd : (1 : ℤ) ≤ L * d` using `by nlinarith`. Rewrite using `[hB]`. Use `push_cast`.

Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;> nlinarith [mul_nonneg f1 g1, mul_nonneg f2 g2, mul_nonneg f1 g2, mul_nonneg f2 g1, mul_nonneg f3 g3, mul_nonneg f4 g4, mul_nonneg f3 g4, mul_nonneg f4 g3]`. Establish `hsum : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ) = 0`. Establish `E : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ) = ∑ m, (j * ((v₂ m : ℤ) * B ^ (m : ℕ)) - j * ((v₁ m : ℤ) * B ^ (m : ℕ)) - i * ((v₃ m : ℤ) * B ^ (m : ℕ)) + i * ((v₁ m : ℤ) * B ^ (m : ℕ)))` using `Finset.sum_congr rfl (fun m _ => by ring)`. Rewrite using `[E, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]`.

Take the linear combination `heq`. Establish `hzero` using `coeff_zero B (fun m => j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) hbound hsum`. Establish `q₁ : ∑ m, ((v₁ m : ℕ) : ℤ) ^ 2 = (k : ℤ)` using `by exact_mod_cast hq₁`. Establish `q₂ : ∑ m, ((v₂ m : ℕ) : ℤ) ^ 2 = (k : ℤ)` using `by exact_mod_cast hq₂`. Establish `q₃ : ∑ m, ((v₃ m : ℕ) : ℤ) ^ 2 = (k : ℤ)` using `by exact_mod_cast hq₃`.

Establish `hrel` using `sphere_rel (fun m => (v₁ m : ℤ)) (fun m => (v₂ m : ℤ)) (fun m => (v₃ m : ℤ)) (k : ℤ) q₁ q₂ q₃ i j (abs_pos.mp hj0) hij (fun m => by show j * ((v₂ m : ℤ) - v₁ m) = i * ((v₃ m : ℤ) - v₁ m)`. Establish `h0 : j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m) = 0` using `hzero m`. Use the proof step `linarith)`. Establish `hv : v₂ = v₁` using `funext fun m => Nat.cast_injective (congrFun hrel m)`. Conclude with `h12 (by rw [hv])`.
-/
lemma noRel_image (L S d k : ℕ) (hL : 1 ≤ L) :
    NoRel ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))) L := by
  unfold NoRel
  intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12 h13 h23 i j hi0 hiL hj0 hjL hij heq
  rw [Finset.mem_image] at hs₁ hs₂ hs₃
  obtain ⟨v₁, hv₁, rfl⟩ := hs₁
  obtain ⟨v₂, hv₂, rfl⟩ := hs₂
  obtain ⟨v₃, hv₃, rfl⟩ := hs₃
  obtain ⟨hb₁, hq₁⟩ := sphere_mem_lemma hv₁
  obtain ⟨hb₂, hq₂⟩ := sphere_mem_lemma hv₂
  obtain ⟨hb₃, hq₃⟩ := sphere_mem_lemma hv₃
  rw [cast_map, cast_map, cast_map] at heq
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = ((4 * L * d : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hB] at heq
  have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
  obtain ⟨hi1, hi2⟩ := abs_le.mp hiL
  obtain ⟨hj1, hj2⟩ := abs_le.mp hjL
  have hbound : ∀ m : Fin S, |j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)| < B := by
    intro m
    have a1 : (v₁ m : ℤ) < d := by exact_mod_cast hb₁ m
    have a2 : (v₂ m : ℤ) < d := by exact_mod_cast hb₂ m
    have a3 : (v₃ m : ℤ) < d := by exact_mod_cast hb₃ m
    have z1 : (0 : ℤ) ≤ v₁ m := by positivity
    have z2 : (0 : ℤ) ≤ v₂ m := by positivity
    have z3 : (0 : ℤ) ≤ v₃ m := by positivity
    have hdpos : (1 : ℤ) ≤ d := by omega
    have f1 : (0 : ℤ) ≤ L - j := by linarith
    have f2 : (0 : ℤ) ≤ L + j := by linarith
    have f3 : (0 : ℤ) ≤ L - i := by linarith
    have f4 : (0 : ℤ) ≤ L + i := by linarith
    have g1 : (0 : ℤ) ≤ d + ((v₂ m : ℤ) - v₁ m) := by linarith
    have g2 : (0 : ℤ) ≤ d - ((v₂ m : ℤ) - v₁ m) := by linarith
    have g3 : (0 : ℤ) ≤ d + ((v₃ m : ℤ) - v₁ m) := by linarith
    have g4 : (0 : ℤ) ≤ d - ((v₃ m : ℤ) - v₁ m) := by linarith
    have hLd : (1 : ℤ) ≤ L * d := by nlinarith
    rw [hB]
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith [mul_nonneg f1 g1, mul_nonneg f2 g2, mul_nonneg f1 g2,
      mul_nonneg f2 g1, mul_nonneg f3 g3, mul_nonneg f4 g4, mul_nonneg f3 g4, mul_nonneg f4 g3]
  have hsum : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ) = 0 := by
    have E : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ)
        = ∑ m, (j * ((v₂ m : ℤ) * B ^ (m : ℕ)) - j * ((v₁ m : ℤ) * B ^ (m : ℕ))
          - i * ((v₃ m : ℤ) * B ^ (m : ℕ)) + i * ((v₁ m : ℤ) * B ^ (m : ℕ))) :=
      Finset.sum_congr rfl (fun m _ => by ring)
    rw [E, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination heq
  have hzero := coeff_zero B (fun m => j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m))
    hbound hsum
  have q₁ : ∑ m, ((v₁ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₁
  have q₂ : ∑ m, ((v₂ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₂
  have q₃ : ∑ m, ((v₃ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₃
  have hrel := sphere_rel (fun m => (v₁ m : ℤ)) (fun m => (v₂ m : ℤ)) (fun m => (v₃ m : ℤ))
    (k : ℤ) q₁ q₂ q₃ i j (abs_pos.mp hj0) hij (fun m => by
      show j * ((v₂ m : ℤ) - v₁ m) = i * ((v₃ m : ℤ) - v₁ m)
      have h0 : j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m) = 0 := hzero m
      linarith)
  have hv : v₂ = v₁ := funext fun m => Nat.cast_injective (congrFun hrel m)
  exact h12 (by rw [hv])

/- English proof (translation)
Apply `Finset.card_image_of_injOn` to reduce the goal to its premises. Introduce `v hv w hw hvw`. Take `⟨hbv, -⟩` from `sphere_mem_lemma (Finset.mem_coe.mp hv)`. Take `⟨hbw, -⟩` from `sphere_mem_lemma (Finset.mem_coe.mp hw)`. Establish `hc : ((Behrend.map (4 * L * d) v : ℕ) : ℤ) = ((Behrend.map (4 * L * d) w : ℕ) : ℤ)`.

Rewrite using `[hvw]`. Rewrite `hc` using `[cast_map, cast_map]`. Establish `hbound : ∀ m : Fin S, |(v m : ℤ) - w m| < ((4 * L * d : ℕ) : ℤ)`. Introduce `m`. Establish `a1 : (v m : ℤ) < d` using `by exact_mod_cast hbv m`.

Establish `a2 : (w m : ℤ) < d` using `by exact_mod_cast hbw m`. Establish `z1 : (0 : ℤ) ≤ v m` using `by positivity`. Establish `z2 : (0 : ℤ) ≤ w m` using `by positivity`. Establish `z3 : (0 : ℤ) ≤ d` using `by positivity`. Establish `hL' : (1 : ℤ) ≤ L` using `by exact_mod_cast hL`.

Use `push_cast`. Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;> nlinarith`. Establish `hsum : ∑ m, ((v m : ℤ) - w m) * ((4 * L * d : ℕ) : ℤ) ^ (m : ℕ) = 0`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`.

Rewrite using `[hc, sub_self]`. Establish `hz` using `coeff_zero ((4 * L * d : ℕ) : ℤ) (fun m => (v m : ℤ) - w m) hbound hsum`. Use function extensionality and compare the values at `m`. Establish `h0 : (v m : ℤ) - w m = 0` using `hz m`. Use linear arithmetic over natural numbers and integers.
-/
lemma card_image (L S d k : ℕ) (hL : 1 ≤ L) :
    ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))).card =
      (Behrend.sphere S d k).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  obtain ⟨hbv, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hv)
  obtain ⟨hbw, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hw)
  have hc : ((Behrend.map (4 * L * d) v : ℕ) : ℤ) = ((Behrend.map (4 * L * d) w : ℕ) : ℤ) := by
    rw [hvw]
  rw [cast_map, cast_map] at hc
  have hbound : ∀ m : Fin S, |(v m : ℤ) - w m| < ((4 * L * d : ℕ) : ℤ) := by
    intro m
    have a1 : (v m : ℤ) < d := by exact_mod_cast hbv m
    have a2 : (w m : ℤ) < d := by exact_mod_cast hbw m
    have z1 : (0 : ℤ) ≤ v m := by positivity
    have z2 : (0 : ℤ) ≤ w m := by positivity
    have z3 : (0 : ℤ) ≤ d := by positivity
    have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith
  have hsum : ∑ m, ((v m : ℤ) - w m) * ((4 * L * d : ℕ) : ℤ) ^ (m : ℕ) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hc, sub_self]
  have hz := coeff_zero ((4 * L * d : ℕ) : ℤ) (fun m => (v m : ℤ) - w m) hbound hsum
  funext m
  have h0 : (v m : ℤ) - w m = 0 := hz m
  omega

end Formalism.FrobeniusOrbits.ThickExists

namespace Formalism.FrobeniusOrbits

set_option maxHeartbeats 1000000 in
open ThickExists in
/- English proof (translation)
Unfold `HostThickExists`. Use `⟨32, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `n L hL`. Establish `hL2 : (2 : ℝ) ≤ L` using `by exact_mod_cast hL`. Establish `hLpos : (0 : ℝ) < L` using `by linarith`.

Take `⟨y, hy⟩ : ∃ y : ℝ, y = Real.log (L : ℝ)` from `⟨_, rfl⟩`. Take `⟨x, hx⟩ : ∃ x : ℝ, x = Real.log (n : ℝ)` from `⟨_, rfl⟩`. Take `⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (x * y)` from `⟨_, rfl⟩`. Establish `hrw : Real.sqrt (Real.log (n : ℝ) * Real.log (L : ℝ)) = s` using `by rw [hs, hx, hy]`. Rewrite using `[hrw]`.

Establish `hy_half : (1 : ℝ) / 2 < y`. Establish `h1` using `Real.log_two_gt_d9`. Establish `h2` using `Real.log_le_log (by norm_num) hL2`. Rewrite using `[hy]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hy0 : 0 < y` using `by linarith`. Distinguish the cases in `hsmall : (n : ℝ) * Real.exp (-32 * s) / L ≤ 1`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Use `⟨∅, by simp, ?_, by simp [hn]⟩` and prove the remaining obligations. Unfold `NoRel`.

Introduce `s₁ hs₁`. Simplify using `at hs₁`. Use `⟨{0}, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_singleton]`.

Substitute `hm` using the available equality. Simplify using `using hn`. Unfold `NoRel`. Introduce `s₁ hs₁ s₂ hs₂ s₃ hs₃ h12`. Rewrite `hs₁`, `hs₂` using `[Finset.mem_singleton]`.

Conclude with `absurd (hs₁.trans hs₂.symm) h12`. Rewrite using `[Finset.card_singleton, Nat.cast_one]`. Conclude with `hsmall`. Use `push_neg at hsmall`. Establish `hnpos : (0 : ℝ) < n`.

Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Rewrite `hsmall` using `[hn]`. Evaluate the numerical expressions using `at hsmall`. Conclude with `hn` after adjusting the coercions. Establish `eL : Real.exp y = L` using `by rw [hy, Real.exp_log hLpos]`.

Establish `en : Real.exp x = n` using `by rw [hx, Real.exp_log hnpos]`. Establish `hpos : 0 < x + -32 * s - y`. Rewrite using `[← Real.exp_lt_exp, Real.exp_zero, Real.exp_sub, Real.exp_add, eL, en]`. Conclude with `hsmall`. Establish `hs0 : 0 ≤ s` using `by rw [hs]; exact Real.sqrt_nonneg _`.

Establish `hxpos : 0 < x` using `by linarith`. Establish `hs2 : s ^ 2 = x * y` using `by rw [hs]; exact Real.sq_sqrt (mul_pos hxpos hy0).le`. Establish `hs32 : 32 * y < s`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use polynomial arithmetic with `[mul_nonneg hs0 (sub_nonneg.mpr hc), mul_pos hpos hy0, sq_nonneg y]`. Establish `hs16 : 16 < s` using `by linarith`. Take `⟨S, hSdef⟩ : ∃ S : ℕ, S = ⌊s / y⌋₊` from `⟨_, rfl⟩`. Establish `hS1 : (S : ℝ) ≤ s / y` using `by rw [hSdef]; exact Nat.floor_le (div_nonneg hs0 hy0.le)`. Establish `hS2 : s / y < S + 1` using `by rw [hSdef]; exact Nat.lt_floor_add_one _`.

Establish `hSy : (S : ℝ) * y ≤ s` using `(le_div_iff₀ hy0).mp hS1`. Establish `hSy2 : s < (S + 1) * y` using `(div_lt_iff₀ hy0).mp hS2`. Establish `hS31 : (31 : ℝ) < S`. Establish `h` using `lt_of_mul_lt_mul_right (show (32 : ℝ) * y < (S + 1) * y by linarith) hy0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hSpos : (0 : ℝ) < S` using `by linarith`. Establish `hSne : (S : ℝ) ≠ 0` using `hSpos.ne'`. Take `⟨a, ha⟩ : ∃ a : ℝ, a = (x - y - 3) / S` from `⟨_, rfl⟩`. Establish `haS : a * S = x - y - 3` using `by rw [ha]; field_simp`. Establish `h2Sy : s ≤ 2 * S * y`.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ S - 1) hy0.le]`. Establish `hxle : x ≤ 2 * s * S`. Establish `h : x * y ≤ (2 * s * S) * y` using `by nlinarith [mul_le_mul_of_nonneg_left h2Sy hs0]`. Conclude with `le_of_mul_le_mul_right h hy0`. Establish `ha2s : a ≤ 2 * s`.

Establish `h : a * S ≤ (2 * s) * S` using `by nlinarith`. Conclude with `le_of_mul_le_mul_right h hSpos`. Establish `ha7 : 7 + y ≤ a`. Establish `h1 : (7 + y) * S * y ≤ (x - y - 3) * y`. Use polynomial arithmetic with `[mul_nonneg hy0.le (sub_nonneg.mpr hSy), mul_nonneg hs0 (sub_nonneg.mpr hs32.le), mul_nonneg hy0.le (sub_nonneg.mpr hs32.le), mul_nonneg hs0 (sub_nonneg.mpr hy_half.le)]`.

Establish `h2 : (7 + y) * S ≤ x - y - 3` using `le_of_mul_le_mul_right h1 hy0`. Conclude with `le_of_mul_le_mul_right (by rw [haS]; exact h2) hSpos`. Establish `hexpb : 3 + S * (7 + y) + S + 2 * a ≤ 32 * s`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hy_half.le) hSpos.le]`. Establish `h4L : (0 : ℝ) < 4 * L` using `by positivity`.

Take `⟨d, hddef⟩ : ∃ d : ℕ, d = ⌊Real.exp a / (4 * L)⌋₊` from `⟨_, rfl⟩`. Establish `hd1 : (d : ℝ) ≤ Real.exp a / (4 * L)` using `by rw [hddef]; exact Nat.floor_le (by positivity)`. Establish `hd2 : Real.exp a / (4 * L) < d + 1` using `by rw [hddef]; exact Nat.lt_floor_add_one _`. Establish `hd1' : (d : ℝ) * (4 * L) ≤ Real.exp a` using `(le_div_iff₀ h4L).mp hd1`. Establish `hd2' : Real.exp a < (d + 1) * (4 * L)` using `(div_lt_iff₀ h4L).mp hd2`.

Establish `h8Ly : 8 * (L : ℝ) ≤ Real.exp (7 + y)`. Establish `h87 : (8 : ℝ) ≤ Real.exp 7` using `by linarith [Real.add_one_le_exp (7 : ℝ)]`. Rewrite using `[Real.exp_add, eL]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h8L : 8 * (L : ℝ) ≤ Real.exp a` using `le_trans h8Ly (Real.exp_le_exp.mpr ha7)`.

Establish `hQd : Real.exp a / (8 * L) ≤ d`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hd1r : (1 : ℝ) ≤ d` using `le_trans ((one_le_div (by positivity)).mpr h8L) hQd`. Establish `hdpos : (0 : ℝ) < d` using `by linarith`.

Establish `hdQ : (d : ℝ) ≤ Real.exp a`. Use polynomial arithmetic with `[mul_nonneg hdpos.le (by linarith : (0 : ℝ) ≤ 4 * L - 1)]`. Establish `hdS : Real.exp a ^ S ≤ (d : ℝ) ^ S * (8 * L) ^ S`. Establish `h : (Real.exp a / (8 * L)) ^ S ≤ (d : ℝ) ^ S` using `by gcongr`. Rewrite `h` using `[div_pow, div_le_iff₀ (by positivity)]`. Then use the resulting hypothesis.

Establish `hQS : Real.exp a ^ S = Real.exp (x - y - 3)`. Rewrite using `[← Real.exp_nat_mul, mul_comm, haS]`. Establish `hn_eq : (n : ℝ) = Real.exp a ^ S * L * Real.exp 3`. Rewrite using `[hQS, ← eL, ← Real.exp_add, ← Real.exp_add, ← en]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hprod : Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2 ≤ Real.exp (32 * s)`. Establish `hP : ((8 : ℝ) * L) ^ S ≤ Real.exp (S * (7 + y))`. Rewrite using `[Real.exp_nat_mul]`. Use `gcongr`.

Establish `hSe : (S : ℝ) ≤ Real.exp S` using `by linarith [Real.add_one_le_exp (S : ℝ)]`. Establish `hQ2 : Real.exp a ^ 2 = Real.exp (2 * a)` using `by rw [sq, ← Real.exp_add, two_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQ2]`. Use `gcongr`.

Use `_ = Real.exp (3 + S * (7 + y) + S + 2 * a) := by`. Rewrite using `[Real.exp_add, Real.exp_add, Real.exp_add]`. Use `_ ≤ Real.exp (32 * s) := Real.exp_le_exp.mpr hexpb`. Take `⟨k, hk⟩` from `Behrend.exists_large_sphere S d`. Use `⟨(Behrend.sphere S d k).image (Behrend.map (4 * L * d)), ?_, noRel_image L S d k (by omega), ?_⟩` and prove the remaining obligations.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_image]`. Take `⟨v, hv, rfl⟩` from `hm`. Take `⟨hbox, -⟩` from `sphere_mem_lemma hv`. Establish `hdd : d ≤ 4 * L * d` using `by nlinarith`.

Establish `hmlt` using `map_lt (4 * L * d) v (fun i => lt_of_lt_of_le (hbox i) hdd)`. Establish `hpowle : ((4 : ℝ) * L * d) ^ S ≤ Real.exp a ^ S` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hreal : (4 : ℝ) * L * (4 * L * d) ^ S ≤ n`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hpowle h4L.le, mul_nonneg (by linarith [Real.add_one_le_exp (3 : ℝ)] : (0 : ℝ) ≤ Real.exp 3 - 4) (by positivity : (0 : ℝ) ≤ L * Real.exp a ^ S)]`.

Establish `hnat : 4 * L * (4 * L * d) ^ S ≤ n` using `by exact_mod_cast hreal`. Conclude with `lt_of_lt_of_le (mul_lt_mul_of_pos_left hmlt (by omega)) hnat`. Rewrite using `[card_image L S d k (by omega)]`. Use `le_trans ?_ hk` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[div_le_iff₀ hLpos, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hSpos (pow_pos hdpos 2))]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hn_eq]`. Use `_ ≤ ((d : ℝ) ^ S * (8 * L) ^ S * L * Real.exp 3) * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by gcongr`. Use `_ = (d : ℝ) ^ S * L * (Real.exp (-32 * s) * (Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2)) := by`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (d : ℝ) ^ S * L * (Real.exp (-32 * s) * Real.exp (32 * s)) := by gcongr`. Use `_ = (d : ℝ) ^ S * L := by`. Rewrite using `[← Real.exp_add, show -32 * s + 32 * s = 0 by ring, Real.exp_zero, mul_one]`.
-/
theorem hostThickExists : HostThickExists := by
  unfold HostThickExists
  refine ⟨32, by norm_num, ?_⟩
  intro n L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log (L : ℝ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (x * y) := ⟨_, rfl⟩
  have hrw : Real.sqrt (Real.log (n : ℝ) * Real.log (L : ℝ)) = s := by rw [hs, hx, hy]
  rw [hrw]
  have hy_half : (1 : ℝ) / 2 < y := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hL2
    rw [hy]
    linarith
  have hy0 : 0 < y := by linarith
  by_cases hsmall : (n : ℝ) * Real.exp (-32 * s) / L ≤ 1
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · refine ⟨∅, by simp, ?_, by simp [hn]⟩
      unfold NoRel
      intro s₁ hs₁
      simp at hs₁
    · refine ⟨{0}, ?_, ?_, ?_⟩
      · intro m hm
        rw [Finset.mem_singleton] at hm
        subst hm
        simpa using hn
      · unfold NoRel
        intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12
        rw [Finset.mem_singleton] at hs₁ hs₂
        exact absurd (hs₁.trans hs₂.symm) h12
      · rw [Finset.card_singleton, Nat.cast_one]
        exact hsmall
  push_neg at hsmall
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn] at hsmall
      norm_num at hsmall
    · exact_mod_cast hn
  have eL : Real.exp y = L := by rw [hy, Real.exp_log hLpos]
  have en : Real.exp x = n := by rw [hx, Real.exp_log hnpos]
  have hpos : 0 < x + -32 * s - y := by
    rw [← Real.exp_lt_exp, Real.exp_zero, Real.exp_sub, Real.exp_add, eL, en]
    exact hsmall
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hxpos : 0 < x := by linarith
  have hs2 : s ^ 2 = x * y := by rw [hs]; exact Real.sq_sqrt (mul_pos hxpos hy0).le
  have hs32 : 32 * y < s := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hc), mul_pos hpos hy0, sq_nonneg y]
  have hs16 : 16 < s := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ, S = ⌊s / y⌋₊ := ⟨_, rfl⟩
  have hS1 : (S : ℝ) ≤ s / y := by rw [hSdef]; exact Nat.floor_le (div_nonneg hs0 hy0.le)
  have hS2 : s / y < S + 1 := by rw [hSdef]; exact Nat.lt_floor_add_one _
  have hSy : (S : ℝ) * y ≤ s := (le_div_iff₀ hy0).mp hS1
  have hSy2 : s < (S + 1) * y := (div_lt_iff₀ hy0).mp hS2
  have hS31 : (31 : ℝ) < S := by
    have h := lt_of_mul_lt_mul_right (show (32 : ℝ) * y < (S + 1) * y by linarith) hy0.le
    linarith
  have hSpos : (0 : ℝ) < S := by linarith
  have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (x - y - 3) / S := ⟨_, rfl⟩
  have haS : a * S = x - y - 3 := by rw [ha]; field_simp
  have h2Sy : s ≤ 2 * S * y := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S - 1) hy0.le]
  have hxle : x ≤ 2 * s * S := by
    have h : x * y ≤ (2 * s * S) * y := by nlinarith [mul_le_mul_of_nonneg_left h2Sy hs0]
    exact le_of_mul_le_mul_right h hy0
  have ha2s : a ≤ 2 * s := by
    have h : a * S ≤ (2 * s) * S := by nlinarith
    exact le_of_mul_le_mul_right h hSpos
  have ha7 : 7 + y ≤ a := by
    have h1 : (7 + y) * S * y ≤ (x - y - 3) * y := by
      nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hSy), mul_nonneg hs0 (sub_nonneg.mpr hs32.le),
        mul_nonneg hy0.le (sub_nonneg.mpr hs32.le), mul_nonneg hs0 (sub_nonneg.mpr hy_half.le)]
    have h2 : (7 + y) * S ≤ x - y - 3 := le_of_mul_le_mul_right h1 hy0
    exact le_of_mul_le_mul_right (by rw [haS]; exact h2) hSpos
  have hexpb : 3 + S * (7 + y) + S + 2 * a ≤ 32 * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy_half.le) hSpos.le]
  have h4L : (0 : ℝ) < 4 * L := by positivity
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = ⌊Real.exp a / (4 * L)⌋₊ := ⟨_, rfl⟩
  have hd1 : (d : ℝ) ≤ Real.exp a / (4 * L) := by rw [hddef]; exact Nat.floor_le (by positivity)
  have hd2 : Real.exp a / (4 * L) < d + 1 := by rw [hddef]; exact Nat.lt_floor_add_one _
  have hd1' : (d : ℝ) * (4 * L) ≤ Real.exp a := (le_div_iff₀ h4L).mp hd1
  have hd2' : Real.exp a < (d + 1) * (4 * L) := (div_lt_iff₀ h4L).mp hd2
  have h8Ly : 8 * (L : ℝ) ≤ Real.exp (7 + y) := by
    have h87 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    rw [Real.exp_add, eL]
    nlinarith
  have h8L : 8 * (L : ℝ) ≤ Real.exp a := le_trans h8Ly (Real.exp_le_exp.mpr ha7)
  have hQd : Real.exp a / (8 * L) ≤ d := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hd1r : (1 : ℝ) ≤ d := le_trans ((one_le_div (by positivity)).mpr h8L) hQd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdQ : (d : ℝ) ≤ Real.exp a := by
    nlinarith [mul_nonneg hdpos.le (by linarith : (0 : ℝ) ≤ 4 * L - 1)]
  have hdS : Real.exp a ^ S ≤ (d : ℝ) ^ S * (8 * L) ^ S := by
    have h : (Real.exp a / (8 * L)) ^ S ≤ (d : ℝ) ^ S := by gcongr
    rwa [div_pow, div_le_iff₀ (by positivity)] at h
  have hQS : Real.exp a ^ S = Real.exp (x - y - 3) := by
    rw [← Real.exp_nat_mul, mul_comm, haS]
  have hn_eq : (n : ℝ) = Real.exp a ^ S * L * Real.exp 3 := by
    rw [hQS, ← eL, ← Real.exp_add, ← Real.exp_add, ← en]
    congr 1
    ring
  have hprod : Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2 ≤ Real.exp (32 * s) := by
    have hP : ((8 : ℝ) * L) ^ S ≤ Real.exp (S * (7 + y)) := by
      rw [Real.exp_nat_mul]
      gcongr
    have hSe : (S : ℝ) ≤ Real.exp S := by linarith [Real.add_one_le_exp (S : ℝ)]
    have hQ2 : Real.exp a ^ 2 = Real.exp (2 * a) := by rw [sq, ← Real.exp_add, two_mul]
    calc Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2
        ≤ Real.exp 3 * Real.exp (S * (7 + y)) * Real.exp S * Real.exp (2 * a) := by
          rw [hQ2]
          gcongr
      _ = Real.exp (3 + S * (7 + y) + S + 2 * a) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (32 * s) := Real.exp_le_exp.mpr hexpb
  obtain ⟨k, hk⟩ := Behrend.exists_large_sphere S d
  refine ⟨(Behrend.sphere S d k).image (Behrend.map (4 * L * d)), ?_,
    noRel_image L S d k (by omega), ?_⟩
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨v, hv, rfl⟩ := hm
    obtain ⟨hbox, -⟩ := sphere_mem_lemma hv
    have hdd : d ≤ 4 * L * d := by nlinarith
    have hmlt := map_lt (4 * L * d) v (fun i => lt_of_lt_of_le (hbox i) hdd)
    have hpowle : ((4 : ℝ) * L * d) ^ S ≤ Real.exp a ^ S := by
      gcongr
      linarith
    have hreal : (4 : ℝ) * L * (4 * L * d) ^ S ≤ n := by
      nlinarith [mul_le_mul_of_nonneg_left hpowle h4L.le,
        mul_nonneg (by linarith [Real.add_one_le_exp (3 : ℝ)] : (0 : ℝ) ≤ Real.exp 3 - 4)
          (by positivity : (0 : ℝ) ≤ L * Real.exp a ^ S)]
    have hnat : 4 * L * (4 * L * d) ^ S ≤ n := by exact_mod_cast hreal
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hmlt (by omega)) hnat
  · rw [card_image L S d k (by omega)]
    refine le_trans ?_ hk
    push_cast
    rw [div_le_iff₀ hLpos, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hSpos (pow_pos hdpos 2))]
    calc (n : ℝ) * Real.exp (-32 * s) * (S * d ^ 2)
        ≤ n * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by gcongr
      _ = (Real.exp a ^ S * L * Real.exp 3) * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by
          rw [← hn_eq]
      _ ≤ ((d : ℝ) ^ S * (8 * L) ^ S * L * Real.exp 3) * Real.exp (-32 * s)
            * (S * Real.exp a ^ 2) := by gcongr
      _ = (d : ℝ) ^ S * L * (Real.exp (-32 * s) * (Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2)) := by
          ring
      _ ≤ (d : ℝ) ^ S * L * (Real.exp (-32 * s) * Real.exp (32 * s)) := by gcongr
      _ = (d : ℝ) ^ S * L := by
          rw [← Real.exp_add, show -32 * s + 32 * s = 0 by ring, Real.exp_zero, mul_one]

end Formalism.FrobeniusOrbits
