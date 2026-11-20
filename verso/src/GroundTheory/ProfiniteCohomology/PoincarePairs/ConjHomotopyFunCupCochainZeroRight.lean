import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula.ConjHomotopy
import GroundTheory.TateCohomology.CupCochains
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct Finset GroundTheory.GroupCoh

universe u

section Sequences

variable {Γ : Type*} [Group Γ]

def seqProd (F : ℕ → Γ) : ℕ → Γ
  | 0 => 1
  | r + 1 => seqProd F r * F r

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem seqProd_succ (F : ℕ → Γ) (r : ℕ) : seqProd F (r + 1) = seqProd F r * F r :=
  rfl

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact Fin.partialProd_zero _`. Consider the case `succ r ih`. Establish `h1` using `Fin.partialProd_succ (seqTuple n F) ⟨r, by omega⟩`. Simplify using `only [Fin.succ_mk, Fin.castSucc_mk] at h1`.

Rewrite using `[h1, ih (by omega), seqProd_succ]`. Both sides reduce to the same expression.
-/
theorem partialProd_seqTuple {n : ℕ} (F : ℕ → Γ) (r : ℕ) (hr : r < n + 1) :
    Fin.partialProd (seqTuple n F) ⟨r, hr⟩ = seqProd F r := by
  induction r with
  | zero => exact Fin.partialProd_zero _
  | succ r ih =>
    have h1 := Fin.partialProd_succ (seqTuple n F) ⟨r, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1
    rw [h1, ih (by omega), seqProd_succ]
    rfl

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rfl`. Consider the case `succ r ih`. Rewrite using `[seqProd_succ, seqProd_succ, ih (by omega)]`. Simplify using `only [prismSeq, if_pos (show r < i by omega)]`.
-/
theorem seqProd_prismSeq_of_ge (g : Γ) {i r : ℕ} (hr : r ≤ i) (F : ℕ → Γ) :
    seqProd (prismSeq g i F) r = seqProd F r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [seqProd_succ, seqProd_succ, ih (by omega)]
    simp only [prismSeq, if_pos (show r < i by omega)]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Take `rfl : i = 0` from `by omega`. Simplify using `[seqProd, prismSeq]`. Consider the case `succ r ih`.

Break down `Nat.lt_or_ge i (r + 1) with h | h` into its components or cases. Rewrite using `[seqProd_succ, ih (by omega), seqProd_succ]`. Simplify using `only [prismSeq, if_neg (show ¬ r + 1 < i by omega), if_neg (show r + 1 ≠ i by omega), Nat.add_sub_cancel]`. Use `group`. Take `rfl : i = r + 1` from `by omega`.

Rewrite using `[seqProd_succ, seqProd_prismSeq_of_ge g le_rfl, seqProd_succ]`. Simplify using `[prismSeq]`.
-/
theorem seqProd_prismSeq_of_le (g : Γ) {i r : ℕ} (hi : i ≤ r) (F : ℕ → Γ) :
    seqProd (prismSeq g i F) (r + 1) = seqProd F r * g := by
  induction r with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [seqProd, prismSeq]
  | succ r ih =>
    rcases Nat.lt_or_ge i (r + 1) with h | h
    · rw [seqProd_succ, ih (by omega), seqProd_succ]
      simp only [prismSeq, if_neg (show ¬ r + 1 < i by omega), if_neg (show r + 1 ≠ i by omega),
        Nat.add_sub_cancel]
      group
    · obtain rfl : i = r + 1 := by omega
      rw [seqProd_succ, seqProd_prismSeq_of_ge g le_rfl, seqProd_succ]
      simp [prismSeq]

end Sequences

section Cup

variable {k Γ : Type u} [CommRing k] [Group Γ] {A B : Rep.{u} k Γ}

/- English proof (translation)
Rewrite using `[cupCochain_apply, partialProd_seqTuple]`. Both sides reduce to the same expression.
-/
theorem cupCochain_seqTuple {r s n : ℕ} (h : r + s = n) (F : (Fin r → Γ) → A)
    (E : (Fin s → Γ) → B) (Y : ℕ → Γ) :
    cupCochain h F E (seqTuple n Y) =
      F (seqTuple r Y) ⊗ₜ[k] B.ρ (seqProd Y r) (E (seqTuple s fun l => Y (r + l))) := by
  rw [cupCochain_apply, partialProd_seqTuple]
  rfl

/- English proof (translation)
Rewrite using `[cupCochain_seqTuple, seqProd_prismSeq_of_le g hi, map_mul, Module.End.mul_apply]`. Use `congr 2`. Express the relevant statement in the definitionally equal form `B.ρ g (E _) = B.ρ g (E _)`. Use `congr 2`. Use function extensionality and compare the values at `l`.

Express the relevant statement in the definitionally equal form `prismSeq g i Y (r + 1 + l) = g⁻¹ * Y (r + l) * g`. Simplify using `only [prismSeq, if_neg (show ¬ r + 1 + l < i by omega), if_neg (show r + 1 + (l : ℕ) ≠ i by omega)]`. Use `congr 3`. Use linear arithmetic over natural numbers and integers.
-/
theorem cupCochain_seqTuple_prismSeq_of_le (g : Γ) {r s n : ℕ} (h : r + 1 + s = n)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin s → Γ) → B) (Y : ℕ → Γ) {i : ℕ} (hi : i ≤ r) :
    cupCochain h F E (seqTuple n (prismSeq g i Y)) =
      F (seqTuple (r + 1) (prismSeq g i Y)) ⊗ₜ[k] B.ρ (seqProd Y r)
        (conjCochainFun B g E (seqTuple s fun l => Y (r + l))) := by
  rw [cupCochain_seqTuple, seqProd_prismSeq_of_le g hi, map_mul, Module.End.mul_apply]
  congr 2
  change B.ρ g (E _) = B.ρ g (E _)
  congr 2
  funext l
  change prismSeq g i Y (r + 1 + l) = g⁻¹ * Y (r + l) * g
  simp only [prismSeq, if_neg (show ¬ r + 1 + l < i by omega),
    if_neg (show r + 1 + (l : ℕ) ≠ i by omega)]
  congr 3
  omega

/- English proof (translation)
Rewrite using `[cupCochain_seqTuple, seqProd_prismSeq_of_ge g (by omega)]`. Use `congr 1`. Use `congr 1`. Conclude with `seqTuple_congr fun l hl => by simp only [prismSeq, if_pos (show l < r + j by omega)]`. Use `congr 2`.

Use `seqTuple_congr fun l hl => ?_` and prove the remaining obligations. Simplify using `only [prismSeq]`. Use `split_ifs with h1 h2 h3 h4 h5 h6`. Apply the tactic sequence `all_goals first | omega | rfl | (rw [show r + l - 1 = r + (l - 1) by omega])`.
-/
theorem cupCochain_seqTuple_prismSeq_add (g : Γ) {r s n : ℕ} (h : r + (s + 1) = n)
    (F : (Fin r → Γ) → A) (E : (Fin (s + 1) → Γ) → B) (Y : ℕ → Γ) (j : ℕ) :
    cupCochain h F E (seqTuple n (prismSeq g (r + j) Y)) =
      F (seqTuple r Y) ⊗ₜ[k] B.ρ (seqProd Y r)
        (E (seqTuple (s + 1) (prismSeq g j fun l => Y (r + l)))) := by
  rw [cupCochain_seqTuple, seqProd_prismSeq_of_ge g (by omega)]
  congr 1
  · congr 1
    exact seqTuple_congr fun l hl => by simp only [prismSeq, if_pos (show l < r + j by omega)]
  · congr 2
    refine seqTuple_congr fun l hl => ?_
    simp only [prismSeq]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first | omega | rfl | (rw [show r + l - 1 = r + (l - 1) by omega])

end Cup

section Leibniz

variable {k Γ : Type u} [CommRing k] [Group Γ] {A B : Rep.{u} k Γ}

/- English proof (translation)
Take `rfl : m = r + 1 + s` from `by omega`. Use function extensionality and compare the values at `γ`. Rewrite using `[← seqTuple_tupleSeq γ]`. Use `set Y := tupleSeq γ`. Rewrite using `[Pi.add_apply, Pi.smul_apply, conjHomotopyFun_seqTuple, cupCochain_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, conjHomotopyFun_seqTuple, show range (r + 1 + s + 1) = range ((r + 1) + (s + 1)) from rfl, sum_range_add]`.

Use `congr 1`. Rewrite using `[sum_tmul]`. Use `sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']`. Rewrite using `[map_sum, tmul_sum, smul_sum]`.

Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[cupCochain_seqTuple_prismSeq_add g h F E Y j, map_smul, tmul_smul, smul_smul, pow_add]`.
-/
theorem conjHomotopyFun_cupCochain (g : Γ) {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin (s + 1) → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show r + (s + 1) = m by omega) (conjHomotopyFun A g r F) (conjCochainFun B g E) +
        (-1 : k) ^ (r + 1) • cupCochain (show r + 1 + s = m by omega) F (conjHomotopyFun B g s E) := by
  obtain rfl : m = r + 1 + s := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [Pi.add_apply, Pi.smul_apply, conjHomotopyFun_seqTuple, cupCochain_seqTuple,
    cupCochain_seqTuple, conjHomotopyFun_seqTuple, conjHomotopyFun_seqTuple,
    show range (r + 1 + s + 1) = range ((r + 1) + (s + 1)) from rfl, sum_range_add]
  congr 1
  · rw [sum_tmul]
    refine sum_congr rfl fun i hi => ?_
    rw [cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']
  · rw [map_sum, tmul_sum, smul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [cupCochain_seqTuple_prismSeq_add g h F E Y j, map_smul, tmul_smul, smul_smul, pow_add]

/- English proof (translation)
Take `rfl : m = s` from `by omega`. Use function extensionality and compare the values at `γ`. Rewrite using `[← seqTuple_tupleSeq γ]`. Use `set Y := tupleSeq γ`. Rewrite using `[conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, map_sum, tmul_sum]`.

Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e` using `cupCochain_seqTuple_prismSeq_add g h F E Y j`. Rewrite `e` using `[zero_add]`. Rewrite using `[e, map_smul, tmul_smul]`.
-/
theorem conjHomotopyFun_cupCochain_zero_left (g : Γ) {s m : ℕ} (h : 0 + (s + 1) = m + 1)
    (F : (Fin 0 → Γ) → A) (E : (Fin (s + 1) → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show 0 + s = m by omega) F (conjHomotopyFun B g s E) := by
  obtain rfl : m = s := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, map_sum, tmul_sum]
  refine sum_congr rfl fun j _ => ?_
  have e := cupCochain_seqTuple_prismSeq_add g h F E Y j
  rw [zero_add] at e
  rw [e, map_smul, tmul_smul]

/- English proof (translation)
Take `rfl : m = r` from `by omega`. Use function extensionality and compare the values at `γ`. Rewrite using `[← seqTuple_tupleSeq γ]`. Use `set Y := tupleSeq γ`. Rewrite using `[conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, sum_tmul]`.

Use `sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']`.
-/
theorem conjHomotopyFun_cupCochain_zero_right (g : Γ) {r m : ℕ} (h : r + 1 + 0 = m + 1)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin 0 → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show r + 0 = m by omega) (conjHomotopyFun A g r F) (conjCochainFun B g E) := by
  obtain rfl : m = r := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, sum_tmul]
  refine sum_congr rfl fun i hi => ?_
  rw [cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']

end Leibniz

end GroundTheory.ProfCoh
