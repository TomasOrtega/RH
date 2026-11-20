import Formalism.GrowthSums.StatementB

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

/- English proof (translation)
Introduce `n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood s s' f f' hs hs' hm hm' hsucc hf hfim hf' hfim'`. Take `⟨_, hTiles, hInt⟩` from `hgood`. Introduce `a b D`. Establish `haT : a ∈ T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))`. Rewrite using `[hfim]`.

Conclude with `mem_image_of_mem _ (mem_univ _)`. Establish `hbT : b ∈ T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u))`. Rewrite using `[hfim']`. Conclude with `mem_image_of_mem _ (mem_univ _)`. Establish `hD : D = if s < s' then b - a else b + n - a` using `rfl`.

Use `clear_value a b D`. Use `set E := (6 * r + 1) * u with hEdef`. Use `set t := n / E with htdef`. Establish `hE : 0 < E` using `Nat.mul_pos (by omega) (by omega)`. Establish `ht1 : M₀ + 1 ≤ t` using `(Nat.le_div_iff_mul_le hE).2 hn`.

Establish `htE : t * E ≤ n` using `Nat.div_mul_le_self n E`. Establish `hnE : n < t * E + E`. Establish `h1 : E * t + n % E = n` using `Nat.div_add_mod n E`. Establish `h2` using `Nat.mod_lt n hE`. Rewrite `h1` using `[mul_comm]`.

Use linear arithmetic over natural numbers and integers. Rewrite `haT`, `hbT` using `[mem_inter, mem_Ico]`. Take `⟨haT, ha1, ha2⟩` from `haT`. Take `⟨hbT, hb1, hb2⟩` from `hbT`. Rewrite `ha2`, `hb2` using `[add_one_mul]`.

Establish `hgap : (if s < s' then s' - s else s' + t - s) ≤ M₀ + 1`. Take `⟨j, hj, hmj⟩` from `hTiles ((s + 1) % t) (Nat.mod_lt _ (by omega))`. Rewrite `hmj` using `[Nat.mod_add_mod, show s + 1 + j = s + (j + 1) by omega]`. Assume the negation of the conclusion as `hc`. Conclude with `hsucc (j + 1) (by omega) (by omega) hmj`.

Establish `hst : (s + 1) * E ≤ t * E` using `Nat.mul_le_mul_right _ (by omega)`. Establish `hs't : (s' + 1) * E ≤ t * E` using `Nat.mul_le_mul_right _ (by omega)`. Rewrite `hst`, `hs't` using `[add_one_mul]`. Establish `hGE : M₀ * E + 5 * E ≤ G'` using `by rw [← add_mul]; exact hG`. Establish `hDG : D < G' ∧ (a + D) % n = b`.

Distinguish the cases in `hss : s < s'`. Rewrite `hgap`, `hD` using `[if_pos hss]`. Establish `hg : s' * E = s * E + (s' - s) * E` using `by rw [← add_mul]; congr 1; omega`. Establish `hgE : (s' - s) * E ≤ M₀ * E + E`. Rewrite using `[← add_one_mul]`.

Conclude with `Nat.mul_le_mul_right _ hgap`. Establish `hsE : s * E + E ≤ s' * E` using `by rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hss`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hD, show a + (b - a) = b by omega]`. Conclude with `Nat.mod_eq_of_lt (by omega)`.

Rewrite `hgap`, `hD` using `[if_neg hss]`. Establish `hg : s' * E + t * E = s * E + (s' + t - s) * E`. Rewrite using `[← add_mul, ← add_mul]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `hgE : (s' + t - s) * E ≤ M₀ * E + E`. Rewrite using `[← add_one_mul]`. Conclude with `Nat.mul_le_mul_right _ hgap`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hD, show a + (b + n - a) = b + n by omega, Nat.add_mod_right]`.

Conclude with `Nat.mod_eq_of_lt (by omega)`. Use `⟨hDG.1, hDG.2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `card_le_card` to reduce the goal to its premises. Apply `inter_subset_inter_left` to reduce the goal to its premises.

Unfold `window`. Apply `image_subset_image` to reduce the goal to its premises. Establish `h3` using `hDG.1`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_range]`.

Use linear arithmetic over natural numbers and integers. Use `_ ≤ N₁ := hInt a (by omega)`.
-/
theorem segment_bound_holds : SegmentBound := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood s s' f f' hs hs' hm hm' hsucc hf hfim hf' hfim'
  obtain ⟨_, hTiles, hInt⟩ := hgood
  intro a b D
  have haT : a ∈ T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) := by
    rw [hfim]; exact mem_image_of_mem _ (mem_univ _)
  have hbT : b ∈ T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u)) := by
    rw [hfim']; exact mem_image_of_mem _ (mem_univ _)
  have hD : D = if s < s' then b - a else b + n - a := rfl
  clear_value a b D
  set E := (6 * r + 1) * u with hEdef
  set t := n / E with htdef
  have hE : 0 < E := Nat.mul_pos (by omega) (by omega)
  have ht1 : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hE).2 hn
  have htE : t * E ≤ n := Nat.div_mul_le_self n E
  have hnE : n < t * E + E := by
    have h1 : E * t + n % E = n := Nat.div_add_mod n E
    have h2 := Nat.mod_lt n hE
    rw [mul_comm] at h1
    omega
  rw [mem_inter, mem_Ico] at haT hbT
  obtain ⟨haT, ha1, ha2⟩ := haT
  obtain ⟨hbT, hb1, hb2⟩ := hbT
  rw [add_one_mul] at ha2 hb2

  have hgap : (if s < s' then s' - s else s' + t - s) ≤ M₀ + 1 := by
    obtain ⟨j, hj, hmj⟩ := hTiles ((s + 1) % t) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show s + 1 + j = s + (j + 1) by omega] at hmj
    by_contra hc
    exact hsucc (j + 1) (by omega) (by omega) hmj

  have hst : (s + 1) * E ≤ t * E := Nat.mul_le_mul_right _ (by omega)
  have hs't : (s' + 1) * E ≤ t * E := Nat.mul_le_mul_right _ (by omega)
  rw [add_one_mul] at hst hs't
  have hGE : M₀ * E + 5 * E ≤ G' := by rw [← add_mul]; exact hG
  have hDG : D < G' ∧ (a + D) % n = b := by
    by_cases hss : s < s'
    · rw [if_pos hss] at hgap hD
      have hg : s' * E = s * E + (s' - s) * E := by rw [← add_mul]; congr 1; omega
      have hgE : (s' - s) * E ≤ M₀ * E + E := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hgap
      have hsE : s * E + E ≤ s' * E := by rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hss
      refine ⟨by omega, ?_⟩
      rw [hD, show a + (b - a) = b by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [if_neg hss] at hgap hD
      have hg : s' * E + t * E = s * E + (s' + t - s) * E := by
        rw [← add_mul, ← add_mul]; congr 1; omega
      have hgE : (s' + t - s) * E ≤ M₀ * E + E := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hgap
      refine ⟨by omega, ?_⟩
      rw [hD, show a + (b + n - a) = b + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hDG.1, hDG.2, ?_⟩
  calc (T ∩ (range (D + 1)).image (fun j => (a + j) % n)).card
      ≤ (T ∩ window n a G').card := by
        apply card_le_card
        apply inter_subset_inter_left
        unfold window
        apply image_subset_image
        have h3 := hDG.1
        intro x hx
        rw [mem_range] at hx ⊢
        omega
    _ ≤ N₁ := hInt a (by omega)

end Formalism.GrowthSums
