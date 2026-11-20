import Formalism.GrowthSums.StatementB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

/- English proof (translation)
Introduce `n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood i hi`. Take `⟨_, hTiles, _⟩` from `hgood`. Use `set ℓ := (6 * r + 1) * u with hℓ`. Establish `hℓpos : 0 < ℓ` using `Nat.mul_pos (by omega) (by omega)`. Establish `h2u : 2 * u ≤ ℓ` using `by rw [hℓ]; nlinarith`.

Use `set t := n / ℓ with ht`. Establish `htM : M₀ + 1 ≤ t` using `(Nat.le_div_iff_mul_le hℓpos).2 hn`. Establish `hnt : n < t * ℓ + ℓ`. Establish `h1 : ℓ * t + n % ℓ = n` using `Nat.div_add_mod n ℓ`. Establish `h2` using `Nat.mod_lt n hℓpos`.

Establish `h3 : t * ℓ = ℓ * t` using `Nat.mul_comm _ _`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨si, hsi_lt, hsi_le, hsi_case⟩ : ∃ si, si < t ∧ si * ℓ ≤ i ∧ (i < si * ℓ + ℓ ∨ si + 1 = t) := by`. Distinguish the cases in `hc : i < t * ℓ`. Use `⟨i / ℓ, ?_, Nat.div_mul_le_self i ℓ, Or.inl ?_⟩` and prove the remaining obligations.

Conclude with `(Nat.div_lt_iff_lt_mul hℓpos).2 hc`. Conclude with `Nat.lt_div_mul_add hℓpos`. Use `⟨t - 1, by omega, ?_, Or.inr (by omega)⟩` and prove the remaining obligations. Establish `: (t - 1) * ℓ ≤ t * ℓ` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers.

Establish `htpos : 0 < t` using `by omega`. Take `⟨j, hj, hM⟩` from `hTiles ((si + 1) % t) (Nat.mod_lt _ htpos)`. Rewrite `hM` using `[Nat.mod_add_mod]`. Take `⟨s, hs⟩ : ∃ s, s = (si + 1 + j) % t` from `⟨_, rfl⟩`. Rewrite `hM` using `[← hs]`.

Establish `hslt : s < t` using `hs ▸ Nat.mod_lt _ htpos`. Establish `hsc : s = si + 1 + j ∨ s + t = si + 1 + j`. Distinguish the cases in `hc : si + 1 + j < t`. Use `left`. Rewrite using `[hs, Nat.mod_eq_of_lt hc]`.

Use `right`. Rewrite using `[hs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hxe⟩` from `(hM 2 (by omega) (by omega)).2 even_two`. Establish `hxmem : x ∈ T ∩ cell r u s 2` using `by rw [hx]; exact mem_singleton_self x`.

Rewrite `hxmem` using `[mem_inter]`. Take `⟨hxT, hxc⟩` from `hxmem`. Simplify using `only [cell, mem_Ico] at hxc`. Rewrite `hxc` using `[← hℓ]`. Establish `hxn : x < n` using `mem_range.1 (hT hxT)`.

Establish `hjl : j * ℓ ≤ M₀ * ℓ` using `Nat.mul_le_mul_right _ hj`. Establish `hG5 : (M₀ + 5) * ℓ = M₀ * ℓ + 5 * ℓ` using `by ring`. Establish `key : ∃ D, 1 ≤ D ∧ D ≤ G' ∧ (i + D) % n = x`. Break down `hsc with hA | hB` into its components or cases. Establish `e : s * ℓ = si * ℓ + ℓ + j * ℓ` using `by rw [hA]; ring`.

Use `⟨x - i, by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]`. Establish `e : s * ℓ + t * ℓ = si * ℓ + ℓ + j * ℓ` using `by rw [← add_mul, hB]; ring`. Establish `hssi : s ≤ si` using `by omega`. Establish `e2 : s * ℓ ≤ si * ℓ` using `Nat.mul_le_mul_right _ hssi`.

Distinguish the cases in `hxi : i < x`. Use `⟨x - i, by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]`. Use `⟨x + n - i, by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hxn]`.

Take `⟨D, hD1, hD2, hDx⟩` from `key`. Conclude with `⟨D, mem_Icc.2 ⟨hD1, hD2⟩, by rw [hDx]; exact ⟨hxT, hxe⟩⟩`.
-/
theorem next_even_top_holds : NextEvenTop := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood i hi
  obtain ⟨_, hTiles, _⟩ := hgood
  set ℓ := (6 * r + 1) * u with hℓ
  have hℓpos : 0 < ℓ := Nat.mul_pos (by omega) (by omega)
  have h2u : 2 * u ≤ ℓ := by rw [hℓ]; nlinarith
  set t := n / ℓ with ht
  have htM : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hℓpos).2 hn
  have hnt : n < t * ℓ + ℓ := by
    have h1 : ℓ * t + n % ℓ = n := Nat.div_add_mod n ℓ
    have h2 := Nat.mod_lt n hℓpos
    have h3 : t * ℓ = ℓ * t := Nat.mul_comm _ _
    omega
  obtain ⟨si, hsi_lt, hsi_le, hsi_case⟩ :
      ∃ si, si < t ∧ si * ℓ ≤ i ∧ (i < si * ℓ + ℓ ∨ si + 1 = t) := by
    by_cases hc : i < t * ℓ
    · refine ⟨i / ℓ, ?_, Nat.div_mul_le_self i ℓ, Or.inl ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hℓpos).2 hc
      · exact Nat.lt_div_mul_add hℓpos
    · refine ⟨t - 1, by omega, ?_, Or.inr (by omega)⟩
      have : (t - 1) * ℓ ≤ t * ℓ := Nat.mul_le_mul_right _ (by omega)
      omega
  have htpos : 0 < t := by omega
  obtain ⟨j, hj, hM⟩ := hTiles ((si + 1) % t) (Nat.mod_lt _ htpos)
  rw [Nat.mod_add_mod] at hM
  obtain ⟨s, hs⟩ : ∃ s, s = (si + 1 + j) % t := ⟨_, rfl⟩
  rw [← hs] at hM
  have hslt : s < t := hs ▸ Nat.mod_lt _ htpos
  have hsc : s = si + 1 + j ∨ s + t = si + 1 + j := by
    by_cases hc : si + 1 + j < t
    · left; rw [hs, Nat.mod_eq_of_lt hc]
    · right
      rw [hs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  obtain ⟨x, hx, hxe⟩ := (hM 2 (by omega) (by omega)).2 even_two
  have hxmem : x ∈ T ∩ cell r u s 2 := by rw [hx]; exact mem_singleton_self x
  rw [mem_inter] at hxmem
  obtain ⟨hxT, hxc⟩ := hxmem
  simp only [cell, mem_Ico] at hxc
  rw [← hℓ] at hxc
  have hxn : x < n := mem_range.1 (hT hxT)
  have hjl : j * ℓ ≤ M₀ * ℓ := Nat.mul_le_mul_right _ hj
  have hG5 : (M₀ + 5) * ℓ = M₀ * ℓ + 5 * ℓ := by ring
  have key : ∃ D, 1 ≤ D ∧ D ≤ G' ∧ (i + D) % n = x := by
    rcases hsc with hA | hB
    · have e : s * ℓ = si * ℓ + ℓ + j * ℓ := by rw [hA]; ring
      refine ⟨x - i, by omega, by omega, ?_⟩
      rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
    · have e : s * ℓ + t * ℓ = si * ℓ + ℓ + j * ℓ := by rw [← add_mul, hB]; ring
      have hssi : s ≤ si := by omega
      have e2 : s * ℓ ≤ si * ℓ := Nat.mul_le_mul_right _ hssi
      by_cases hxi : i < x
      · refine ⟨x - i, by omega, by omega, ?_⟩
        rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
      · refine ⟨x + n - i, by omega, by omega, ?_⟩
        rw [show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hxn]
  obtain ⟨D, hD1, hD2, hDx⟩ := key
  exact ⟨D, mem_Icc.2 ⟨hD1, hD2⟩, by rw [hDx]; exact ⟨hxT, hxe⟩⟩

/- English proof (translation)
Introduce `n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood`. Establish `hnext` using `next_even_top_holds n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood`. Take `⟨_, _, hInt⟩` from `hgood`. Establish `hℓpos : 0 < (6 * r + 1) * u` using `Nat.mul_pos (by omega) (by omega)`. Establish `hnpos : 0 < n` using `lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hn`.

Establish `hGpos : 0 < G'` using `lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hG`. Prove the components needed by the constructor for the conclusion. Establish `hsub : range n ⊆ (T ×ˢ Icc 1 G').image (fun p => (p.1 + n * G' - p.2) % n)`. Introduce `i hi`. Rewrite `hi` using `[mem_range]`.

Take `⟨D, hD, hDT, -⟩` from `hnext i hi`. Rewrite `hD` using `[mem_Icc]`. Rewrite using `[mem_image]`. Use `⟨((i + D) % n, D), mem_product.2 ⟨hDT, mem_Icc.2 hD⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Establish `h1` using `Nat.div_add_mod (i + D) n`. Take `⟨q, hq⟩ : ∃ q, q = (i + D) / n` from `⟨_, rfl⟩`. Take `⟨x, hx⟩ : ∃ x, x = (i + D) % n` from `⟨_, rfl⟩`. Rewrite `h1` using `[← hq, ← hx]`. Rewrite using `[← hx]`.

Establish `hqG : q ≤ G'`. Assume the negation of the conclusion as `hc`. Establish `: n * (G' + 1) ≤ n * q` using `Nat.mul_le_mul_left _ (by omega)`. Establish `: n * (G' + 1) = n * G' + n` using `by ring`. Establish `: G' ≤ n * G'` using `Nat.le_mul_of_pos_left _ hnpos`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : n * (G' - q) = n * G' - n * q` using `Nat.mul_sub n G' q`. Establish `h3 : n * q ≤ n * G'` using `Nat.mul_le_mul_left _ hqG`. Establish `h4 : x + n * G' - D = i + n * (G' - q)` using `by omega`. Rewrite using `[h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcov : T ⊆ (T.image (fun p => p / G')).biUnion (fun c => T ∩ window n (c * G') G')`. Introduce `p hp`. Rewrite using `[mem_biUnion]`. Use `⟨p / G', mem_image_of_mem _ hp, mem_inter.2 ⟨hp, ?_⟩⟩` and prove the remaining obligations.

Establish `hpn : p < n` using `mem_range.1 (hT hp)`. Unfold `window`. Rewrite using `[mem_image]`. Establish `h1` using `Nat.lt_div_mul_add (a := p) hGpos`. Establish `h2` using `Nat.div_mul_le_self p G'`.

Use `⟨p - p / G' * G', mem_range.2 (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[show p / G' * G' + (p - p / G' * G') = p by omega, Nat.mod_eq_of_lt hpn]`. Establish `hcard : T.card ≤ (T.image (fun p => p / G')).card * N₁`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum` to reduce the goal to its premises.

Introduce `c hc`. Take `⟨p, hp, rfl⟩` from `mem_image.1 hc`. Apply `hInt` to reduce the goal to its premises. Use `Nat.div_mul_le_self p G'` as an intermediate fact. Use `mem_range.1 (hT hp)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `_ = _ := by rw [sum_const, smul_eq_mul]`. Establish `himg : (T.image (fun p => p / G')).card ≤ n / G' + 1`. Combine the equalities or inequalities in the displayed calculation. Apply `card_le_card` to reduce the goal to its premises.

Introduce `c hc`. Take `⟨p, hp, rfl⟩` from `mem_image.1 hc`. Rewrite using `[mem_range]`. Use `Nat.div_le_div_right (c := G') (mem_range.1 (hT hp)).le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `_ = _ := card_range _`. Establish `h5 : (n / G' + 1) * G' ≤ n + G'`. Use `Nat.div_mul_le_self n G'` as an intermediate fact. Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem top_count_holds : TopCount := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  have hnext := next_even_top_holds n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  obtain ⟨_, _, hInt⟩ := hgood
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hn
  have hGpos : 0 < G' := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hG
  constructor
  · have hsub : range n ⊆ (T ×ˢ Icc 1 G').image (fun p => (p.1 + n * G' - p.2) % n) := by
      intro i hi
      rw [mem_range] at hi
      obtain ⟨D, hD, hDT, -⟩ := hnext i hi
      rw [mem_Icc] at hD
      rw [mem_image]
      refine ⟨((i + D) % n, D), mem_product.2 ⟨hDT, mem_Icc.2 hD⟩, ?_⟩
      simp only
      have h1 := Nat.div_add_mod (i + D) n
      obtain ⟨q, hq⟩ : ∃ q, q = (i + D) / n := ⟨_, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, x = (i + D) % n := ⟨_, rfl⟩
      rw [← hq, ← hx] at h1
      rw [← hx]
      have hqG : q ≤ G' := by
        by_contra hc
        have : n * (G' + 1) ≤ n * q := Nat.mul_le_mul_left _ (by omega)
        have : n * (G' + 1) = n * G' + n := by ring
        have : G' ≤ n * G' := Nat.le_mul_of_pos_left _ hnpos
        omega
      have h2 : n * (G' - q) = n * G' - n * q := Nat.mul_sub n G' q
      have h3 : n * q ≤ n * G' := Nat.mul_le_mul_left _ hqG
      have h4 : x + n * G' - D = i + n * (G' - q) := by omega
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    calc n = (range n).card := (card_range n).symm
      _ ≤ _ := card_le_card hsub
      _ ≤ (T ×ˢ Icc 1 G').card := card_image_le
      _ = T.card * G' := by rw [card_product, Nat.card_Icc]; simp
  · have hcov : T ⊆ (T.image (fun p => p / G')).biUnion
        (fun c => T ∩ window n (c * G') G') := by
      intro p hp
      rw [mem_biUnion]
      refine ⟨p / G', mem_image_of_mem _ hp, mem_inter.2 ⟨hp, ?_⟩⟩
      have hpn : p < n := mem_range.1 (hT hp)
      unfold window
      rw [mem_image]
      have h1 := Nat.lt_div_mul_add (a := p) hGpos
      have h2 := Nat.div_mul_le_self p G'
      refine ⟨p - p / G' * G', mem_range.2 (by omega), ?_⟩
      rw [show p / G' * G' + (p - p / G' * G') = p by omega, Nat.mod_eq_of_lt hpn]
    have hcard : T.card ≤ (T.image (fun p => p / G')).card * N₁ := by
      calc T.card ≤ _ := card_le_card hcov
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), (T ∩ window n (c * G') G').card :=
            card_biUnion_le
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), N₁ := by
            apply sum_le_sum
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            apply hInt
            have := Nat.div_mul_le_self p G'
            have := mem_range.1 (hT hp)
            omega
        _ = _ := by rw [sum_const, smul_eq_mul]
    have himg : (T.image (fun p => p / G')).card ≤ n / G' + 1 := by
      calc _ ≤ (range (n / G' + 1)).card := by
            apply card_le_card
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            rw [mem_range]
            have := Nat.div_le_div_right (c := G') (mem_range.1 (hT hp)).le
            omega
        _ = _ := card_range _
    have h5 : (n / G' + 1) * G' ≤ n + G' := by
      have := Nat.div_mul_le_self n G'
      rw [add_mul, one_mul]; omega
    calc T.card * G' ≤ ((n / G' + 1) * N₁) * G' :=
          Nat.mul_le_mul_right _ (hcard.trans (Nat.mul_le_mul_right _ himg))
      _ = N₁ * ((n / G' + 1) * G') := by ring
      _ ≤ N₁ * (n + G') := Nat.mul_le_mul_left _ h5

end Formalism.GrowthSums
