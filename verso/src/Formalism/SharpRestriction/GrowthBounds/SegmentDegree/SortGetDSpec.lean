import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Establish `hlen : (s.sort (· ≤ ·)).length = s.card` using `Finset.length_sort _`. Establish `hk : (s.sort (· ≤ ·)).length - r < s.card` using `by omega`. Use `set f := s.orderEmbOfFin rfl with hf`. Establish `hget : (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 = f ⟨(s.sort (· ≤ ·)).length - r, hk⟩`. Rewrite using `[hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem]`.

Simplify using `[Fin.getElem_fin]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hget]`. Use `⟨Finset.orderEmbOfFin_mem s rfl _, ?_⟩` and prove the remaining obligations. Establish `hset : s.filter (f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ ≤ ·) = (Finset.univ.filter (fun i : Fin s.card => (s.sort (· ≤ ·)).length - r ≤ i.val ∧ i.val < s.card)).map f.toEmbedding`.

Use extensionality with `y`. Simplify using `only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hle⟩`. Establish `hr : y ∈ Set.range f` using `by rw [hf, Finset.range_orderEmbOfFin]; exact hy`.

Take `⟨i, rfl⟩` from `hr`. Conclude with `⟨i, ⟨f.le_iff_le.1 hle, i.isLt⟩, rfl⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨Finset.orderEmbOfFin_mem s rfl i, f.le_iff_le.2 hi.1⟩`. Rewrite using `[hset, Finset.card_map, card_fin_range _ _ _ le_rfl]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sort_getD_spec (s : Finset ℤ) (r : ℕ) (hr : 0 < r) (hrs : r ≤ s.card) :
    (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ∈ s ∧
      (s.filter ((s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ≤ ·)).card = r := by
  classical
  have hlen : (s.sort (· ≤ ·)).length = s.card := Finset.length_sort _
  have hk : (s.sort (· ≤ ·)).length - r < s.card := by omega
  set f := s.orderEmbOfFin rfl with hf
  have hget : (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 = f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ := by
    rw [hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem]
    · simp [Fin.getElem_fin]
    · omega
  rw [hget]
  refine ⟨Finset.orderEmbOfFin_mem s rfl _, ?_⟩
  have hset : s.filter (f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ ≤ ·) =
      (Finset.univ.filter (fun i : Fin s.card => (s.sort (· ≤ ·)).length - r ≤ i.val ∧ i.val < s.card)).map f.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hle⟩
      have hr : y ∈ Set.range f := by rw [hf, Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, ⟨f.le_iff_le.1 hle, i.isLt⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s rfl i, f.le_iff_le.2 hi.1⟩
  rw [hset, Finset.card_map, card_fin_range _ _ _ le_rfl]
  omega

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Use `set E := segE F j i with hE`. Establish `hmono : StrictMono (segE F j)` using `fun a b hab => by`. Simplify using `only [segE]`. Conclude with `Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)`. Establish `hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x` using `fun x hx => ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩`.

Establish `hlow : ∀ i' < r, F.fr (j - 1) i' < E`. Introduce `i' hi'`. Take `⟨k, hk⟩` from `hsurj _ (frp_mem hV j i' hi')`. Establish `hki` using `idx_w hV k i' hi' hk`. Rewrite using `[← hk]`.

Apply `hmono` to reduce the goal to its premises. Use `show k.val < i.val`. Use linear arithmetic over natural numbers and integers. Establish `hcard : r ≤ ((F.letters j).filter fun z => Even z ∧ z < E).card`. Establish `hsub : (Finset.range r).image (F.fr (j - 1)) ⊆ (F.letters j).filter fun z => Even z ∧ z < E`.

Introduce `x hx`. Simplify using `only [Finset.mem_image, Finset.mem_range] at hx`. Take `⟨i', hi', rfl⟩` from `hx`. Simplify using `only [Finset.mem_filter]`. Conclude with `⟨frp_mem hV j i' hi', (hV.2.2.2.2.1 (j - 1) i' hi').2, hlow i' hi'⟩`.

Establish `hinj : Set.InjOn (F.fr (j - 1)) (Finset.range r)` using `fun a ha b hb h => fr_inj hV _ a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_image_of_injOn hinj, Finset.card_range]`. Use `_ ≤ _ := Finset.card_le_card hsub`. Take `⟨hm, hc⟩` from `sort_getD_spec ((F.letters j).filter fun z => Even z ∧ z < E) r (Nat.pos_of_ne_zero (NeZero.ne r)) hcard`.

Establish `hold : F.oldest j E = (((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).getD ((((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).length - r) 0` using `rfl`. Rewrite using `[hold]`. Simplify using `only [Finset.mem_filter] at hm`. Use `⟨hm.1, hm.2.1, hm.2.2, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[Finset.filter_filter]`.

Use `Eq.trans ?_ hc` and prove the remaining obligations. Conclude with `congrArg Finset.card (Finset.filter_congr (fun z _ => by tauto))`.
-/
theorem oldest_spec (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) (hi : r ≤ i.val) :
    F.oldest j (segE F j i) ∈ F.letters j ∧ Even (F.oldest j (segE F j i)) ∧ F.oldest j (segE F j i) < segE F j i ∧
      ((F.letters j).filter fun z => F.oldest j (segE F j i) ≤ z ∧ z < segE F j i ∧ Even z).card = r := by
  classical
  set E := segE F j i with hE
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hlow : ∀ i' < r, F.fr (j - 1) i' < E := by
    intro i' hi'
    obtain ⟨k, hk⟩ := hsurj _ (frp_mem hV j i' hi')
    have hki := idx_w hV k i' hi' hk
    rw [← hk]
    apply hmono
    show k.val < i.val
    omega
  have hcard : r ≤ ((F.letters j).filter fun z => Even z ∧ z < E).card := by
    have hsub : (Finset.range r).image (F.fr (j - 1)) ⊆ (F.letters j).filter fun z => Even z ∧ z < E := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i', hi', rfl⟩ := hx
      simp only [Finset.mem_filter]
      exact ⟨frp_mem hV j i' hi', (hV.2.2.2.2.1 (j - 1) i' hi').2, hlow i' hi'⟩
    have hinj : Set.InjOn (F.fr (j - 1)) (Finset.range r) := fun a ha b hb h =>
      fr_inj hV _ a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
    calc r = ((Finset.range r).image (F.fr (j - 1))).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨hm, hc⟩ := sort_getD_spec ((F.letters j).filter fun z => Even z ∧ z < E) r
    (Nat.pos_of_ne_zero (NeZero.ne r)) hcard
  have hold : F.oldest j E = (((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).getD
      ((((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).length - r) 0 := rfl
  rw [hold]
  simp only [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  rw [Finset.filter_filter] at hc
  refine Eq.trans ?_ hc
  exact congrArg Finset.card (Finset.filter_congr (fun z _ => by tauto))

/- English proof (translation)
Establish `hmono : StrictMono (segE F j)` using `fun a b hab => by`. Simplify using `only [segE]`. Conclude with `Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)`. Establish `hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x` using `fun x hx => ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩`. Establish `hmem : ∀ l, segE F j l ∈ F.letters j` using `fun l => by`.

Simplify using `only [segE]`. Conclude with `Subtype.mem _`. Establish `hex : ∀ i : Fin (segN F j), ∃ k, r ≤ i.val → segE F j k = F.oldest j (segE F j i)`. Introduce `i`. Distinguish the cases in `h : r ≤ i.val`.

Take `⟨k, hk⟩` from `hsurj _ (oldest_spec hV j i h).1`. Conclude with `⟨k, fun _ => hk⟩`. Conclude with `⟨i, fun h' => absurd h' h⟩`. Use `choose g hg using hex`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Establish `hk` using `hg i hi`. Take `⟨-, hev, hlt, hc⟩` from `oldest_spec hV j i hi`. Use `⟨hk, hmono.lt_iff_lt.1 (by rw [hk]; exact hlt), by simp [segLL, LZ, hk, hev], ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[← hk]`.

Use `Eq.trans ?_ hc` and prove the remaining obligations. Establish `hset : (F.letters j).filter (fun z => segE F j (g i) ≤ z ∧ z < segE F j i ∧ Even z) = (Finset.univ.filter fun l : Fin (segN F j) => g i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).map ⟨segE F j, hmono.injective⟩`. Use extensionality with `z`. Simplify using `only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hz, h1, h2, h3⟩`. Take `⟨l, rfl⟩` from `hsurj z hz`. Conclude with `⟨l, ⟨hmono.le_iff_le.1 h1, hmono.lt_iff_lt.1 h2, by simp [segLL, LZ, h3]⟩, rfl⟩`. Introduce and unpack `⟨l, ⟨h1, h2, h3⟩, rfl⟩`. Conclude with `⟨hmem l, hmono.le_iff_le.2 h1, hmono.lt_iff_lt.2 h2, by simpa [segLL, LZ] using h3⟩`.

Rewrite using `[hset, Finset.card_map]`.
-/
theorem exists_od (hV : F.Valid L₁ N₁) (j : ℤ) : ∃ od : Fin (segN F j) → Fin (segN F j), ∀ i, r ≤ i.val →
    segE F j (od i) = F.oldest j (segE F j i) ∧ od i < i ∧ (segLL F j).vec (od i) = true ∧
      (Finset.univ.filter fun l : Fin (segN F j) => od i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).card = r := by
  classical
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hmem : ∀ l, segE F j l ∈ F.letters j := fun l => by
    simp only [segE]
    exact Subtype.mem _
  have hex : ∀ i : Fin (segN F j), ∃ k, r ≤ i.val → segE F j k = F.oldest j (segE F j i) := by
    intro i
    by_cases h : r ≤ i.val
    · obtain ⟨k, hk⟩ := hsurj _ (oldest_spec hV j i h).1
      exact ⟨k, fun _ => hk⟩
    · exact ⟨i, fun h' => absurd h' h⟩
  choose g hg using hex
  refine ⟨g, ?_⟩
  intro i hi
  have hk := hg i hi
  obtain ⟨-, hev, hlt, hc⟩ := oldest_spec hV j i hi
  refine ⟨hk, hmono.lt_iff_lt.1 (by rw [hk]; exact hlt), by simp [segLL, LZ, hk, hev], ?_⟩
  rw [← hk] at hc
  refine Eq.trans ?_ hc
  have hset : (F.letters j).filter (fun z => segE F j (g i) ≤ z ∧ z < segE F j i ∧ Even z) =
      (Finset.univ.filter fun l : Fin (segN F j) => g i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).map
        ⟨segE F j, hmono.injective⟩ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hz, h1, h2, h3⟩
      obtain ⟨l, rfl⟩ := hsurj z hz
      exact ⟨l, ⟨hmono.le_iff_le.1 h1, hmono.lt_iff_lt.1 h2, by simp [segLL, LZ, h3]⟩, rfl⟩
    · rintro ⟨l, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨hmem l, hmono.le_iff_le.2 h1, hmono.lt_iff_lt.2 h2, by simpa [segLL, LZ] using h3⟩
  rw [hset, Finset.card_map]

end Formalism.MainNotions.SelectionLemmas.Pf.TE
