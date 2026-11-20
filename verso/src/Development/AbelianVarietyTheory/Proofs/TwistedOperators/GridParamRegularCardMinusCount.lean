import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Finset
open GlobalTheory.SignedHC

namespace GlobalTheory.PiCounts

variable {G : GridData}

/- English proof (translation)
Introduce `i j h`. Establish `e` using `G.a_sub_a i j`. Rewrite `e` using `[h, sub_self]`. Establish `hg' : (G.ga : ℚ) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `: ((j : ℚ) - i) = 0`.

Break down `mul_eq_zero.1 e.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hg'`. Establish `: (j : ℚ) = i` using `by linarith`. Conclude with `this.symm` after adjusting the coercions.
-/
theorem a_injective (hg : 0 < G.ga) : Function.Injective G.a := by
  intro i j h
  have e := G.a_sub_a i j
  rw [h, sub_self] at e
  have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have : ((j : ℚ) - i) = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact h
    · exact absurd h hg'
  have : (j : ℚ) = i := by linarith
  exact_mod_cast this.symm

/- English proof (translation)
Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Establish `: (0 : ℚ) ≤ G.ga` using `by positivity`. Combine the linear relations using `[GlobalTheory.ChiGrid.a_add_le (G := G) h]`.
-/
theorem a_anti {i j : ℕ} (h : i ≤ j) : G.a j ≤ G.a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ G.ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h]

/- English proof (translation)
Rewrite using `[GridData.tops, card_image_of_injective _ (a_injective hg), card_range]`.
-/
theorem card_tops (hg : 0 < G.ga) : G.tops.card = G.m + 1 := by
  rw [GridData.tops, card_image_of_injective _ (a_injective hg), card_range]

/- English proof (translation)
Rewrite using `[GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]`. Use linear arithmetic over natural numbers and integers. Introduce `i hi j hj h`. Establish `hi` using `mem_Icc.1 (mem_coe.1 hi)`. Establish `hj` using `mem_Icc.1 (mem_coe.1 hj)`.

Establish `e : G.v i = G.v j`. Establish `: (G.v i : ℚ) = G.v j` using `by simp only [GridData.vHalf] at h; linarith`. Conclude with `this` after adjusting the coercions. Break down `lt_trichotomy i j with h' | h' | h'` into its components or cases. Conclude with `absurd e (G.v_anti i j hi.1 h' hj.2).ne'`.

Conclude with `h'`. Conclude with `absurd e (G.v_anti j i hj.1 h' hi.2).ne`.
-/
theorem card_cloudHalf : G.cloudHalf.card = G.k - 1 := by
  rw [GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : G.v i = G.v j := by
      have : (G.v i : ℚ) = G.v j := by simp only [GridData.vHalf] at h; linarith
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e (G.v_anti i j hi.1 h' hj.2).ne'
    · exact h'
    · exact absurd e (G.v_anti j i hj.1 h' hi.2).ne

/- English proof (translation)
Rewrite using `[card_biUnion]`. Establish `: ∀ u ∈ Icc (G.m - i + 1) G.m, (G.blockC' u).card = G.s - 1` using `fun u _ => card_block _ _`. Rewrite using `[sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Introduce `u hu v hv huv`. Establish `hu` using `mem_Icc.1 (mem_coe.1 hu)`. Establish `hv` using `mem_Icc.1 (mem_coe.1 hv)`. Use `disjoint_left.2 fun x h1 h2 => ?_` and prove the remaining obligations. Establish `b1` using `GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h1`.

Establish `b2` using `GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hv.2 h2`. Apply the tactic sequence `rcases lt_or_gt_of_ne huv with h | h <;>`. Combine the linear relations using `[GlobalTheory.ChiGrid.a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]`.
-/
theorem card_Cs' (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card = i * (G.s - 1) := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc (G.m - i + 1) G.m, (G.blockC' u).card = G.s - 1 := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  · intro u hu v hv huv
    have hu := mem_Icc.1 (mem_coe.1 hu)
    have hv := mem_Icc.1 (mem_coe.1 hv)
    refine disjoint_left.2 fun x h1 h2 => ?_
    have b1 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h1
    have b2 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hv.2 h2
    rcases lt_or_gt_of_ne huv with h | h <;>
      linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]

/- English proof (translation)
Establish `hg0 : 0 < G.ga` using `by omega`. Establish `d1 : Disjoint G.tops G.cloudHalf` using `disjoint_left.2 fun x h1 h2 => by`. Take `⟨l, hl, rfl⟩` from `GridData.mem_tops.1 h1`. Combine the linear relations using `[GlobalTheory.ChiGrid.cloudHalf_lt h2, a_anti (G := G) hl]`. Establish `d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc (G.m - i + 1) G.m).biUnion G.blockC')` using `disjoint_left.2 fun x h1 h2 => by`.

Take `⟨u, hu, h2⟩` from `mem_biUnion.1 h2`. Establish `hu` using `mem_Icc.1 hu`. Establish `b` using `GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h2`. Break down `mem_union.1 h1 with h1 | h1` into its components or cases. Take `⟨l, -, rfl⟩` from `GridData.mem_tops.1 h1`.

Break down `lt_or_ge l u with h | h` into its components or cases. Combine the linear relations using `[GlobalTheory.ChiGrid.a_add_le (G := G) h, b.2]`. Combine the linear relations using `[a_anti (G := G) h, b.1]`. Combine the linear relations using `[GlobalTheory.ChiGrid.cloudHalf_lt h1, a_anti (G := G) hu.2, b.1]`. Use `G.two_le_k` as an intermediate fact.

Rewrite using `[GridData.entries_parPi, GridData.entries_lam, card_union_of_disjoint d2, card_union_of_disjoint d1, card_tops hg0, card_cloudHalf, card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_entries_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (entries (G.parPi i)).card = G.rankP i := by
  have hg0 : 0 < G.ga := by omega
  have d1 : Disjoint G.tops G.cloudHalf := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨l, hl, rfl⟩ := GridData.mem_tops.1 h1
    linarith [GlobalTheory.ChiGrid.cloudHalf_lt h2, a_anti (G := G) hl]
  have d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc (G.m - i + 1) G.m).biUnion G.blockC') :=
    disjoint_left.2 fun x h1 h2 => by
      obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
      have hu := mem_Icc.1 hu
      have b := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h2
      rcases mem_union.1 h1 with h1 | h1
      · obtain ⟨l, -, rfl⟩ := GridData.mem_tops.1 h1
        rcases lt_or_ge l u with h | h
        · linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b.2]
        · linarith [a_anti (G := G) h, b.1]
      · linarith [GlobalTheory.ChiGrid.cloudHalf_lt h1, a_anti (G := G) hu.2, b.1]
  have := G.two_le_k
  rw [GridData.entries_parPi, GridData.entries_lam, card_union_of_disjoint d2, card_union_of_disjoint d1,
    card_tops hg0, card_cloudHalf, card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

/- English proof (translation)
Rewrite using `[GridData.parPi]`. Use `(card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)` and prove the remaining obligations. Conclude with `card_image_le.trans (card_range _).le`. Conclude with `card_image_le.trans card_cloudHalf.le`. Conclude with `card_image_le`.
-/
theorem card_parPi_le {i : ℕ} (hg : 0 < G.ga) : (G.parPi i).card ≤ (G.m + 1) + (G.k - 1) +
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card := by
  rw [GridData.parPi]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact card_image_le.trans (card_range _).le
  · exact card_image_le.trans card_cloudHalf.le
  · exact card_image_le

/- English proof (translation)
Use `le_antisymm ?_ ((card_entries_parPi hm hs hg hi).symm.le.trans card_image_le)` and prove the remaining obligations. Use `G.two_le_k` as an intermediate fact. Use `(card_parPi_le (by omega)).trans ?_` and prove the remaining obligations. Rewrite using `[card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (G.parPi i).card = G.rankP i := by
  refine le_antisymm ?_ ((card_entries_parPi hm hs hg hi).symm.le.trans card_image_le)
  have := G.two_le_k
  refine (card_parPi_le (by omega)).trans ?_
  rw [card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

/- English proof (translation)
The claim follows from `isRegular_iff_card.2 ((card_entries_parPi hm hs hg hi).trans (card_parPi hm hs hg hi).symm)`.
-/
theorem isRegular_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    IsRegular (G.parPi i) :=
  isRegular_iff_card.2 ((card_entries_parPi hm hs hg hi).trans (card_parPi hm hs hg hi).symm)

/- English proof (translation)
Establish `: (G.parPi i).filter (fun x => x.2 = false) = (range ((G.m - i + 1) / 2)).image fun c => (G.a (G.m - i - 1 - 2 * c), false)`. Use extensionality with `⟨x, s⟩`. Simplify using `only [mem_filter, GridData.mem_parPi, mem_image, mem_range, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨l, h1, h2, h3⟩ | ⟨-, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩`.

Establish `h5 : ¬ (G.m - i ≤ l ∨ Even (G.m - i - l))` using `by simpa using h3.symm`. Rewrite `h5` using `[Nat.even_iff]`. Use `⟨(G.m - i - l - 1) / 2, by omega, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[show G.m - i - 1 - 2 * ((G.m - i - l - 1) / 2) = l by omega, h2]`. Simplify using `at h`.

Simplify using `at h`. Introduce and unpack `⟨c, hc, rfl, rfl⟩`. Use `⟨Or.inl ⟨G.m - i - 1 - 2 * c, by omega, rfl, ?_⟩, rfl⟩` and prove the remaining obligations. Use `symm`. Rewrite using `[decide_eq_false_iff_not, Nat.even_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[nMinus, this, card_image_of_injOn, card_range]`. Introduce `c hc c' hc' h`. Simplify using `only [coe_range, Set.mem_Iio] at hc hc'`. Establish `h1` using `a_injective hg (congrArg Prod.fst h)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nMinus_parPi (hg : 0 < G.ga) (i : ℕ) : nMinus (G.parPi i) = (G.m - i + 1) / 2 := by
  have : (G.parPi i).filter (fun x => x.2 = false) =
      (range ((G.m - i + 1) / 2)).image fun c => (G.a (G.m - i - 1 - 2 * c), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parPi, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨l, h1, h2, h3⟩ | ⟨-, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · have h5 : ¬ (G.m - i ≤ l ∨ Even (G.m - i - l)) := by simpa using h3.symm
        rw [Nat.even_iff] at h5
        refine ⟨(G.m - i - l - 1) / 2, by omega, ?_, rfl⟩
        rw [show G.m - i - 1 - 2 * ((G.m - i - l - 1) / 2) = l by omega, h2]
      · simp at h
      · simp at h
    · rintro ⟨c, hc, rfl, rfl⟩
      refine ⟨Or.inl ⟨G.m - i - 1 - 2 * c, by omega, rfl, ?_⟩, rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro c hc c' hc' h
  simp only [coe_range, Set.mem_Iio] at hc hc'
  have h1 := a_injective hg (congrArg Prod.fst h)
  omega

end GlobalTheory.PiCounts

namespace GlobalTheory.Grid

/- English proof (translation)
Introduce `D _ τ i hi`. Establish `hg : (grid D τ).s < (grid D τ).ga`. Use `(isLeast_gap D).1.2.1` as an intermediate fact. Use `show sLen D < gap D`. Use linear arithmetic over natural numbers and integers.

Establish `hs : 1 ≤ (grid D τ).s` using `by show 1 ≤ D.R.r + 6; omega`. Establish `hm` using `grid_nearMid D τ`. Establish `hi' : i ≤ (grid D τ).m` using `hi`. Use `⟨GlobalTheory.PiCounts.isRegular_parPi hm hs hg hi', ?_, GlobalTheory.PiCounts.nMinus_parPi (by omega) i⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.PiCounts.card_parPi hm hs hg hi').trans rfl`.
-/
theorem parPi_counts : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m →
    GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧
      GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  intro D _ τ i hi
  have hg : (grid D τ).s < (grid D τ).ga := by
    have := (isLeast_gap D).1.2.1
    show sLen D < gap D
    omega
  have hs : 1 ≤ (grid D τ).s := by show 1 ≤ D.R.r + 6; omega
  have hm := grid_nearMid D τ
  have hi' : i ≤ (grid D τ).m := hi
  refine ⟨GlobalTheory.PiCounts.isRegular_parPi hm hs hg hi', ?_, GlobalTheory.PiCounts.nMinus_parPi (by omega) i⟩
  exact (GlobalTheory.PiCounts.card_parPi hm hs hg hi').trans rfl

end GlobalTheory.Grid
