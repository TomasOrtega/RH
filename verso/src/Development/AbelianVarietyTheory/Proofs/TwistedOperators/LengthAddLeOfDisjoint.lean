import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

/- English proof (translation)
Establish `h : ∃ i, α i = 0` using `⟨m, hm m le_rfl⟩`. Use `⟨Nat.find h, Nat.find_min' h (hm m le_rfl), fun i => ⟨fun hi => Nat.find_min' h hi, fun hi => ?_⟩⟩` and prove the remaining obligations. Use `hα hi` as an intermediate fact. Rewrite `this` using `[Nat.find_spec h]`. Conclude with `Nat.le_zero.1 this`.
-/
theorem exists_length_of_antitone {α : ℕ → ℕ} (hα : Antitone α) {m : ℕ}
    (hm : ∀ i, m ≤ i → α i = 0) : ∃ t, t ≤ m ∧ ∀ i, α i = 0 ↔ t ≤ i := by
  classical
  have h : ∃ i, α i = 0 := ⟨m, hm m le_rfl⟩
  refine ⟨Nat.find h, Nat.find_min' h (hm m le_rfl), fun i => ⟨fun hi => Nat.find_min' h hi,
    fun hi => ?_⟩⟩
  have := hα hi
  rw [Nat.find_spec h] at this
  exact Nat.le_zero.1 this

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `h1` using `h ⟨t - 1, by omega⟩`. Rewrite `h1` using `[ht, hu, Fin.val_rev]`. Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem length_add_le_of_disjoint {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (htn : t ≤ n) (hun : u ≤ n)
    (h : ∀ i : Fin n, α i = 0 ∨ β i.rev = 0) : t + u ≤ n := by
  by_contra hc
  have h1 := h ⟨t - 1, by omega⟩
  rw [ht, hu, Fin.val_rev] at h1
  simp only at h1
  omega

def posList (α : ℕ → ℕ) (t : ℕ) : List ℤ := (List.range t).map fun i => (α i : ℤ)

def negList (β : ℕ → ℕ) (t : ℕ) : List ℤ := ((List.range t).map fun i => -(β i : ℤ)).reverse

/- English proof (translation)
Simplify using `[posList]`.
-/
@[simp] theorem length_posList (α : ℕ → ℕ) (t : ℕ) : (posList α t).length = t := by
  simp [posList]

/- English proof (translation)
Simplify using `[negList]`.
-/
@[simp] theorem length_negList (β : ℕ → ℕ) (t : ℕ) : (negList β t).length = t := by
  simp [negList]

/- English proof (translation)
Introduce `v hv`. Simplify using `only [posList, List.mem_map, List.mem_range] at hv`. Take `⟨i, hi, rfl⟩` from `hv`. Use `ht i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem posList_pos {α : ℕ → ℕ} {t : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i) :
    ∀ v ∈ posList α t, 0 < v := by
  intro v hv
  simp only [posList, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

/- English proof (translation)
Introduce `v hv`. Simplify using `only [negList, List.mem_reverse, List.mem_map, List.mem_range] at hv`. Take `⟨i, hi, rfl⟩` from `hv`. Use `ht i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem negList_neg {β : ℕ → ℕ} {t : ℕ} (ht : ∀ i, β i = 0 ↔ t ≤ i) :
    ∀ v ∈ negList β t, v < 0 := by
  intro v hv
  simp only [negList, List.mem_reverse, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

/- English proof (translation)
Rewrite using `[posList, List.pairwise_map]`. Use `List.pairwise_lt_range.imp fun {a b} h => ?_` and prove the remaining obligations. Use `hα h.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem posList_pairwise {α : ℕ → ℕ} (hα : Antitone α) (t : ℕ) :
    (posList α t).Pairwise (· ≥ ·) := by
  rw [posList, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hα h.le
  omega

/- English proof (translation)
Rewrite using `[negList, List.pairwise_reverse, List.pairwise_map]`. Use `List.pairwise_lt_range.imp fun {a b} h => ?_` and prove the remaining obligations. Use `hβ h.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem negList_pairwise {β : ℕ → ℕ} (hβ : Antitone β) (t : ℕ) :
    (negList β t).Pairwise (· ≥ ·) := by
  rw [negList, List.pairwise_reverse, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hβ h.le
  omega

/- English proof (translation)
Take `⟨i, hi⟩` from `i`. Simplify using `only [length_posList, length_negList, Fin.val_rev]`. Establish `hlen : i < (pad (posList α t) (n - t - u) (negList β u)).length`. Simplify using `[pad]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[List.getD_eq_getElem _ _ hlen]`. Simplify using `only [pad, List.getElem_map, List.getElem_append, List.length_append, length_posList, List.length_replicate, List.getElem_replicate]`. Use `split_ifs with h1 h2`. Rewrite using `[(hu _).2 (by omega)]`. Simplify using `[posList]`.

Rewrite using `[(hu _).2 (by omega), (ht _).2 (by omega)]`. Simplify using the standard rewrite rules. Rewrite using `[(ht _).2 (by omega)]`. Simplify using `only [negList, List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map, List.length_range]`. Establish `: u - 1 - (i - (t + (n - t - u))) = n - (i + 1)` using `by omega`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem getD_pad_posList_negList {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (hn : t + u ≤ n) (i : Fin n) :
    (pad (posList α t) (n - (posList α t).length - (negList β u).length) (negList β u)).getD i 0
      = (α i : ℚ) - β i.rev := by
  obtain ⟨i, hi⟩ := i
  simp only [length_posList, length_negList, Fin.val_rev]
  have hlen : i < (pad (posList α t) (n - t - u) (negList β u)).length := by
    simp [pad]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [pad, List.getElem_map, List.getElem_append, List.length_append, length_posList,
    List.length_replicate, List.getElem_replicate]
  split_ifs with h1 h2
  · rw [(hu _).2 (by omega)]
    simp [posList]
  · rw [(hu _).2 (by omega), (ht _).2 (by omega)]
    simp
  · rw [(ht _).2 (by omega)]
    simp only [negList, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    have : u - 1 - (i - (t + (n - t - u))) = n - (i + 1) := by omega
    rw [this]
    simp

/- English proof (translation)
Take `⟨α, β, γ, δ, hα, hβ, hγ, hδ, zα, zβ, zγ, zδ, d1, d2, d3, d4, e1, e2, e3, e4⟩` from `h`. Take `⟨a, ha, ta⟩` from `exists_length_of_antitone hα zα`. Take `⟨b, hb, tb⟩` from `exists_length_of_antitone hβ zβ`. Take `⟨c, hc, tc⟩` from `exists_length_of_antitone hγ zγ`. Take `⟨d, hd, td⟩` from `exists_length_of_antitone hδ zδ`.

Rewrite `ha`, `hb`, `hc`, `hd` using `[le_min_iff]`. Establish `l1` using `length_add_le_of_disjoint ta tb ha.1 hb.1 d1`. Establish `l2` using `length_add_le_of_disjoint tc td hc.1 hd.1 d2`. Establish `l3` using `length_add_le_of_disjoint ta td ha.2 hd.2 d3`. Establish `l4` using `length_add_le_of_disjoint tc tb hc.2 hb.2 d4`.

Use `⟨posList α a, negList β b, posList γ c, negList δ d, posList_pos ta, posList_pos tc, negList_neg tb, negList_neg td, posList_pairwise hα a, negList_pairwise hβ b, posList_pairwise hγ c, negList_pairwise hδ d, by simpa using l1, by simpa using l2, by simpa using l3, by simpa using …` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Break down `x with i | i` into its components or cases. Conclude with `(e1 i).trans (getD_pad_posList_negList ta tb l1 i).symm`. Conclude with `(e2 i).trans (getD_pad_posList_negList tc td l2 i).symm`.

Use function extensionality and compare the values at `x`. Break down `x with i | i` into its components or cases. Conclude with `(e3 i).trans (getD_pad_posList_negList ta td l3 i).symm`. Conclude with `(e4 i).trans (getD_pad_posList_negList tc tb l4 i).symm`.
-/
theorem jointShape_of_fnShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : FnShape p q r s μ μ') : JointShape p q r s μ μ' := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, zα, zβ, zγ, zδ, d1, d2, d3, d4, e1, e2, e3, e4⟩ := h
  obtain ⟨a, ha, ta⟩ := exists_length_of_antitone hα zα
  obtain ⟨b, hb, tb⟩ := exists_length_of_antitone hβ zβ
  obtain ⟨c, hc, tc⟩ := exists_length_of_antitone hγ zγ
  obtain ⟨d, hd, td⟩ := exists_length_of_antitone hδ zδ
  rw [le_min_iff] at ha hb hc hd
  have l1 := length_add_le_of_disjoint ta tb ha.1 hb.1 d1
  have l2 := length_add_le_of_disjoint tc td hc.1 hd.1 d2
  have l3 := length_add_le_of_disjoint ta td ha.2 hd.2 d3
  have l4 := length_add_le_of_disjoint tc tb hc.2 hb.2 d4
  refine ⟨posList α a, negList β b, posList γ c, negList δ d, posList_pos ta, posList_pos tc,
    negList_neg tb, negList_neg td, posList_pairwise hα a, negList_pairwise hβ b,
    posList_pairwise hγ c, negList_pairwise hδ d, by simpa using l1, by simpa using l2,
    by simpa using l3, by simpa using l4, ?_, ?_⟩
  · funext x
    rcases x with i | i
    · exact (e1 i).trans (getD_pad_posList_negList ta tb l1 i).symm
    · exact (e2 i).trans (getD_pad_posList_negList tc td l2 i).symm
  · funext x
    rcases x with i | i
    · exact (e3 i).trans (getD_pad_posList_negList ta td l3 i).symm
    · exact (e4 i).trans (getD_pad_posList_negList tc tb l4 i).symm

end GlobalTheory.JointHarm
