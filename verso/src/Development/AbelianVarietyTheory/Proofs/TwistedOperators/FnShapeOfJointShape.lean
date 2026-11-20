import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ListShape

def posFn (x : List ℤ) (i : ℕ) : ℕ := (x.getD i 0).toNat

def negFn (y : List ℤ) (i : ℕ) : ℕ := posFn (y.reverse.map fun v => -v) i

/- English proof (translation)
Unfold `posFn`. Rewrite using `[List.getD_eq_default _ _ h]`. Simplify using the standard rewrite rules.
-/
theorem posFn_eq_zero {x : List ℤ} {i : ℕ} (h : x.length ≤ i) : posFn x i = 0 := by
  unfold posFn
  rw [List.getD_eq_default _ _ h]
  simp

/- English proof (translation)
Unfold `negFn`. Conclude with `posFn_eq_zero (by simpa using h)`.
-/
theorem negFn_eq_zero {y : List ℤ} {i : ℕ} (h : y.length ≤ i) : negFn y i = 0 := by
  unfold negFn
  exact posFn_eq_zero (by simpa using h)

/- English proof (translation)
Introduce `i j hij`. Distinguish the cases in `hj : j < x.length`. Establish `hi : i < x.length` using `lt_of_le_of_lt hij hj`. Simplify using `only [posFn, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]`. Apply `Int.toNat_le_toNat` to reduce the goal to its premises.

Break down `hij.lt_or_eq with hlt | heq` into its components or cases. Conclude with `List.pairwise_iff_getElem.mp h i j hi hj hlt`. Substitute `heq` using the available equality. Conclude with `le_rfl`. Rewrite using `[posFn_eq_zero (not_lt.mp hj)]`.

Conclude with `Nat.zero_le _`.
-/
theorem posFn_antitone {x : List ℤ} (h : x.Pairwise (· ≥ ·)) : Antitone (posFn x) := by
  intro i j hij
  by_cases hj : j < x.length
  · have hi : i < x.length := lt_of_le_of_lt hij hj
    simp only [posFn, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    apply Int.toNat_le_toNat
    rcases hij.lt_or_eq with hlt | heq
    · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
    · subst heq
      exact le_rfl
  · rw [posFn_eq_zero (not_lt.mp hj)]
    exact Nat.zero_le _

/- English proof (translation)
Use `show Antitone (posFn (y.reverse.map fun v => -v))`. Apply `posFn_antitone` to reduce the goal to its premises. Rewrite using `[List.pairwise_map, List.pairwise_reverse]`. Conclude with `h.imp fun hab => neg_le_neg hab`.
-/
theorem negFn_antitone {y : List ℤ} (h : y.Pairwise (· ≥ ·)) : Antitone (negFn y) := by
  show Antitone (posFn (y.reverse.map fun v => -v))
  apply posFn_antitone
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => neg_le_neg hab

/- English proof (translation)
Establish `hp : 0 < x[i]` using `hx _ (List.getElem_mem hi)`. Simplify using `only [posFn, List.getD_eq_getElem _ _ hi]`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hp.le]`.
-/
theorem posFn_cast {x : List ℤ} (hx : ∀ v ∈ x, 0 < v) {i : ℕ} (hi : i < x.length) :
    (posFn x i : ℚ) = (x[i] : ℤ) := by
  have hp : 0 < x[i] := hx _ (List.getElem_mem hi)
  simp only [posFn, List.getD_eq_getElem _ _ hi]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]

/- English proof (translation)
Establish `hl : i < (y.reverse.map fun v => -v).length` using `by simpa using hi`. Establish `hk : y.length - 1 - i < y.length` using `by omega`. Establish `hv : y[y.length - 1 - i] < 0` using `hy _ (List.getElem_mem hk)`. Simplify using `only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]`.
-/
theorem negFn_cast {y : List ℤ} (hy : ∀ v ∈ y, v < 0) {i : ℕ} (hi : i < y.length) :
    (negFn y i : ℚ) = -((y[y.length - 1 - i] : ℤ) : ℚ) := by
  have hl : i < (y.reverse.map fun v => -v).length := by simpa using hi
  have hk : y.length - 1 - i < y.length := by omega
  have hv : y[y.length - 1 - i] < 0 := hy _ (List.getElem_mem hk)
  simp only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]

/- English proof (translation)
Establish `hn` using `i.isLt`. Distinguish the cases in `hi : x.length ≤ (i : ℕ)`. Conclude with `Or.inl (posFn_eq_zero hi)`. Use `right`. Apply `negFn_eq_zero` to reduce the goal to its premises.

Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem disj {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) (i : Fin n) :
    posFn x i = 0 ∨ negFn y i.rev = 0 := by
  have hn := i.isLt
  by_cases hi : x.length ≤ (i : ℕ)
  · exact Or.inl (posFn_eq_zero hi)
  · right
    apply negFn_eq_zero
    rw [Fin.val_rev]
    omega

/- English proof (translation)
Rewrite using `[List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]`. Apply the tactic sequence `cases l[i]? <;> simp`.
-/
private lemma getD_map_intCast (l : List ℤ) (i : ℕ) :
    (l.map (fun v : ℤ => (v : ℚ))).getD i 0 = ((l.getD i 0 : ℤ) : ℚ) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/- English proof (translation)
Establish `hn` using `i.isLt`. Unfold `pad`. Rewrite using `[getD_map_intCast, List.append_assoc, Fin.val_rev]`. Distinguish the cases in `h1 : (i : ℕ) < x.length`. Rewrite using `[List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, posFn_cast hx h1, negFn_eq_zero (by omega)]`.

Simplify using the standard rewrite rules. Rewrite using `[List.getD_append_right _ _ _ _ (not_lt.mp h1), posFn_eq_zero (not_lt.mp h1)]`. Distinguish the cases in `h2 : (i : ℕ) - x.length < n - x.length - y.length`. Rewrite using `[List.getD_append _ _ _ _ (by simpa using h2), negFn_eq_zero (by omega)]`. Simplify using `[List.getD_eq_getElem?_getD, List.getElem?_replicate, h2]`.

Rewrite using `[List.getD_append_right _ _ _ _ (by simp; omega)]`. Simplify using `only [List.length_replicate]`. Establish `hj : n - ((i : ℕ) + 1) < y.length` using `by omega`. Rewrite using `[negFn_cast hy hj]`. Establish `e : (i : ℕ) - x.length - (n - x.length - y.length) = y.length - 1 - (n - ((i : ℕ) + 1))`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, List.getD_eq_getElem _ _ (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem pad_getD {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (i : Fin n) :
    (pad x (n - x.length - y.length) y).getD i 0 = (posFn x i : ℚ) - negFn y i.rev := by
  have hn := i.isLt
  unfold pad
  rw [getD_map_intCast, List.append_assoc, Fin.val_rev]
  by_cases h1 : (i : ℕ) < x.length
  · rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, posFn_cast hx h1,
      negFn_eq_zero (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), posFn_eq_zero (not_lt.mp h1)]
    by_cases h2 : (i : ℕ) - x.length < n - x.length - y.length
    · rw [List.getD_append _ _ _ _ (by simpa using h2), negFn_eq_zero (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h2]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      have hj : n - ((i : ℕ) + 1) < y.length := by omega
      rw [negFn_cast hy hj]
      have e : (i : ℕ) - x.length - (n - x.length - y.length) = y.length - 1 - (n - ((i : ℕ) + 1)) := by
        omega
      rw [e, List.getD_eq_getElem _ _ (by omega)]
      simp

end GlobalTheory.JointHarm.ListShape

namespace GlobalTheory.JointHarm

open ListShape in

/- English proof (translation)
Take `⟨a, b, c, d, ha, hc, hb, hd, ha', hb', hc', hd', hab, hcd, had, hcb, hμ, hμ'⟩` from `h`. Use `⟨posFn a, negFn b, posFn c, negFn d, posFn_antitone ha', negFn_antitone hb', posFn_antitone hc', negFn_antitone hd', fun i hi => posFn_eq_zero (by omega), fun i hi => negFn_eq_zero (by omega), fun i hi => posFn_eq_zero (by omega), fun i hi => negFn_eq_zero (by omega), disj hab, d …` and prove the remaining obligations. Rewrite using `[hμ]`. Conclude with `pad_getD ha hb hab i`. Rewrite using `[hμ]`.

Conclude with `pad_getD hc hd hcd i`. Rewrite using `[hμ']`. Conclude with `pad_getD ha hd had i`. Rewrite using `[hμ']`. Conclude with `pad_getD hc hb hcb i`.
-/
theorem fnShape_of_jointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : JointShape p q r s μ μ') : FnShape p q r s μ μ' := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, ha', hb', hc', hd', hab, hcd, had, hcb, hμ, hμ'⟩ := h
  refine ⟨posFn a, negFn b, posFn c, negFn d, posFn_antitone ha', negFn_antitone hb',
    posFn_antitone hc', negFn_antitone hd', fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), disj hab, disj hcd, disj had, disj hcb,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hμ]
    exact pad_getD ha hb hab i
  · rw [hμ]
    exact pad_getD hc hd hcd i
  · rw [hμ']
    exact pad_getD ha hd had i
  · rw [hμ']
    exact pad_getD hc hb hcb i

end GlobalTheory.JointHarm
