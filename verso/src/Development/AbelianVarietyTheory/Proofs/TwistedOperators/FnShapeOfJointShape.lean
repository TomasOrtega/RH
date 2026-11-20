import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ListShape

def posFn (x : List ℤ) (i : ℕ) : ℕ := (x.getD i 0).toNat

def negFn (y : List ℤ) (i : ℕ) : ℕ := posFn (y.reverse.map fun v => -v) i

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem posFn_eq_zero {x : List ℤ} {i : ℕ} (h : x.length ≤ i) : posFn x i = 0 := by
  unfold posFn
  rw [List.getD_eq_default _ _ h]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem negFn_eq_zero {y : List ℤ} {i : ℕ} (h : y.length ≤ i) : negFn y i = 0 := by
  unfold negFn
  exact posFn_eq_zero (by simpa using h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem negFn_antitone {y : List ℤ} (h : y.Pairwise (· ≥ ·)) : Antitone (negFn y) := by
  show Antitone (posFn (y.reverse.map fun v => -v))
  apply posFn_antitone
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => neg_le_neg hab

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem posFn_cast {x : List ℤ} (hx : ∀ v ∈ x, 0 < v) {i : ℕ} (hi : i < x.length) :
    (posFn x i : ℚ) = (x[i] : ℤ) := by
  have hp : 0 < x[i] := hx _ (List.getElem_mem hi)
  simp only [posFn, List.getD_eq_getElem _ _ hi]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem negFn_cast {y : List ℤ} (hy : ∀ v ∈ y, v < 0) {i : ℕ} (hi : i < y.length) :
    (negFn y i : ℚ) = -((y[y.length - 1 - i] : ℤ) : ℚ) := by
  have hl : i < (y.reverse.map fun v => -v).length := by simpa using hi
  have hk : y.length - 1 - i < y.length := by omega
  have hv : y[y.length - 1 - i] < 0 := hy _ (List.getElem_mem hk)
  simp only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Prove the first alternative. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma getD_map_intCast (l : List ℤ) (i : ℕ) :
    (l.map (fun v : ℤ => (v : ℚ))).getD i 0 = ((l.getD i 0 : ℤ) : ℚ) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
