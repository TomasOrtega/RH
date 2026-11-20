import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*}

def moveToFront (E : List α) (j : ℕ) : List α :=
  match E[j]? with
  | some a => a :: E.eraseIdx j
  | none => E

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem moveToFront_eq_cons (E : List α) (j : ℕ) (hj : j < E.length) :
    moveToFront E j = (E[j]'hj) :: E.eraseIdx j := by
  simp [moveToFront, List.getElem?_eq_getElem hj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem length_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) :
    (moveToFront E j).length = E.length := by
  rw [moveToFront_eq_cons E j hj, List.length_cons,
    List.length_eraseIdx_add_one hj]

def indexBeforeMoveToFront (j : ℕ) : ℕ → ℕ
  | 0 => j
  | (i + 1) => if i < j then i else i + 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem indexBeforeMoveToFront_zero (j : ℕ) : indexBeforeMoveToFront j 0 = j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem indexBeforeMoveToFront_succ (j i : ℕ) : indexBeforeMoveToFront j (i + 1) = if i < j then i else i + 1 := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. It suffices to derive a contradiction. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately.

Split into cases according to the possible forms of the given data. Treat this case separately. It suffices to derive a contradiction. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Treat this case separately. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem indexBeforeMoveToFront_injective (j : ℕ) : Function.Injective (indexBeforeMoveToFront j) := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ i =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
  | succ i =>
    cases b with
    | zero =>
      exfalso
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
    | succ i' =>
      simp only [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem indexBeforeMoveToFront_lt_length (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < E.length) : indexBeforeMoveToFront j i < E.length := by
  cases i with
  | zero => exact hj
  | succ n =>
    show (if n < j then n else n + 1) < E.length
    split <;> omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem getElem_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < (moveToFront E j).length) :
    (moveToFront E j)[i]'hi =
      E[indexBeforeMoveToFront j i]'(indexBeforeMoveToFront_lt_length E j hj i (by
        rw [length_moveToFront E j hj] at hi; exact hi)) := by
  have hi' : i < E.length := by rw [length_moveToFront E j hj] at hi; exact hi
  have hlt : indexBeforeMoveToFront j i < E.length := indexBeforeMoveToFront_lt_length E j hj i hi'
  have key : (moveToFront E j)[i]? = E[indexBeforeMoveToFront j i]? := by
    rw [moveToFront_eq_cons E j hj]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, indexBeforeMoveToFront_zero, List.getElem?_eq_getElem hj]
    | succ m =>
      rw [List.getElem?_cons_succ, indexBeforeMoveToFront_succ]
      by_cases hm : m < j
      · rw [if_pos hm]
        simp [List.getElem?_eraseIdx_of_lt, hm]
      · rw [if_neg hm]
        have hm' : j ≤ m := by omega
        simp [List.getElem?_eraseIdx_of_ge, hm']
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hlt] at key
  exact Option.some.inj key

def indexInMoveToFront (j : ℕ) (i : ℕ) : ℕ := if i = j then 0 else if i < j then i + 1 else i

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem indexInMoveToFront_self (j : ℕ) : indexInMoveToFront j j = 0 := by
  simp [indexInMoveToFront]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem indexInMoveToFront_injective (j : ℕ) : Function.Injective (indexInMoveToFront j) := by
  intro a b hab
  simp only [indexInMoveToFront] at hab
  split_ifs at hab <;> omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem indexInMoveToFront_lt_length (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ) (hi : i < E.length) :
    indexInMoveToFront j i < (moveToFront E j).length := by
  rw [length_moveToFront E j hj]
  show (if i = j then 0 else if i < j then i + 1 else i) < E.length
  split_ifs <;> omega

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem getElem_eq_getElem_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < E.length) :
    E[i]'hi = (moveToFront E j)[indexInMoveToFront j i]'(indexInMoveToFront_lt_length E j hj i hi) := by
  rcases lt_trichotomy i j with h | h | h
  · have hb : indexInMoveToFront j i = i + 1 := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_lt, h]
  · subst h
    simp only [moveToFront_eq_cons E _ hj, indexInMoveToFront_self, List.getElem_cons_zero]
  · have hb : indexInMoveToFront j i = i := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hjk : j ≤ k := by omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_ge, hjk]

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_of_mem_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) (D : α)
    (hD : D ∈ moveToFront E j) : D ∈ E := by
  rw [moveToFront_eq_cons E j hj] at hD
  rcases List.mem_cons.mp hD with h1 | h2
  · subst h1
    simp
  · exact List.mem_of_mem_eraseIdx h2

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem chartAssignment_comp_of_injective {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
    (E E' : List X.IdealSheafData) (σ : ℕ → ℕ)
    (hinj : Function.Injective σ)
    (hlt : ∀ i, i < E'.length → σ i < E.length)
    (hEq : ∀ i, ∀ h : i < E'.length, (E'[i]'h) = E[σ i]'(hlt i h))
    (hainj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤)
    (hsome : ∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        (a ∘ σ) i = some t → (a ∘ σ) j = some t → i = j) ∧
      (∀ i, ∀ h : i < E'.length, (a ∘ σ) i = none → restrictIdeal (E'[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E'.length, ∀ t : Fin m, (a ∘ σ) i = some t →
        restrictIdeal (E'[i]'h) U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hit hjt
    simp only [Function.comp_apply] at hit hjt
    exact hinj (hainj (σ i) (hlt i hi) (σ j) (hlt j hj) t hit hjt)
  · intro i h hn
    simp only [Function.comp_apply] at hn
    rw [hEq i h]
    exact hnone (σ i) (hlt i h) hn
  · intro i h t ht
    simp only [Function.comp_apply] at ht
    rw [hEq i h]
    exact hsome (σ i) (hlt i h) t ht

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem inStrictNormalCrossingPosition_moveToFront {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (j : ℕ)
    (hj : j < E.length) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p (moveToFront E j) := by
  refine ⟨?_, ?_⟩
  · intro D hD
    exact hE.1 D (mem_of_mem_moveToFront E j hj D hD)
  · intro x
    obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hE.2 x
    have hlen : (moveToFront E j).length = E.length := length_moveToFront E j hj
    have hlt : ∀ i, i < (moveToFront E j).length → indexBeforeMoveToFront j i < E.length := by
      intro i hi
      refine indexBeforeMoveToFront_lt_length E j hj i ?_
      rw [hlen] at hi
      exact hi
    have hEq : ∀ i, ∀ h : i < (moveToFront E j).length,
        ((moveToFront E j)[i]'h) = E[indexBeforeMoveToFront j i]'(hlt i h) :=
      fun i h => getElem_moveToFront E j hj i h
    obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a E (moveToFront E j) (indexBeforeMoveToFront j)
      (indexBeforeMoveToFront_injective j) hlt hEq h1 h2 h3
    exact ⟨U, hxU, m, c, a ∘ indexBeforeMoveToFront j, k1, k2, k3⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem hasStrictNormalCrossingsWith_of_moveToFront {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hZ : HasStrictNormalCrossingsWith p Z (moveToFront E j)) :
    HasStrictNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := hZ x hx
  have hlt : ∀ i, i < E.length → indexInMoveToFront j i < (moveToFront E j).length :=
    fun i hi => indexInMoveToFront_lt_length E j hj i hi
  have hEq : ∀ i, ∀ h : i < E.length,
      (E[i]'h) = (moveToFront E j)[indexInMoveToFront j i]'(hlt i h) :=
    fun i h => getElem_eq_getElem_moveToFront E j hj i h
  obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a (moveToFront E j) E (indexInMoveToFront j)
    (indexInMoveToFront_injective j) hlt hEq h1 h2 h3
  exact ⟨U, hxU, m, c, a ∘ indexInMoveToFront j, S, k1, k2, k3, h4⟩

end FunctorialResolution.EmbeddedResolution
