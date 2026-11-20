import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
Establish `h1 : κ b ≤ κ a` using `h hab.le`. Establish `h2 : a.val < b.val` using `hab`. Use linear arithmetic over natural numbers and integers.
-/
theorem lca_content_lt {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q} (hab : a < b) :
    (κ b : ℤ) - (b.val : ℤ) < (κ a : ℤ) - (a.val : ℤ) := by
  have h1 : κ b ≤ κ a := h hab.le
  have h2 : a.val < b.val := hab
  omega

/- English proof (translation)
Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Use `lca_content_lt κ h hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hab`. Use `lca_content_lt κ h hab` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem lca_content_inj {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q}
    (e : (κ a : ℤ) - (a.val : ℤ) = (κ b : ℤ) - (b.val : ℤ)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lca_content_lt κ h hab; omega
  · exact hab
  · have := lca_content_lt κ h hab; omega

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero => intro _`. Rewrite using `[H.start, H'.start]`. Consider the case `succ l ih`.

Introduce `hl`. Establish `e` using `ih (by omega)`. Establish `hln : l < n` using `by omega`. Establish `h1` using `hc ⟨l, hln⟩ (by show l < m; omega)`. Establish `h2` using `H.step ⟨l, hln⟩`.

Establish `h3` using `H'.step ⟨l, hln⟩`. Simplify using `only [cseq] at h1 h2 h3`. Rewrite `h1`, `h3` using `[← e]`. Establish `h4 : ρ ⟨l, hln⟩ = ρ' ⟨l, hln⟩` using `lca_content_inj (κ l) (H.dom l (by omega)) h1`. Rewrite using `[h2, h3, h4]`.
-/
theorem path_eq_of_content_sequence {q n : ℕ} {lam2 tau tau' : Fin q → ℕ} {κ κ' : ℕ → Fin q → ℕ} {ρ ρ' : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (H' : IsPath n lam2 tau' κ' ρ') (m : ℕ) (hm : m ≤ n)
    (hc : ∀ j : Fin n, j.val < m → cseq κ ρ j = cseq κ' ρ' j) : ∀ l ≤ m, κ l = κ' l := by
  intro l
  induction l with
  | zero => intro _; rw [H.start, H'.start]
  | succ l ih =>
    intro hl
    have e := ih (by omega)
    have hln : l < n := by omega
    have h1 := hc ⟨l, hln⟩ (by show l < m; omega)
    have h2 := H.step ⟨l, hln⟩
    have h3 := H'.step ⟨l, hln⟩
    dsimp only [cseq] at h1 h2 h3
    rw [← e] at h1 h3
    have h4 : ρ ⟨l, hln⟩ = ρ' ⟨l, hln⟩ := lca_content_inj (κ l) (H.dom l (by omega)) h1
    rw [h2, h3, h4]

/- English proof (translation)
Simplify using `[Pi.single_apply, h]`.
-/
theorem lca_single_ne {q : ℕ} {r a : Fin q} (h : a ≠ r) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) a = A a := by
  simp [Pi.single_apply, h]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lca_single_eq {q : ℕ} (r : Fin q) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) r = A r + 1 := by simp

/- English proof (translation)
Establish `hjn` using `j'.isLt`. Establish `s1` using `H.step j`. Establish `d1` using `H.dom (j.val + 1) (by omega)`. Establish `hle' : κ (j.val + 1) (ρ j') ≤ κ j.val (ρ j)`. Use `hle` as an intermediate fact.

Unfold `colSeq at this`. Rewrite `this` using `[hv]`. Then use the resulting hypothesis. Establish `hlt : ρ j < ρ j'`. Assume the negation of the conclusion as `hcon`. Establish `hcon : ρ j' ≤ ρ j` using `not_lt.mp hcon`.

Establish `h3` using `d1 hcon`. Rewrite `h3`, `hle'` using `[s1]`. Rewrite `h3` using `[lca_single_eq]`. Use linear arithmetic over natural numbers and integers. Use `⟨hlt, ?_⟩` and prove the remaining obligations.

Unfold `colSeq`. Rewrite using `[hv, s1, lca_single_ne hlt.ne']`.
-/
theorem lca_rows_lt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hle : colSeq κ ρ j' ≤ colSeq κ ρ j) :
    ρ j < ρ j' ∧ colSeq κ ρ j' = κ j.val (ρ j') := by
  have hjn := j'.isLt
  have s1 := H.step j
  have d1 := H.dom (j.val + 1) (by omega)
  have hle' : κ (j.val + 1) (ρ j') ≤ κ j.val (ρ j) := by
    have := hle; unfold colSeq at this; rwa [hv] at this
  have hlt : ρ j < ρ j' := by
    by_contra hcon
    have hcon : ρ j' ≤ ρ j := not_lt.mp hcon
    have h3 := d1 hcon
    rw [s1] at h3 hle'
    rw [lca_single_eq] at h3
    omega
  refine ⟨hlt, ?_⟩
  unfold colSeq; rw [hv, s1, lca_single_ne hlt.ne']

/- English proof (translation)
Take `⟨hr, hc⟩` from `lca_rows_lt H j j' hv hlt.le`. Establish `hjn` using `j'.isLt`. Establish `s1` using `H.step j`. Establish `s2` using `H.step j'`. Rewrite `s2` using `[hv]`.

Establish `d0` using `H.dom j.val (by omega)`. Establish `d2` using `H.dom (j.val + 1 + 1) (by omega)`. Establish `hA : κ j.val (ρ j') < κ j.val (ρ j)` using `by rw [← hc]; exact hlt`. Establish `hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ)`. Use `hc` as an intermediate fact.

Unfold `colSeq at this`. Unfold `cseq`. Rewrite using `[this]`. Establish `hr' : (ρ j).val < (ρ j').val` using `hr`. Use `⟨by rw [hc']; unfold cseq; omega, ?_⟩` and prove the remaining obligations.

Take `⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ, ∀ l, κ' l = if l = j.val + 1 then κ j.val + Pi.single (ρ j') 1 else κ l` from `⟨_, fun _ => rfl⟩`. Establish `k1 : κ' (j.val + 1) = κ j.val + Pi.single (ρ j') 1` using `by rw [hκ', if_pos rfl]`. Establish `k2 : ∀ l, l ≠ j.val + 1 → κ' l = κ l` using `fun l h => by rw [hκ', if_neg h]`. Establish `anti : Antitone (κ j.val + Pi.single (ρ j') 1)`. Introduce `a b hab`.

Distinguish the cases in `hb : b = ρ j'`. Distinguish the cases in `ha : a = ρ j'`. Rewrite using `[ha, hb]`. Rewrite using `[hb, lca_single_eq, lca_single_ne ha]`. Establish `hab' : a < ρ j'` using `lt_of_le_of_ne (hb ▸ hab) ha`.

Distinguish the cases in `har : a ≤ ρ j`. Use `d0 har` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `har : ρ j < a` using `not_le.mp har`. Establish `h5` using `d2 hab'.le`.

Rewrite `h5` using `[s2, s1]`. Rewrite `h5` using `[lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha, lca_single_ne har.ne']`. Conclude with `h5`. Rewrite using `[lca_single_ne hb]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcol : colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j'`. Use function extensionality and compare the values at `l`. Distinguish the cases in `h1 : l = j`. Rewrite using `[h1]`. Simplify using `only [colSeq, Function.comp, Equiv.swap_apply_left]`.

Rewrite using `[k2 j.val (by omega), hv, s1, lca_single_ne hr.ne']`. Distinguish the cases in `h2 : l = j'`. Rewrite using `[h2]`. Simplify using `only [colSeq, Function.comp, Equiv.swap_apply_right]`. Rewrite using `[hv, k1, lca_single_ne hr.ne]`.

Establish `h4 : l.val ≠ j.val + 1` using `fun h => h2 (Fin.ext (h.trans hv.symm))`. Simplify using `only [colSeq, Function.comp]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ h4]`. Use `⟨κ', ⟨?_, ?_, ?_, ?_⟩, ?_, hcol⟩` and prove the remaining obligations. Rewrite using `[k2 0 (by omega), H.start]`.

Introduce `l`. Distinguish the cases in `h1 : l = j`. Rewrite using `[h1]`. Simplify using `only [Function.comp, Equiv.swap_apply_left]`. Rewrite using `[k1, k2 j.val (by omega)]`.

Distinguish the cases in `h2 : l = j'`. Rewrite using `[h2]`. Simplify using `only [Function.comp, Equiv.swap_apply_right]`. Rewrite using `[hv, k1, k2 (j.val + 1 + 1) (by omega), s2, s1]`. Conclude with `add_right_comm _ _ _`.

Establish `h3 : l.val ≠ j.val` using `fun h => h1 (Fin.ext h)`. Establish `h4 : l.val ≠ j.val + 1` using `fun h => h2 (Fin.ext (h.trans hv.symm))`. Simplify using `only [Function.comp]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ (by omega), k2 _ h4]`. Conclude with `H.step l`.

Rewrite using `[k2 n (by omega), H.stop]`. Introduce `l hl`. Distinguish the cases in `h : l = j.val + 1`. Rewrite using `[h, k1]`. Conclude with `anti`.

Rewrite using `[k2 l h]`. Conclude with `H.dom l hl`. Use function extensionality and compare the values at `l`. Use `congrFun hcol l` as an intermediate fact. Simplify using `only [colSeq, cseq, Function.comp] at this ⊢`.

Rewrite using `[this]`.
-/
theorem lca_swap {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hlt : colSeq κ ρ j' < colSeq κ ρ j) :
    2 ≤ cseq κ ρ j - cseq κ ρ j' ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j j') ∧
        cseq κ' (ρ ∘ Equiv.swap j j') = cseq κ ρ ∘ Equiv.swap j j' ∧
        colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv hlt.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') < κ j.val (ρ j) := by rw [← hc]; exact hlt
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  refine ⟨by rw [hc']; unfold cseq; omega, ?_⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ,
      ∀ l, κ' l = if l = j.val + 1 then κ j.val + Pi.single (ρ j') 1 else κ l := ⟨_, fun _ => rfl⟩
  have k1 : κ' (j.val + 1) = κ j.val + Pi.single (ρ j') 1 := by rw [hκ', if_pos rfl]
  have k2 : ∀ l, l ≠ j.val + 1 → κ' l = κ l := fun l h => by rw [hκ', if_neg h]
  have anti : Antitone (κ j.val + Pi.single (ρ j') 1) := by
    intro a b hab
    by_cases hb : b = ρ j'
    · by_cases ha : a = ρ j'
      · rw [ha, hb]
      · rw [hb, lca_single_eq, lca_single_ne ha]
        have hab' : a < ρ j' := lt_of_le_of_ne (hb ▸ hab) ha
        by_cases har : a ≤ ρ j
        · have := d0 har; omega
        · have har : ρ j < a := not_le.mp har
          have h5 := d2 hab'.le
          rw [s2, s1] at h5
          rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha, lca_single_ne har.ne'] at h5
          exact h5
    · rw [lca_single_ne hb]
      calc κ j.val b ≤ κ j.val a := d0 hab
        _ ≤ (κ j.val + Pi.single (ρ j') 1 : Fin q → ℕ) a := by simp [Pi.add_apply]
  have hcol : colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
    funext l
    by_cases h1 : l = j
    · rw [h1]
      simp only [colSeq, Function.comp, Equiv.swap_apply_left]
      rw [k2 j.val (by omega), hv, s1, lca_single_ne hr.ne']
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [colSeq, Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, lca_single_ne hr.ne]
      · have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [colSeq, Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ h4]
  refine ⟨κ', ⟨?_, ?_, ?_, ?_⟩, ?_, hcol⟩
  · rw [k2 0 (by omega), H.start]
  · intro l
    by_cases h1 : l = j
    · rw [h1]
      simp only [Function.comp, Equiv.swap_apply_left]
      rw [k1, k2 j.val (by omega)]
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, k2 (j.val + 1 + 1) (by omega), s2, s1]
        exact add_right_comm _ _ _
      · have h3 : l.val ≠ j.val := fun h => h1 (Fin.ext h)
        have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ (by omega), k2 _ h4]
        exact H.step l
  · rw [k2 n (by omega), H.stop]
  · intro l hl
    by_cases h : l = j.val + 1
    · rw [h, k1]; exact anti
    · rw [k2 l h]; exact H.dom l hl
  · funext l
    have := congrFun hcol l
    simp only [colSeq, cseq, Function.comp] at this ⊢
    rw [this]

/- English proof (translation)
Introduce `q n lam2 tau κ ρ H j hj hlt`. Conclude with `lca_swap H j ⟨j.val + 1, hj⟩ rfl hlt`.
-/
theorem swap_path_exists : SwapPath := by
  intro q n lam2 tau κ ρ H j hj hlt
  exact lca_swap H j ⟨j.val + 1, hj⟩ rfl hlt

/- English proof (translation)
Take `⟨hr, hc⟩` from `lca_rows_lt H j j' hv heq.le`. Establish `hjn` using `j'.isLt`. Establish `s1` using `H.step j`. Establish `s2` using `H.step j'`. Rewrite `s2` using `[hv]`.

Establish `d0` using `H.dom j.val (by omega)`. Establish `d2` using `H.dom (j.val + 1 + 1) (by omega)`. Establish `hA : κ j.val (ρ j') = κ j.val (ρ j)` using `by rw [← hc]; exact heq`. Establish `hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ)`. Use `hc` as an intermediate fact.

Unfold `colSeq at this`. Unfold `cseq`. Rewrite using `[this]`. Establish `hr' : (ρ j).val < (ρ j').val` using `hr`. Prove the components needed by the constructor for the conclusion.

Establish `hrow : (ρ j').val = (ρ j).val + 1`. Assume the negation of the conclusion as `hcon`. Establish `hq` using `(ρ j').isLt`. Take `⟨a, ha⟩ : ∃ a : Fin q, a.val = (ρ j).val + 1` from `⟨⟨(ρ j).val + 1, by omega⟩, rfl⟩`. Establish `ha1 : ρ j < a` using `by show (ρ j).val < a.val; omega`.

Establish `ha2 : a < ρ j'` using `by show a.val < (ρ j').val; omega`. Establish `h5` using `d2 ha2.le`. Rewrite `h5` using `[s2, s1]`. Rewrite `h5` using `[lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha2.ne, lca_single_ne ha1.ne']`. Establish `h6` using `d0 ha1.le`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hc']`. Unfold `cseq`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨tau', κ', ρ', H', hcs⟩`.

Establish `hpre : ∀ i : Fin n, i.val < j.val → cseq κ ρ i = cseq κ' ρ' i`. Introduce `i hi`. Establish `h` using `congrFun hcs i`. Establish `h1 : i ≠ j` using `fun h => by rw [h] at hi; omega`. Establish `h2 : i ≠ j'` using `fun h => by rw [h] at hi; omega`.

Simplify using `only [Function.comp] at h`. Rewrite `h` using `[Equiv.swap_apply_of_ne_of_ne h1 h2]`. Conclude with `h.symm`. Establish `e : κ j.val = κ' j.val` using `path_eq_of_content_sequence H H' j.val (by omega) hpre j.val le_rfl`. Establish `h1` using `congrFun hcs j`.

Simplify using `only [Function.comp, Equiv.swap_apply_left] at h1`. Rewrite `h1` using `[hc']`. Unfold `cseq at h1`. Rewrite `h1` using `[← e]`. Establish `h2 : ρ' j = ρ j'` using `lca_content_inj _ d0 h1`.

Establish `h3` using `H'.dom (j.val + 1) (by omega) hr.le`. Rewrite `h3` using `[H'.step j, ← e, h2, lca_single_eq, lca_single_ne hr.ne]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lca_same {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (heq : colSeq κ ρ j' = colSeq κ ρ j) :
    cseq κ ρ j' = cseq κ ρ j - 1 ∧ ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j j') := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv heq.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') = κ j.val (ρ j) := by rw [← hc]; exact heq
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  constructor
  · have hrow : (ρ j').val = (ρ j).val + 1 := by
      by_contra hcon
      have hq := (ρ j').isLt
      obtain ⟨a, ha⟩ : ∃ a : Fin q, a.val = (ρ j).val + 1 := ⟨⟨(ρ j).val + 1, by omega⟩, rfl⟩
      have ha1 : ρ j < a := by show (ρ j).val < a.val; omega
      have ha2 : a < ρ j' := by show a.val < (ρ j').val; omega
      have h5 := d2 ha2.le
      rw [s2, s1] at h5
      rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha2.ne, lca_single_ne ha1.ne'] at h5
      have h6 := d0 ha1.le
      omega
    rw [hc']; unfold cseq; omega
  · rintro ⟨tau', κ', ρ', H', hcs⟩
    have hpre : ∀ i : Fin n, i.val < j.val → cseq κ ρ i = cseq κ' ρ' i := by
      intro i hi
      have h := congrFun hcs i
      have h1 : i ≠ j := fun h => by rw [h] at hi; omega
      have h2 : i ≠ j' := fun h => by rw [h] at hi; omega
      simp only [Function.comp] at h
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at h
      exact h.symm
    have e : κ j.val = κ' j.val := path_eq_of_content_sequence H H' j.val (by omega) hpre j.val le_rfl
    have h1 := congrFun hcs j
    simp only [Function.comp, Equiv.swap_apply_left] at h1
    rw [hc'] at h1
    unfold cseq at h1
    rw [← e] at h1
    have h2 : ρ' j = ρ j' := lca_content_inj _ d0 h1
    have h3 := H'.dom (j.val + 1) (by omega) hr.le
    rw [H'.step j, ← e, h2, lca_single_eq, lca_single_ne hr.ne] at h3
    omega

/- English proof (translation)
Introduce `q n lam2 tau κ ρ H j hj heq`. Conclude with `lca_same H j ⟨j.val + 1, hj⟩ rfl heq`.
-/
theorem same_column : SameCol := by
  intro q n lam2 tau κ ρ H j hj heq
  exact lca_same H j ⟨j.val + 1, hj⟩ rfl heq

end Formalism.CohomologicalDescent.LC
