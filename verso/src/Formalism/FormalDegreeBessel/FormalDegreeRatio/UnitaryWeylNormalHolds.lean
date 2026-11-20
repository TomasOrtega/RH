import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

namespace WeylGroupFacts

variable {k r : ℕ}

def col (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
    g i j = if i = j then 1 else 0

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

/- English proof (translation)
Simplify using `only [Nset, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hU, h1, h2⟩`. Use `⟨hU, ?_⟩` and prove the remaining obligations. Introduce `i j hj hij`.

Distinguish the cases in `hjr : j.val < r`. Establish `e` using `h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)`. Establish `he : eI k r ⟨j.val, hjr⟩ = j` using `Fin.ext rfl`. Rewrite `e` using `[he]`. Conclude with `e`.

Conclude with `h2 i j (by omega) hj (by omega)`. Introduce and unpack `⟨hU, hc⟩`. Use `⟨hU, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Conclude with `hc i (eI k r a) (by show a.val ≤ r + k; have := a.isLt; omega) (Or.inl hai)`.

Introduce `i j hrj hj hri`. Conclude with `hc i j hj (Or.inr hri)`.
-/
theorem nset_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ col k r g := by
  simp only [Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, h1, h2⟩
    refine ⟨hU, ?_⟩
    intro i j hj hij
    by_cases hjr : j.val < r
    · have e := h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rw [he] at e
      exact e
    · exact h2 i j (by omega) hj (by omega)
  · rintro ⟨hU, hc⟩
    refine ⟨hU, ?_, ?_⟩
    · intro a i hai
      exact hc i (eI k r a) (by show a.val ≤ r + k; have := a.isLt; omega) (Or.inl hai)
    · intro i j hrj hj hri
      exact hc i j hj (Or.inr hri)

/- English proof (translation)
Introduce `i j _ _`. Conclude with `Matrix.one_apply`.
-/
theorem col_one : col k r (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
  intro i j _ _
  exact Matrix.one_apply

/- English proof (translation)
Introduce `i j hj hij`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single j]`. Rewrite using `[hg i j hj hij, hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one]`. Introduce `p hp`. Distinguish the cases in `hpj : j.val ≤ p.val ∨ r ≤ p.val`.

Rewrite using `[hh p j hj hpj, if_neg hp, mul_zero]`. Establish `hz : g i p = 0`. Rewrite using `[hg i p (by omega) (by omega), if_neg]`. Introduce `hip`. Substitute `hip` using the available equality.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hz, zero_mul]`.
-/
theorem col_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : col k r (g * h) := by
  intro i j hj hij
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · rw [hg i j hj hij, hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one]
  · intro p hp
    by_cases hpj : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hh p j hj hpj, if_neg hp, mul_zero]
    · have hz : g i p = 0 := by
        rw [hg i p (by omega) (by omega), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val = n → j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → g' i j = if i = j then 1 else 0 by`. Introduce `i j hj hij`. Conclude with `H j.val i j rfl hj hij`. Introduce `n`. Use the proof step `induction' n using Nat.strong_induction_on with n ih`.

Introduce `i j hjn hj hij`. Establish `h1 : (g' * g) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j`. Rewrite using `[hm]`. Rewrite `h1` using `[Matrix.mul_apply, Fintype.sum_eq_single j]`. Rewrite `h1` using `[hg j j hj (Or.inl le_rfl), if_pos rfl, mul_one, Matrix.one_apply]`.

Conclude with `h1`. Introduce `p hp`. Distinguish the cases in `hpj : j.val ≤ p.val ∨ r ≤ p.val`. Rewrite using `[hg p j hj hpj, if_neg hp, mul_zero]`. Establish `hz : g' i p = 0`.

Rewrite using `[ih p.val (by omega) i p rfl (by omega) (by omega), if_neg]`. Introduce `hip`. Substitute `hip` using the available equality. Use linear arithmetic over natural numbers and integers. Rewrite using `[hz, zero_mul]`.
-/
theorem col_of_left_inv {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hm : g' * g = 1) : col k r g' := by
  suffices H : ∀ n : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val = n → j.val ≤ r + k →
      (j.val ≤ i.val ∨ r ≤ i.val) → g' i j = if i = j then 1 else 0 by
    intro i j hj hij
    exact H j.val i j rfl hj hij
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro i j hjn hj hij
  have h1 : (g' * g) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
    rw [hm]
  rw [Matrix.mul_apply, Fintype.sum_eq_single j] at h1
  · rw [hg j j hj (Or.inl le_rfl), if_pos rfl, mul_one, Matrix.one_apply] at h1
    exact h1
  · intro p hp
    by_cases hpj : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p j hj hpj, if_neg hp, mul_zero]
    · have hz : g' i p = 0 := by
        rw [ih p.val (by omega) i p rfl (by omega) (by omega), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hm` using `m.isLt`. Unfold `Hpk tau sgn`. Simplify using `only [Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num`.
-/
theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hm := m.isLt
  unfold Hpk tau sgn
  simp only [Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single (tau k r i)]`. Rewrite using `[hpk_row, if_pos rfl]`. Introduce `p hp`. Rewrite using `[hpk_row, if_neg hp, zero_mul]`.
-/
theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro p hp
    rw [hpk_row, if_neg hp, zero_mul]

/- English proof (translation)
Establish `hi` using `i.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [tau, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau, Fin.val_mk]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Simplify using `only [sgn, tau, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num`.
-/
theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  have hi := i.isLt
  simp only [sgn, tau, Fin.val_mk]
  split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, sgn_mul_self]`.

Rewrite using `[if_neg (Ne.symm h), if_neg h, mul_zero]`.
-/
theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, sgn_mul_self]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/- English proof (translation)
Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h2 : (Hpk k r * (gᴴ * Hpk k r)) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = 1 := by rw [h1, hpk_sq]`.

Establish `h3` using `congrArg Matrix.det h2`. Rewrite `h3` using `[Matrix.det_mul, Matrix.det_one, mul_comm]`. Conclude with `⟨⟨_, _, h3, (mul_comm _ _).trans h3⟩, rfl⟩`.
-/
theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : (Hpk k r * (gᴴ * Hpk k r)) * g = 1 := by
    calc (Hpk k r * (gᴴ * Hpk k r)) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [mul_assoc]
      _ = 1 := by rw [h1, hpk_sq]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h3
  exact ⟨⟨_, _, h3, (mul_comm _ _).trans h3⟩, rfl⟩

/- English proof (translation)
Use `show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r`. Rewrite using `[Matrix.conjTranspose_one, one_mul, mul_one]`.
-/
theorem uh_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  rw [Matrix.conjTranspose_one, one_mul, mul_one]

/- English proof (translation)
Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h2 : hᴴ * Hpk k r * h = Hpk k r` using `hh`. Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

/- English proof (translation)
Establish `hd` using `isUnit_of_uh hg`. Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hr : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hd`. Use `show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [mul_assoc]`. Use `_ = Hpk k r := by rw [hr, Matrix.conjTranspose_one, one_mul, mul_one]`.
-/
theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hd := isUnit_of_uh hg
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hr : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [h1]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = Hpk k r := by rw [hr, Matrix.conjTranspose_one, one_mul, mul_one]

/- English proof (translation)
The claim follows from `(nset_iff 1).2 ⟨uh_one, col_one⟩`.
-/
theorem mem_n_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r := (nset_iff 1).2 ⟨uh_one, col_one⟩

/- English proof (translation)
Establish `hg'` using `(nset_iff g).1 hg`. Establish `hh'` using `(nset_iff h).1 hh`. Conclude with `(nset_iff _).2 ⟨uh_mul hg'.1 hh'.1, col_mul hg'.2 hh'.2⟩`.
-/
theorem mem_n_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) : g * h ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hh' := (nset_iff h).1 hh
  exact (nset_iff _).2 ⟨uh_mul hg'.1 hh'.1, col_mul hg'.2 hh'.2⟩

/- English proof (translation)
Establish `hg'` using `(nset_iff g).1 hg`. Establish `hd` using `isUnit_of_uh hg'.1`. Conclude with `(nset_iff _).2 ⟨uh_inv hg'.1, col_of_left_inv hg'.2 (Matrix.nonsing_inv_mul g hd)⟩`.
-/
theorem mem_n_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g⁻¹ ∈ Nset k r := by
  have hg' := (nset_iff g).1 hg
  have hd := isUnit_of_uh hg'.1
  exact (nset_iff _).2 ⟨uh_inv hg'.1, col_of_left_inv hg'.2 (Matrix.nonsing_inv_mul g hd)⟩

end WeylGroupFacts

open WeylGroupFacts in
/- English proof (translation)
Unfold `NSubgroup`. Conclude with `fun k r => ⟨WeylGroupFacts.mem_n_one, fun g hg h hh => WeylGroupFacts.mem_n_mul hg hh, fun g hg => WeylGroupFacts.mem_n_inv hg⟩`.
-/
theorem unipotent_subgroup_holds : NSubgroup := by
  unfold NSubgroup
  exact fun k r => ⟨WeylGroupFacts.mem_n_one, fun g hg h hh => WeylGroupFacts.mem_n_mul hg hh,
    fun g hg => WeylGroupFacts.mem_n_inv hg⟩

namespace WeylGroupFacts

variable {k r : ℕ}

/- English proof (translation)
Establish `hij' : j ≠ i` using `fun e => by subst e; omega`. Rewrite using `[Matrix.mul_apply]`. Rewrite using `[Fintype.sum_eq_add j i hij']`. Rewrite using `[hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one, hg i i (by omega) (Or.inl le_rfl), if_pos rfl, one_mul]`. Introduce and unpack `p ⟨hpj, hpi⟩`.

Distinguish the cases in `h1 : j.val ≤ p.val ∨ r ≤ p.val`. Rewrite using `[hh p j hj h1, if_neg hpj, mul_zero]`. Distinguish the cases in `h2 : p.val ≤ i.val`. Rewrite using `[hg i p (by omega) (Or.inl h2), if_neg (Ne.symm hpi), zero_mul]`. It suffices to derive a contradiction.

Use linear arithmetic over natural numbers and integers.
-/
theorem mul_apply_add {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) (i j : Fin (2 * r + k + 1)) (hir : i.val < r)
    (hj : j.val ≤ r + k) (hij : i.val < j.val) (hji : j.val ≤ i.val + 1 ∨ r ≤ i.val + 1) :
    (g * h) i j = g i j + h i j := by
  have hij' : j ≠ i := fun e => by subst e; omega
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add j i hij']
  · rw [hh j j hj (Or.inl le_rfl), if_pos rfl, mul_one, hg i i (by omega) (Or.inl le_rfl), if_pos rfl,
      one_mul]
  · rintro p ⟨hpj, hpi⟩
    by_cases h1 : j.val ≤ p.val ∨ r ≤ p.val
    · rw [hh p j hj h1, if_neg hpj, mul_zero]
    · by_cases h2 : p.val ≤ i.val
      · rw [hg i p (by omega) (Or.inl h2), if_neg (Ne.symm hpi), zero_mul]
      · exfalso
        omega

/- English proof (translation)
Unfold `ell`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Establish `ha` using `a.isLt`. Distinguish the cases in `h1 : a.val + 1 < r`.

Simplify using `only [dif_pos h1]`. Conclude with `mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt) (by show a.val + 1 ≤ r + k; omega) (by show a.val < a.val + 1; omega) (by show a.val + 1 ≤ a.val + 1 ∨ r ≤ a.val + 1; omega)`. Simplify using `only [dif_neg h1] first`. Consider the case `simp only [Matrix.mulVec, dotProduct]`. Consider the case `simp only [Matrix.mulVec, Matrix.dotProduct]`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun q _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hq : q.val < r ∨ r + k < q.val`. Rewrite using `[hz q hq]`. Simplify using the standard rewrite rules.

Rewrite using `[mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt) (by omega) (by show a.val < q.val; omega) (Or.inr (by show r ≤ a.val + 1; omega)), add_mul]`.
-/
theorem ell_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : ell k r z (g * h) = ell k r z g + ell k r z h := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have ha := a.isLt
  by_cases h1 : a.val + 1 < r
  · simp only [dif_pos h1]
    exact mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt)
      (by show a.val + 1 ≤ r + k; omega) (by show a.val < a.val + 1; omega)
      (by show a.val + 1 ≤ a.val + 1 ∨ r ≤ a.val + 1; omega)
  · simp only [dif_neg h1]
    first
      | simp only [Matrix.mulVec, dotProduct]
      | simp only [Matrix.mulVec, Matrix.dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : q.val < r ∨ r + k < q.val
    · rw [hz q hq]
      simp
    · rw [mul_apply_add hg hh _ _ (by show a.val < r; exact a.isLt) (by omega)
        (by show a.val < q.val; omega) (Or.inr (by show r ≤ a.val + 1; omega)), add_mul]

end WeylGroupFacts

open WeylGroupFacts in
/- English proof (translation)
Unfold `EllAdd`. Introduce `k r z hz g hg h hh`. Conclude with `ell_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2`.
-/
theorem length_additive_holds : EllAdd := by
  unfold EllAdd
  intro k r z hz g hg h hh
  exact ell_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2

/- English proof (translation)
Unfold `PsiChar`. Introduce `k r z c hz g hg`. Use `⟨fun h hh => ?_, ?_⟩` and prove the remaining obligations. Unfold `psi`. Rewrite using `[WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff g).1 hg).2 ((WeylGroupFacts.nset_iff h).1 hh).2]`.

Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [mul_add, Complex.add_re, Complex.ofReal_add]`. Unfold `psi`. Rewrite using `[mul_comm Complex.I]`.

Use `first`. Consider the case `exact Complex.norm_exp_ofReal_mul_I _`. Consider the case `simp [Complex.norm_exp]`.
-/
theorem additive_character_holds : PsiChar := by
  unfold PsiChar
  intro k r z c hz g hg
  refine ⟨fun h hh => ?_, ?_⟩
  · unfold psi
    rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff g).1 hg).2 ((WeylGroupFacts.nset_iff h).1 hh).2]
    rw [← Complex.exp_add]
    congr 1
    simp only [mul_add, Complex.add_re, Complex.ofReal_add]
  · unfold psi
    rw [mul_comm Complex.I]
    first
      | exact Complex.norm_exp_ofReal_mul_I _
      | simp [Complex.norm_exp]

namespace WeylGroupFacts

variable {k r : ℕ}

/- English proof (translation)
Establish `hb : ∀ q : Fin (2 * r + k + 1), bvec c q = if q = c then 1 else 0` using `fun q => Pi.single_apply c 1 q`. Establish `h1` using `congrFun hc p`. Use `first`. Consider the case `(simp only [Matrix.mulVec, dotProduct, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1; exact h1)`. Consider the case `simpa [Matrix.mulVec, dotProduct, hb] using h1`.

Consider the case `simpa [Matrix.mulVec, Matrix.dotProduct, hb] using h1`.
-/
theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have hb : ∀ q : Fin (2 * r + k + 1), bvec c q = if q = c then 1 else 0 :=
    fun q => Pi.single_apply c 1 q
  have h1 := congrFun hc p
  first
    | (simp only [Matrix.mulVec, dotProduct, hb, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1; exact h1)
    | simpa [Matrix.mulVec, dotProduct, hb] using h1
    | simpa [Matrix.mulVec, Matrix.dotProduct, hb] using h1

/- English proof (translation)
Establish `h1 : hᴴ * Hpk k r * h = Hpk k r` using `hU`. Establish `h2` using `congrFun (congrFun h1 c) j`. Establish `h3 : ∀ q, (hᴴ * Hpk k r) c q = Hpk k r c q`. Introduce `q`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single c]`.

Rewrite using `[Matrix.conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul]`. Introduce `p hp`. Rewrite using `[Matrix.conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]`. Rewrite `h2` using `[Matrix.mul_apply]`. Simplify using `only [h3] at h2`.

Rewrite `h2` using `[Fintype.sum_eq_single (tau k r c)]`. Rewrite `h2` using `[hpk_row, if_pos rfl, hpk_row]`. Establish `hs : sgn k r c * sgn k r c = 1` using `sgn_mul_self c`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hj : j = tau k r c`.

Rewrite using `[if_pos hj, if_pos hj.symm, hs]`. Rewrite using `[if_neg hj, if_neg (Ne.symm hj), mul_zero]`. Introduce `q hq`. Rewrite using `[hpk_row, if_neg hq, zero_mul]`.
-/
theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hU
  have h2 := congrFun (congrFun h1 c) j
  have h3 : ∀ q, (hᴴ * Hpk k r) c q = Hpk k r c q := by
    intro q
    rw [Matrix.mul_apply, Fintype.sum_eq_single c]
    · rw [Matrix.conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul]
    · intro p hp
      rw [Matrix.conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  rw [Matrix.mul_apply] at h2
  simp only [h3] at h2
  rw [Fintype.sum_eq_single (tau k r c)] at h2
  · rw [hpk_row, if_pos rfl, hpk_row] at h2
    have hs : sgn k r c * sgn k r c = 1 := sgn_mul_self c
    calc h (tau k r c) j = (sgn k r c * sgn k r c) * h (tau k r c) j := by rw [hs, one_mul]
      _ = sgn k r c * (sgn k r c * h (tau k r c) j) := by ring
      _ = sgn k r c * (if j = tau k r c then sgn k r c else 0) := by rw [h2]
      _ = if tau k r c = j then 1 else 0 := by
          by_cases hj : j = tau k r c
          · rw [if_pos hj, if_pos hj.symm, hs]
          · rw [if_neg hj, if_neg (Ne.symm hj), mul_zero]
  · intro q hq
    rw [hpk_row, if_neg hq, zero_mul]

/- English proof (translation)
Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Take `⟨_, hfix, _⟩` from `hh`. Break down `hc with hc | hc` into its components or cases. Establish `e` using `(hfix ⟨c.val, hc⟩).1`. Establish `he : eI k r ⟨c.val, hc⟩ = c` using `Fin.ext rfl`.

Rewrite `e` using `[he]`. Conclude with `col_of_fix e p`. Establish `hcl` using `c.isLt`. Establish `hc' : 2 * r + k - c.val < r` using `by omega`. Establish `e` using `(hfix ⟨2 * r + k - c.val, hc'⟩).2`.

Establish `he : esI k r ⟨2 * r + k - c.val, hc'⟩ = c`. Apply `Fin.ext` to reduce the goal to its premises. Use `show 2 * r + k - (2 * r + k - c.val) = c.val`. Use linear arithmetic over natural numbers and integers. Rewrite `e` using `[he]`.

Conclude with `col_of_fix e p`.
-/
theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨_, hfix, _⟩ := hh
  rcases hc with hc | hc
  · have e := (hfix ⟨c.val, hc⟩).1
    have he : eI k r ⟨c.val, hc⟩ = c := Fin.ext rfl
    rw [he] at e
    exact col_of_fix e p
  · have hcl := c.isLt
    have hc' : 2 * r + k - c.val < r := by omega
    have e := (hfix ⟨2 * r + k - c.val, hc'⟩).2
    have he : esI k r ⟨2 * r + k - c.val, hc'⟩ = c := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - c.val) = c.val
      omega
    rw [he] at e
    exact col_of_fix e p

/- English proof (translation)
Establish `hi'` using `i.isLt`. Simplify using `only [tau, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  have hi' := i.isLt
  simp only [tau, Fin.val_mk]
  split_ifs <;> omega

/- English proof (translation)
Establish `hU : h ∈ UH (Hpk k r)`. Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Conclude with `hh.1`. Unfold `block`. Use `⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩` and prove the remaining obligations.

Establish `hc` using `uw_fixed_col hh (tau k r i) (tau_out i hi)`. Establish `e` using `row_of_fixed_col hU (tau k r i) hc j`. Rewrite `e` using `[tau_tau]`. Conclude with `e`.
-/
theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  have hU : h ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hh
    exact hh.1
  unfold block
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have hc := uw_fixed_col hh (tau k r i) (tau_out i hi)
  have e := row_of_fixed_col hU (tau k r i) hc j
  rw [tau_tau] at e
  exact e

/- English proof (translation)
Simplify using `only [UWset, Set.mem_setOf_eq] at hh ⊢`. Take `⟨hU, hfix, hz⟩` from `hh`. Establish `hd` using `isUnit_of_uh hU`. Establish `key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v`. Introduce `v hv`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨uh_inv hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩`.
-/
theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at hh ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  have hd := isUnit_of_uh hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = (h⁻¹ * h) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [Matrix.nonsing_inv_mul h hd, Matrix.one_mulVec]
  exact ⟨uh_inv hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

/- English proof (translation)
Simplify using `only [UWset, Set.mem_setOf_eq] at hh hh' ⊢`. Take `⟨hU, hfix, hz⟩` from `hh`. Take `⟨hU', hfix', hz'⟩` from `hh'`. Establish `key : ∀ v, h *ᵥ v = v → h' *ᵥ v = v → (h * h') *ᵥ v = v`. Introduce `v hv hv'`.

Rewrite using `[← Matrix.mulVec_mulVec, hv', hv]`. Conclude with `⟨uh_mul hU hU', fun a => ⟨key _ (hfix a).1 (hfix' a).1, key _ (hfix a).2 (hfix' a).2⟩, key _ hz hz'⟩`.
-/
theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh' ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  obtain ⟨hU', hfix', hz'⟩ := hh'
  have key : ∀ v, h *ᵥ v = v → h' *ᵥ v = v → (h * h') *ᵥ v = v := by
    intro v hv hv'
    rw [← Matrix.mulVec_mulVec, hv', hv]
  exact ⟨uh_mul hU hU', fun a => ⟨key _ (hfix a).1 (hfix' a).1, key _ (hfix a).2 (hfix' a).2⟩,
    key _ hz hz'⟩

/- English proof (translation)
Unfold `block at hh`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single q]`. Rewrite using `[hg q q hq (Or.inl le_rfl), if_pos rfl, mul_one]`. Introduce `p hp`. Distinguish the cases in `h1 : q.val ≤ p.val ∨ r ≤ p.val`.

Rewrite using `[hg p q hq h1, if_neg hp, mul_zero]`. Establish `hz : h i p = 0`. Rewrite using `[hh.1 i p (Or.inl (by omega)), if_neg]`. Introduce `hip`. Substitute `hip` using the available equality.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hz, zero_mul]`.
-/
theorem block_mul_col {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q := by
  unfold block at hh
  rw [Matrix.mul_apply, Fintype.sum_eq_single q]
  · rw [hg q q hq (Or.inl le_rfl), if_pos rfl, mul_one]
  · intro p hp
    by_cases h1 : q.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p q hq h1, if_neg hp, mul_zero]
    · have hz : h i p = 0 := by
        rw [hh.1 i p (Or.inl (by omega)), if_neg]
        intro hip
        subst hip
        omega
      rw [hz, zero_mul]

/- English proof (translation)
Unfold `block at hh hh'`. Introduce `i j hj hij`. Establish `key : ∀ p, (h * g) i p * h' p j = h i p * h' p j`. Introduce `p`. Distinguish the cases in `hpj : p = j`.

Rewrite using `[hpj, block_mul_col (by unfold block; exact hh) hg i j hj hij]`. Distinguish the cases in `hjm : j.val < r`. Rewrite using `[hh'.1 p j (Or.inl hjm), if_neg hpj, mul_zero, mul_zero]`. Distinguish the cases in `hpm : p.val < r ∨ r + k < p.val`. Rewrite using `[hh'.2 p j hpm, if_neg hpj, mul_zero, mul_zero]`.

Rewrite using `[block_mul_col (by unfold block; exact hh) hg i p (by omega) (Or.inr (by omega))]`. Establish `e : (h * g * h') i j = (h * h') i j`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl (fun p _ => key p)`. Rewrite using `[e, hinv, Matrix.one_apply]`.
-/
theorem conj_col {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') := by
  unfold block at hh hh'
  intro i j hj hij
  have key : ∀ p, (h * g) i p * h' p j = h i p * h' p j := by
    intro p
    by_cases hpj : p = j
    · rw [hpj, block_mul_col (by unfold block; exact hh) hg i j hj hij]
    · by_cases hjm : j.val < r
      · rw [hh'.1 p j (Or.inl hjm), if_neg hpj, mul_zero, mul_zero]
      · by_cases hpm : p.val < r ∨ r + k < p.val
        · rw [hh'.2 p j hpm, if_neg hpj, mul_zero, mul_zero]
        · rw [block_mul_col (by unfold block; exact hh) hg i p (by omega) (Or.inr (by omega))]
  have e : (h * g * h') i j = (h * h') i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun p _ => key p)
  rw [e, hinv, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single i]`. Rewrite using `[hrow i, if_pos rfl, one_mul]`. Introduce `p hp`. Rewrite using `[hrow p, if_neg (Ne.symm hp), zero_mul]`.
-/
theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  · rw [hrow i, if_pos rfl, one_mul]
  · intro p hp
    rw [hrow p, if_neg (Ne.symm hp), zero_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single j]`. Rewrite using `[hcol j, if_pos rfl, mul_one]`. Introduce `q hq`. Rewrite using `[hcol q, if_neg hq, mul_zero]`.
-/
theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · rw [hcol j, if_pos rfl, mul_one]
  · intro q hq
    rw [hcol q, if_neg hq, mul_zero]

/- English proof (translation)
Use `first`. Consider the case `simp only [Matrix.mulVec, dotProduct]`. Consider the case `simp only [Matrix.mulVec, Matrix.dotProduct]`. Rewrite using `[Fintype.sum_eq_single i]`. Rewrite using `[hrow i, if_pos rfl, one_mul]`.

Introduce `p hp`. Rewrite using `[hrow p, if_neg (Ne.symm hp), zero_mul]`.
-/
theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  first
    | simp only [Matrix.mulVec, dotProduct]
    | simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [Fintype.sum_eq_single i]
  · rw [hrow i, if_pos rfl, one_mul]
  · intro p hp
    rw [hrow p, if_neg (Ne.symm hp), zero_mul]

/- English proof (translation)
Unfold `block at hh hh'`. Unfold `ell`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Establish `hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0` using `fun p => hh.2 (eI k r a) p (Or.inl a.isLt)`. Distinguish the cases in `h1 : a.val + 1 < r`.

Simplify using `only [dif_pos h1]`. Rewrite using `[mul_assoc, mul_apply_of_row _ _ _ hrow]`. Conclude with `mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (Or.inl h1))`. Simplify using `only [dif_neg h1]`. Rewrite using `[mul_assoc, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, ← Matrix.mulVec_mulVec, hz]`.
-/
theorem ell_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold block at hh hh'
  unfold ell
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 (eI k r a) p (Or.inl a.isLt)
  by_cases h1 : a.val + 1 < r
  · simp only [dif_pos h1]
    rw [mul_assoc, mul_apply_of_row _ _ _ hrow]
    exact mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (Or.inl h1))
  · simp only [dif_neg h1]
    rw [mul_assoc, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, ← Matrix.mulVec_mulVec, hz]

end WeylGroupFacts

open WeylGroupFacts in
/- English proof (translation)
Unfold `UWNormal`. Introduce `k r z hz h hh g hg`. Establish `hg'` using `(nset_iff g).1 hg`. Establish `hinv` using `uw_inv hh`. Establish `hb` using `uw_block hh`.

Establish `hb'` using `uw_block hinv`. Establish `hU : h ∈ UH (Hpk k r)`. Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Conclude with `hh.1`. Establish `hUi : h⁻¹ ∈ UH (Hpk k r)`.

Simplify using `only [UWset, Set.mem_setOf_eq] at hinv`. Conclude with `hinv.1`. Establish `hzi : h⁻¹ *ᵥ z = z`. Simplify using `only [UWset, Set.mem_setOf_eq] at hinv`. Conclude with `hinv.2.2`.

Establish `hd` using `isUnit_of_uh hU`. Conclude with `⟨(nset_iff _).2 ⟨uh_mul (uh_mul hU hg'.1) hUi, conj_col hb hb' (Matrix.mul_nonsing_inv h hd) hg'.2⟩, ell_conj z hb hb' hzi⟩`.
-/
theorem unitary_weyl_normal_holds : UWNormal := by
  unfold UWNormal
  intro k r z hz h hh g hg
  have hg' := (nset_iff g).1 hg
  have hinv := uw_inv hh
  have hb := uw_block hh
  have hb' := uw_block hinv
  have hU : h ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hh
    exact hh.1
  have hUi : h⁻¹ ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.1
  have hzi : h⁻¹ *ᵥ z = z := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.2.2
  have hd := isUnit_of_uh hU
  exact ⟨(nset_iff _).2 ⟨uh_mul (uh_mul hU hg'.1) hUi,
    conj_col hb hb' (Matrix.mul_nonsing_inv h hd) hg'.2⟩, ell_conj z hb hb' hzi⟩

open WeylGroupFacts in
/- English proof (translation)
Unfold `SGroup`. Introduce `k r z hz`. Establish `hN` using `unipotent_subgroup_holds k r`. Establish `hW` using `unitary_weyl_normal_holds k r z hz`. Establish `hW1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z`.

Simplify using `only [UWset, Set.mem_setOf_eq]`. Conclude with `⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩`. Simplify using `only [Sset, Set.mem_setOf_eq]`. Use `⟨⟨1, hW1, 1, hN.1, (mul_one 1).symm⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `s ⟨h, hh, m, hm, rfl⟩ t ⟨h', hh', m', hm', rfl⟩`.

Establish `hU' : h' ∈ UH (Hpk k r)`. Simplify using `only [UWset, Set.mem_setOf_eq] at hh'`. Conclude with `hh'.1`. Establish `hd'` using `isUnit_of_uh hU'`. Establish `hc` using `(hW h'⁻¹ (uw_inv hh') m hm).1`.

Rewrite `hc` using `[Matrix.nonsing_inv_nonsing_inv h' hd']`. Use `⟨h * h', uw_mul hh hh', h'⁻¹ * m * h' * m', hN.2.1 _ hc _ hm', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv h' hd', mul_one]`. Simplify using `only [mul_assoc]`.

Use `_ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [mul_assoc]`. Introduce and unpack `s ⟨h, hh, m, hm, rfl⟩`. Establish `hU : h ∈ UH (Hpk k r)`. Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Conclude with `hh.1`.

Establish `hd` using `isUnit_of_uh hU`. Establish `hc` using `(hW h hh m⁻¹ (hN.2.2 m hm)).1`. Use `⟨h⁻¹, uw_inv hh, h * m⁻¹ * h⁻¹, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem symmetric_group_holds : SGroup := by
  unfold SGroup
  intro k r z hz
  have hN := unipotent_subgroup_holds k r
  have hW := unitary_weyl_normal_holds k r z hz
  have hW1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
    simp only [UWset, Set.mem_setOf_eq]
    exact ⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨⟨1, hW1, 1, hN.1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro s ⟨h, hh, m, hm, rfl⟩ t ⟨h', hh', m', hm', rfl⟩
    have hU' : h' ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh'
      exact hh'.1
    have hd' := isUnit_of_uh hU'
    have hc := (hW h'⁻¹ (uw_inv hh') m hm).1
    rw [Matrix.nonsing_inv_nonsing_inv h' hd'] at hc
    refine ⟨h * h', uw_mul hh hh', h'⁻¹ * m * h' * m', hN.2.1 _ hc _ hm', ?_⟩
    calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
          rw [Matrix.mul_nonsing_inv h' hd', mul_one]
          simp only [mul_assoc]
      _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [mul_assoc]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hd := isUnit_of_uh hU
    have hc := (hW h hh m⁻¹ (hN.2.2 m hm)).1
    refine ⟨h⁻¹, uw_inv hh, h * m⁻¹ * h⁻¹, hc, ?_⟩
    rw [Matrix.mul_inv_rev]
    calc m⁻¹ * h⁻¹ = h⁻¹ * h * m⁻¹ * h⁻¹ := by rw [Matrix.nonsing_inv_mul h hd, one_mul]
      _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [mul_assoc]

end Formalism.QuantumDeterminants
