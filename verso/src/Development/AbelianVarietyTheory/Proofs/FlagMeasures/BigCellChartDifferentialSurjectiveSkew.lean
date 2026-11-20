import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterizationStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Onto

open Formalism.QuantumDeterminants.GBasic

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Establish `hs` using `sig_val k r i`. Unfold `wC bigCell esI`. Simplify using `only [Fin.ext_iff, Matrix.one_apply, star_one, inv_one]`.

Apply the tactic sequence `split_ifs at * <;> first | rfl | (exfalso; omega)`.
-/
lemma wC_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if j = sig k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  unfold wC bigCell esI
  simp only [Fin.ext_iff, Matrix.one_apply, star_one, inv_one]
  split_ifs at * <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, wC_eq k r i, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [wC_eq, eq_sig_iff k r j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
lemma conj_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sig k r i) (sig k r j) := by
  simp only [Matrix.mul_apply, wC_eq k r i, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [wC_eq, eq_sig_iff k r j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/- English proof (translation)
Simplify using `only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [Hpk_eq, eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sgn_sig]`.
-/
lemma skew_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Mᴴ * Hpk k r + Hpk k r * M) i j =
      star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j := by
  simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Hpk_eq k r i, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Hpk_eq, eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sgn_sig]

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Simplify using `only [skew_apply, Matrix.zero_apply]`.
-/
lemma skew_iff (k r : ℕ) (M : Mat k r) :
    Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
      ∀ i j, star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [skew_apply, Matrix.zero_apply]

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hs` using `sig_val k r i`. Unfold `lev`. Apply the tactic sequence `split_ifs at * <;> omega`.
-/
lemma lev_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : lev k r (sig k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sig_val k r i
  unfold lev
  split_ifs at * <;> omega

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify, realifyFun]`.
-/
lemma unre {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

/- English proof (translation)
Use `⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0)), ?_⟩, unre _⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1, unre]`. Use `⟨?_, fun i j hij => by simp [not_lt.2 hij]⟩` and prove the remaining obligations. Rewrite `h`, the goal using `[skew_iff]`. Introduce `i j`.

Establish `h1` using `lev_sig k r i`. Establish `h2` using `lev_sig k r j`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `c : lev k r (sig k r j) < lev k r i`. Rewrite using `[if_pos c, if_pos (by omega)]; exact h i j`.

Rewrite using `[if_neg c, if_neg (by omega)]; simp`.
-/
lemma exists_N (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ X : lieE (Nset k r), um X = Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun
    (Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1, unre]
  refine ⟨?_, fun i j hij => by simp [not_lt.2 hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  simp only [Matrix.of_apply]
  by_cases c : lev k r (sig k r j) < lev k r i
  · rw [if_pos c, if_pos (by omega)]; exact h i j
  · rw [if_neg c, if_neg (by omega)]; simp

/- English proof (translation)
Use `⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j => if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0)), ?_⟩, unre _⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.1, unre]`. Use `⟨?_, fun i j hij => by simp only [Matrix.of_apply, if_neg hij]⟩` and prove the remaining obligations. Rewrite `h`, the goal using `[skew_iff]`. Introduce `i j`.

Establish `h1` using `sig_val k r i`. Establish `h2` using `sig_val k r j`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Matrix.of_apply]`.

Distinguish the cases in `c : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`. Apply the tactic sequence `rw [if_pos (by split_ifs at h1 h2 <;> omega), if_pos (by split_ifs at h1 h2 <;> omega)]`. Conclude with `h i j`. Apply the tactic sequence `rw [if_neg (by split_ifs at h1 h2 <;> omega), if_neg (by split_ifs at h1 h2 <;> omega)]`. Simplify using the standard rewrite rules.
-/
lemma exists_lieElement_middleBlockPart (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ Y : lieE (Formalism.FourierDecayAlt.B2.UWb k r), um Y = Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.1, unre]
  refine ⟨?_, fun i j hij => by simp only [Matrix.of_apply, if_neg hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := sig_val k r i
  have h2 := sig_val k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.of_apply]
  by_cases c : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos (by split_ifs at h1 h2 <;> omega), if_pos (by split_ifs at h1 h2 <;> omega)]
    exact h i j
  · rw [if_neg (by split_ifs at h1 h2 <;> omega), if_neg (by split_ifs at h1 h2 <;> omega)]
    simp

/- English proof (translation)
Introduce `k r Z hZ`. Establish `hZ'` using `(skew_iff k r Z).1 hZ`. Take `⟨X', hX'⟩` from `exists_N k r Z hZ`. Take `⟨Y, hY⟩` from `exists_lieElement_middleBlockPart k r Z hZ`. Take `⟨X, hX⟩` from `exists_N k r (Matrix.of fun i j => -Z (sig k r i) (sig k r j)) (by`.

Rewrite using `[skew_iff]`. Introduce `i j`. Use `hZ' (sig k r i) (sig k r j)` as an intermediate fact. Simplify using `only [sig_sig, sgn_sig] at this`. Simplify using `only [Matrix.of_apply, sig_sig, star_neg]`.

Take the linear combination `-this)`. Use `⟨((X, X'), (fun a => Z (eI k r a) (eI k r a), Y)), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1` using `lev_sig k r i`. Establish `h2` using `lev_sig k r j`.

Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [dchart, Matrix.add_apply, Matrix.neg_apply, conj_apply, hX, hX', hY, Matrix.of_apply, sig_sig, torD, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `only [lt_irrefl, if_false, if_true, neg_zero, zero_add, add_zero, and_self]`. Distinguish the cases in `c : i.val < r`. Rewrite using `[dif_pos c, if_neg (by omega), add_zero]; rfl`. Rewrite using `[dif_neg c]`. Distinguish the cases in `c' : r + k < i.val`.

Rewrite using `[dif_pos c', if_neg (by omega), add_zero]`. Establish `e : eI k r ⟨2 * r + k - i.val, by omega⟩ = sig k r i` using `Fin.ext (by rw [sig_hi k r i c']; rfl)`. Rewrite using `[e]`. Use `hZ' (sig k r i) i` as an intermediate fact. Rewrite `this` using `[sgn_sig, sig_sig]`.

Establish `hs : sgn k r i = 1` using `by unfold sgn; rw [if_neg (by omega)]`. Rewrite `this` using `[hs]`. Take the linear combination `-this`. Rewrite using `[dif_neg c', if_pos (by omega), zero_add]`. Rewrite using `[if_neg hij, add_zero]`.

Establish `hij' : i.val ≠ j.val` using `fun h => hij (Fin.ext h)`. Establish `l1 : lev k r i = if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k` using `rfl`. Establish `l2 : lev k r j = if j.val < r then j.val else if j.val ≤ r + k then r else j.val - k` using `rfl`. Break down `lt_trichotomy (lev k r i) (lev k r j) with c | c | c` into its components or cases. Apply the tactic sequence `rw [if_neg (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_pos c]; simp`.

Apply the tactic sequence `rw [if_neg (by omega), if_pos (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp`. Apply the tactic sequence `rw [if_pos (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp`.
-/
theorem dchart_onto : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 →
    ∃ v : EE k r, dchart k r v = Z := by
  intro k r Z hZ
  have hZ' := (skew_iff k r Z).1 hZ
  obtain ⟨X', hX'⟩ := exists_N k r Z hZ
  obtain ⟨Y, hY⟩ := exists_lieElement_middleBlockPart k r Z hZ
  obtain ⟨X, hX⟩ := exists_N k r (Matrix.of fun i j => -Z (sig k r i) (sig k r j)) (by
    rw [skew_iff]
    intro i j
    have := hZ' (sig k r i) (sig k r j)
    simp only [sig_sig, sgn_sig] at this
    simp only [Matrix.of_apply, sig_sig, star_neg]
    linear_combination -this)
  refine ⟨((X, X'), (fun a => Z (eI k r a) (eI k r a), Y)), ?_⟩
  ext i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [dchart, Matrix.add_apply, Matrix.neg_apply, conj_apply, hX, hX', hY, Matrix.of_apply,
    sig_sig, torD, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [lt_irrefl, if_false, if_true, neg_zero, zero_add, add_zero, and_self]
    by_cases c : i.val < r
    · rw [dif_pos c, if_neg (by omega), add_zero]; rfl
    · rw [dif_neg c]
      by_cases c' : r + k < i.val
      · rw [dif_pos c', if_neg (by omega), add_zero]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = sig k r i :=
          Fin.ext (by rw [sig_hi k r i c']; rfl)
        rw [e]
        have := hZ' (sig k r i) i
        rw [sgn_sig, sig_sig] at this
        have hs : sgn k r i = 1 := by unfold sgn; rw [if_neg (by omega)]
        rw [hs] at this
        linear_combination -this
      · rw [dif_neg c', if_pos (by omega), zero_add]
  · rw [if_neg hij, add_zero]
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have l1 : lev k r i = if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k := rfl
    have l2 : lev k r j = if j.val < r then j.val else if j.val ≤ r + k then r else j.val - k := rfl
    rcases lt_trichotomy (lev k r i) (lev k r j) with c | c | c
    · rw [if_neg (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_pos c]; simp
    · rw [if_neg (by omega), if_pos (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp

end GlobalTheory.CellDens.Onto
