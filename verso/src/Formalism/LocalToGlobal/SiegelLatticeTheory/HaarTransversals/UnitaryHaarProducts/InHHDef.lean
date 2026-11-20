import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace Formalism.L2.SG.PoincareInHH.Cut

section Pure

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]`.
-/
private lemma hJ_eq_lemma (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then (1 : ℂ) else -1) * y i) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hJ_eq_lemma]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `_ = ∑ i, ∑ j, ∑ k, star (a j) * b k * (star (x j i) * ((if ε i then (1 : ℂ) else -1) * y k i)) := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[star_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ j, ∑ k, conj (a j) * b k * hJ ε (x j) (y k) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hJ_eq_lemma, Finset.mul_sum, starRingEnd_apply]`.
-/
theorem hJ_sum_sum (ε : Fin n → Bool) {ι : Type} [Fintype ι] (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    hJ ε (∑ j, a j • x j) (∑ k, b k • y k) = ∑ j, ∑ k, conj (a j) * b k * hJ ε (x j) (y k) := by
  calc hJ ε (∑ j, a j • x j) (∑ k, b k • y k)
      = ∑ i, star (∑ j, a j * x j i) * ((if ε i then (1 : ℂ) else -1) * ∑ k, b k * y k i) := by
        rw [hJ_eq_lemma]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i, ∑ j, ∑ k, star (a j) * b k * (star (x j i) * ((if ε i then (1 : ℂ) else -1) * y k i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [star_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [star_mul']; ring
    _ = ∑ j, ∑ k, conj (a j) * b k * hJ ε (x j) (y k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hJ_eq_lemma, Finset.mul_sum, starRingEnd_apply]

/- English proof (translation)
Rewrite using `[hJ_eq_lemma, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hr : (star (y i)).re = (y i).re` using `rfl`. Establish `hi : (star (y i)).im = -(y i).im` using `rfl`. Apply the tactic sequence `split_ifs <;> simp only [Complex.mul_re, Complex.mul_im, hr, hi, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.normSq_apply] <;> ring`.
-/
theorem hJ_self_re (ε : Fin n → Bool) (y : Fin n → ℂ) :
    (hJ ε y y).re = ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq (y i) := by
  rw [hJ_eq_lemma, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (star (y i)).re = (y i).re := rfl
  have hi : (star (y i)).im = -(y i).im := rfl
  split_ifs <;> simp only [Complex.mul_re, Complex.mul_im, hr, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.normSq_apply] <;> ring

/- English proof (translation)
Establish `hli : LinearIndependent ℂ (fun j (s : {i // ε i = false}) => w j s.val)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Use `set x : Fin n → ℂ := ∑ j, g j • w j with hx`. Establish `hπx : ∀ i, ε i = false → x i = 0`.

Introduce `i hi`. Establish `h` using `congrFun hg ⟨i, hi⟩`. Simplify `h` using `[hx, Finset.sum_apply]`. Establish `hnn : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (x i)`. Introduce `i _`.

Consider the cases of `h : ε i`. Simplify using `[hπx i h]`. Simplify using `[Complex.normSq_nonneg]`. Establish `hself : (hJ ε x x).re = ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq (x i)` using `hJ_self_re ε x`. Establish `hdiag : hJ ε x x = ∑ j, conj (g j) * g j * hJ ε (w j) (w j)`.

Rewrite using `[hx, hJ_sum_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Introduce `k _ hkj`. Rewrite using `[horth j k (Ne.symm hkj), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Establish `hre : (hJ ε x x).re = ∑ j, Complex.normSq (g j) * (hJ ε (w j) (w j)).re`. Rewrite using `[hdiag, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]`. Establish `hterm : ∀ j ∈ (univ : Finset (Fin (q + 1))), Complex.normSq (g j) * (hJ ε (w j) (w j)).re ≤ 0`. Introduce `j _`. Establish `h0` using `Complex.normSq_nonneg (g j)`. Distinguish the cases in `hj : j = Fin.last q`.

Substitute `hj` using the available equality. Use polynomial arithmetic with `[hlast]`. Use polynomial arithmetic with `[hneg j hj]`. Establish `hzero : (hJ ε x x).re = 0` using `le_antisymm (by rw [hre]; exact Finset.sum_nonpos hterm) (by rw [hself]; exact Finset.sum_nonneg hnn)`. Establish `hg0 : ∀ j, j ≠ Fin.last q → g j = 0`.

Introduce `j hj`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonpos hterm).1 (by rw [← hre]; exact hzero) j (Finset.mem_univ j)`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `Complex.normSq_eq_zero.1 h`. Conclude with `absurd h (hneg j hj).ne`.

Establish `hx0 : x = 0`. Use function extensionality and compare the values at `i`. Consider the cases of `h : ε i`. Conclude with `hπx i h`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [← hself]; exact hzero) i (Finset.mem_univ i)`.

Rewrite `h1` using `[h]`. Simplify using `using h1`. Establish `hxl : x = g (Fin.last q) • w (Fin.last q)`. Rewrite using `[hx, Finset.sum_eq_single (Fin.last q)]`. Introduce `j _ hj`.

Rewrite using `[hg0 j hj, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `j`. Distinguish the cases in `hj : j = Fin.last q`.

Substitute `hj` using the available equality. Rewrite `hxl` using `[hx0]`. Conclude with `(smul_eq_zero.1 hxl.symm).resolve_right hne`. Conclude with `hg0 j hj`. Simplify `hli.fintype_card_le_finrank` using `[Fintype.card_subtype]`.
-/
theorem card_le_of_orth (ε : Fin n → Bool) (q : ℕ) (w : Fin (q + 1) → Fin n → ℂ)
    (horth : ∀ j k, j ≠ k → hJ ε (w j) (w k) = 0) (hneg : ∀ j : Fin (q + 1), j ≠ Fin.last q → (hJ ε (w j) (w j)).re < 0)
    (hlast : (hJ ε (w (Fin.last q)) (w (Fin.last q))).re ≤ 0) (hne : w (Fin.last q) ≠ 0) :
    q + 1 ≤ (univ.filter fun i => ε i = false).card := by
  classical
  have hli : LinearIndependent ℂ (fun j (s : {i // ε i = false}) => w j s.val) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set x : Fin n → ℂ := ∑ j, g j • w j with hx
    have hπx : ∀ i, ε i = false → x i = 0 := by
      intro i hi
      have h := congrFun hg ⟨i, hi⟩
      simpa [hx, Finset.sum_apply] using h
    have hnn : ∀ i ∈ (univ : Finset (Fin n)),
        0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (x i) := by
      intro i _
      cases h : ε i
      · simp [hπx i h]
      · simp [Complex.normSq_nonneg]
    have hself : (hJ ε x x).re = ∑ i, (if ε i then (1 : ℝ) else -1) * Complex.normSq (x i) :=
      hJ_self_re ε x
    have hdiag : hJ ε x x = ∑ j, conj (g j) * g j * hJ ε (w j) (w j) := by
      rw [hx, hJ_sum_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single j]
      · intro k _ hkj; rw [horth j k (Ne.symm hkj), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hre : (hJ ε x x).re = ∑ j, Complex.normSq (g j) * (hJ ε (w j) (w j)).re := by
      rw [hdiag, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]
    have hterm : ∀ j ∈ (univ : Finset (Fin (q + 1))),
        Complex.normSq (g j) * (hJ ε (w j) (w j)).re ≤ 0 := by
      intro j _
      have h0 := Complex.normSq_nonneg (g j)
      by_cases hj : j = Fin.last q
      · subst hj; nlinarith [hlast]
      · nlinarith [hneg j hj]
    have hzero : (hJ ε x x).re = 0 :=
      le_antisymm (by rw [hre]; exact Finset.sum_nonpos hterm) (by rw [hself]; exact Finset.sum_nonneg hnn)
    have hg0 : ∀ j, j ≠ Fin.last q → g j = 0 := by
      intro j hj
      have h1 := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 (by rw [← hre]; exact hzero) j (Finset.mem_univ j)
      rcases mul_eq_zero.1 h1 with h | h
      · exact Complex.normSq_eq_zero.1 h
      · exact absurd h (hneg j hj).ne
    have hx0 : x = 0 := by
      funext i
      cases h : ε i
      · exact hπx i h
      · have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [← hself]; exact hzero) i (Finset.mem_univ i)
        rw [h] at h1
        simpa using h1
    have hxl : x = g (Fin.last q) • w (Fin.last q) := by
      rw [hx, Finset.sum_eq_single (Fin.last q)]
      · intro j _ hj; rw [hg0 j hj, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    intro j
    by_cases hj : j = Fin.last q
    · subst hj
      rw [hx0] at hxl
      exact (smul_eq_zero.1 hxl.symm).resolve_right hne
    · exact hg0 j hj
  simpa [Fintype.card_subtype] using hli.fintype_card_le_finrank

end Pure

section Pure2

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[hJ_eq_lemma, hJ_eq_lemma, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
theorem hJ_conj (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  rw [hJ_eq_lemma, hJ_eq_lemma, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

/- English proof (translation)
Use `card_le_of_orth ε q (Fin.snoc (α := fun _ => Fin n → ℂ) nv ξ) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j k hjk`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last => exact absurd rfl hjk`. Consider the case `cast k`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`. Rewrite using `[hJ_conj, hξ k, map_zero]`. Consider the case `cast j`.

Proceed by induction on `k using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`. Conclude with `hξ j`. Consider the case `cast k`.

Simplify using `only [Fin.snoc_castSucc]`. Conclude with `horth j k (fun h => hjk (by rw [h]))`. Introduce `j hj`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd rfl hj`.

Consider the case `cast j`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `hneg j`. Simplify using `using hξξ`. Simplify using `using hne`.
-/
theorem card_le_of_orth' (ε : Fin n → Bool) (q : ℕ) (nv : Fin q → Fin n → ℂ) (ξ : Fin n → ℂ)
    (horth : ∀ j k, j ≠ k → hJ ε (nv j) (nv k) = 0) (hneg : ∀ j, (hJ ε (nv j) (nv j)).re < 0)
    (hξ : ∀ j, hJ ε (nv j) ξ = 0) (hξξ : (hJ ε ξ ξ).re ≤ 0) (hne : ξ ≠ 0) :
    q + 1 ≤ (univ.filter fun i => ε i = false).card := by
  classical
  refine card_le_of_orth ε q (Fin.snoc (α := fun _ => Fin n → ℂ) nv ξ) ?_ ?_ ?_ ?_
  · intro j k hjk
    induction j using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => exact absurd rfl hjk
      | cast k =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hJ_conj, hξ k, map_zero]
    | cast j =>
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hξ j
      | cast k =>
        simp only [Fin.snoc_castSucc]
        exact horth j k (fun h => hjk (by rw [h]))
  · intro j hj
    induction j using Fin.lastCases with
    | last => exact absurd rfl hj
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact hneg j
  · simpa using hξξ
  · simpa using hne

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Establish `e : 2 * (s + 1) = 2 * s + 1 + 1` using `by ring`. Establish `h1 : (2 * s + 1) % 2 = 1` using `by omega`.

Establish `h2 : ¬ (2 * s) % 2 = 1` using `by omega`. Establish `h3 : 2 * s + 1 ∉ (range (2 * s)).filter fun t => t % 2 = 1`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Finset.range_add_one, Finset.range_add_one, Finset.filter_insert, Finset.filter_insert, if_pos h1, if_neg h2, Finset.card_insert_eq_ite, if_neg h3, ih]`.
-/
theorem card_odd_range (s : ℕ) : ((range (2 * s)).filter fun t => t % 2 = 1).card = s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : 2 * (s + 1) = 2 * s + 1 + 1 := by ring
    have h1 : (2 * s + 1) % 2 = 1 := by omega
    have h2 : ¬ (2 * s) % 2 = 1 := by omega
    have h3 : 2 * s + 1 ∉ (range (2 * s)).filter fun t => t % 2 = 1 := by
      simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [e, Finset.range_add_one, Finset.range_add_one, Finset.filter_insert, Finset.filter_insert, if_pos h1,
      if_neg h2, Finset.card_insert_eq_ite, if_neg h3, ih]

end Pure2

section Sig

/- English proof (translation)
Simplify using `only [epsS]`. Apply the tactic sequence `by_cases h : i.val < R.k - 1 <;> simp [h] <;> omega`.
-/
theorem epsS_false_iff (R : Formalism.BasicNotions.Ranks) (i : Fin R.r) :
    epsS R i = false ↔ R.k - 1 ≤ i.val ∧ (i.val - (R.k - 1)) % 2 = 1 := by
  simp only [epsS]
  by_cases h : i.val < R.k - 1 <;> simp [h] <;> omega

/- English proof (translation)
Establish `hr : R.r = R.k + R.m - 1` using `rfl`. Establish `h2` using `R.two_le_m`. Establish `hk` using `R.m_add_three_le_k`. Take `⟨s, hs⟩` from `R.m_even`. Establish `hrs : R.rS + 1 = s` using `by simp only [Formalism.BasicNotions.Ranks.rS]; omega`.

Rewrite using `[hrs, ← card_odd_range s]`. Use `Finset.card_bij' (fun i _ => i.val - (R.k - 1)) (fun t ht => ⟨t + (R.k - 1), ?_⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_range] at ht`. Use linear arithmetic over natural numbers and integers. Introduce `i hi`.

Use `i.isLt` as an intermediate fact. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff] at hi`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `t ht`.

Simplify using `only [Finset.mem_filter, Finset.mem_range] at ht`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff]`. Use linear arithmetic over natural numbers and integers. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff] at hi`.

Conclude with `Fin.ext (Nat.sub_add_cancel hi.1)`. Introduce `t _`. Conclude with `Nat.add_sub_cancel _ _`.
-/
theorem card_epsS_false (R : Formalism.BasicNotions.Ranks) : (univ.filter fun i : Fin R.r => epsS R i = false).card = R.rS + 1 := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have h2 := R.two_le_m
  have hk := R.m_add_three_le_k
  obtain ⟨s, hs⟩ := R.m_even
  have hrs : R.rS + 1 = s := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
  rw [hrs, ← card_odd_range s]
  refine Finset.card_bij' (fun i _ => i.val - (R.k - 1)) (fun t ht => ⟨t + (R.k - 1), ?_⟩) ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_range] at ht; omega
  · intro i hi
    have := i.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff] at hi
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff]; omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, epsS_false_iff] at hi
    exact Fin.ext (Nat.sub_add_cancel hi.1)
  · intro t _
    exact Nat.add_sub_cancel _ _

end Sig

section SettingDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hP` using `I.P_spec v`. Establish `hPu : IsUnit (I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)`. Establish `hL : I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) = star (fun i => I.φ v (x i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (y i))`. Simplify using `only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[starRingEnd_apply, I.cm.cmUnram.2.1, RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL]`. Unfold `hJ rv`. Rewrite using `[← hP, star_mulVec, ← dotProduct_mulVec]`.

Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc]`. Establish `h1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1`. Rewrite using `[← conjTranspose_mul, mul_nonsing_inv _ hPu, conjTranspose_one]`. Establish `h2 : I.P v * (I.P v)⁻¹ = 1` using `mul_nonsing_inv _ hPu`. Rewrite using `[h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem phi_hform (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) = hJ (I.ε v) (rv I v x) (rv I v y) := by
  have hP := I.P_spec v
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hL : I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) =
      star (fun i => I.φ v (x i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (y i)) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [starRingEnd_apply, I.cm.cmUnram.2.1, RCLike.star_def]
    ring
  rw [hL]
  unfold hJ rv
  rw [← hP, star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  have h1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ hPu, conjTranspose_one]
  have h2 : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hPu
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [hJ_eq_lemma, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hJ_sub_left {n : ℕ} (ε : Fin n → Bool) (a b c : Fin n → ℂ) : hJ ε (a - b) c = hJ ε a c - hJ ε b c := by
  simp only [hJ_eq_lemma, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hJ_eq_lemma, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hJ_sub_right {n : ℕ} (ε : Fin n → Bool) (a b c : Fin n → ℂ) : hJ ε a (b - c) = hJ ε a b - hJ ε a c := by
  simp only [hJ_eq_lemma, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h1 : D.host.φ₀ (D.host.conj c) = starRingEnd ℂ (D.host.φ₀ c)`. Rewrite using `[← D.embE_φ₀]`. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[D.embE_conj, D.starLL_cx]`. Establish `h2 : D.host.φ₀ (star c) = starRingEnd ℂ (D.host.φ₀ c)` using `NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ c`. Rewrite using `[h1, h2]`.
-/
private lemma host_conj_eq_star (D : D7) (c : D.host.E) : D.host.conj c = star c := by
  haveI := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj c) = starRingEnd ℂ (D.host.φ₀ c) := by
    rw [← D.embE_φ₀]
    simp only [RingHom.comp_apply]
    rw [D.embE_conj, D.starLL_cx]
  have h2 : D.host.φ₀ (star c) = starRingEnd ℂ (D.host.φ₀ c) :=
    NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ c
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[← phi_hform, X.φ_eq]`. Use `congr 1`. Simplify using `only [Formalism.UG.hform, map_sum, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, X.J_eq]`. Use `conv_rhs => rw [← X.bas.sum_repr p, ← X.bas.sum_repr q]`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]`.

Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hc : D.host.conj ((X.bas.repr p) i) = star ((X.bas.repr p) i)` using `host_conj_eq_star D _`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hJ_crd (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((VS D).hT p q) := by
  rw [← phi_hform, X.φ_eq]
  congr 1
  simp only [Formalism.UG.hform, map_sum, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj,
    RingEquiv.apply_symm_apply, X.J_eq]
  conv_rhs => rw [← X.bas.sum_repr p, ← X.bas.sum_repr q]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    RingHom.id_apply, starRingEnd_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : D.host.conj ((X.bas.repr p) i) = star ((X.bas.repr p) i) := host_conj_eq_star D _
  rw [hc]
  ring

/- English proof (translation)
Rewrite using `[← (VS D).herm.eq (X.eX b) (X.fY a), X.ef b a]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef b a]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← card_epsS_false D.R]`. Use `Finset.card_bij' (fun i _ => Fin.cast X.n_eq i) (fun j _ => Fin.cast X.n_eq.symm j) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢`. Rewrite `hi` using `[X.eps_eq v i]`. Then use the resulting hypothesis.

Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢`. Rewrite using `[X.eps_eq v]`. Simplify using `using hj`. Introduce `i _`.

Simplify using the standard rewrite rules. Introduce `j _`. Simplify using the standard rewrite rules.
-/
theorem card_eps_false (v : InfinitePlace X.B.I.F) :
    (univ.filter fun i : Fin X.B.I.n => X.B.I.ε v i = false).card = D.R.rS + 1 := by
  rw [← card_epsS_false D.R]
  refine Finset.card_bij' (fun i _ => Fin.cast X.n_eq i) (fun j _ => Fin.cast X.n_eq.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [X.eps_eq v i] at hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [X.eps_eq v]
    simpa using hj
  · intro i _
    simp
  · intro j _
    simp

/- English proof (translation)
Introduce `ι`. Use `left`. Introduce `x hx0 hxS`. Establish `hherm : star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x`. Establish `hJh` using `X.B.I.J_herm`.

Unfold `Formalism.UG.IsHerm Formalism.UG.cT at hJh`. Establish `hji : ∀ i j, starRingEnd X.B.I.E (X.B.I.J i j) = X.B.I.J j i` using `fun i j => by`. Use `congrFun (congrFun hJh j) i` as an intermediate fact. Simplify using `using this`. Simplify using `only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `hji j i` as an intermediate fact. Rewrite `this` using `[starRingEnd_apply]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `(X.B.I.cm.fixed _).1 hherm`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Use `set ψ : X.B.I.F →+* ℂ := Complex.ofRealHom.comp ι`. Establish `hψr : NumberField.ComplexEmbedding.IsReal ψ`.

Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `b`. Simplify using `[ψ, NumberField.ComplexEmbedding.conjugate_coe_eq]`. Use `set v : InfinitePlace X.B.I.F := InfinitePlace.mk ψ`. Establish `hemb : v.embedding = ψ` using `NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψr`.

Establish `hval : ((ι a : ℝ) : ℂ) = hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x)`. Rewrite using `[← phi_hform, ← ha, X.B.I.φ_over v a, hemb]`. Both sides reduce to the same expression. Establish `hre : ι a = (hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x)).re` using `by rw [← hval]; simp`. Rewrite using `[hre]`.

Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Set `nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ` to `fun j => if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u)`. Establish `hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ)` using `by exact_mod_cast (D.mem u).A.T_prime.pos`. Establish `hb` using `card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv (rv X.B.I v x) ?_ ?_ ?_ hle ?_`.

Rewrite `hb` using `[card_eps_false X v]`. Use linear arithmetic over natural numbers and integers. Introduce `j k hjk`. Simplify using `only [nv]`. Use `split_ifs with hj hk hk`.

Rewrite using `[hJ_sub_left, hJ_sub_right, hJ_sub_right]`. Simplify using `only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]`. Establish `hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩` using `fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))`. Establish `hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩` using `fun h => hne h.symm`. Simplify using `[hne, hne']`.

Rewrite using `[hJ_sub_left]`. Simplify using `only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u _).1, (X.zu_orth u _).2]`. Simplify using the standard rewrite rules. Rewrite using `[hJ_sub_right]`. Establish `h1` using `hJ_crd X v (X.zu u) (X.eX ⟨k.1, hk⟩)`.

Establish `h2` using `hJ_crd X v (X.zu u) (X.fY ⟨k.1, hk⟩)`. Establish `e1 : (VS D).hT (X.zu u) (X.eX ⟨k.1, hk⟩) = 0`. Rewrite using `[← (VS D).herm.eq, (X.zu_orth u _).1]`. Simplify using the standard rewrite rules. Establish `e2 : (VS D).hT (X.zu u) (X.fY ⟨k.1, hk⟩) = 0`.

Rewrite using `[← (VS D).herm.eq, (X.zu_orth u _).2]`. Simplify using the standard rewrite rules. Simplify using `only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]`. It suffices to derive a contradiction. Apply `hjk` to reduce the goal to its premises.

Use `ext`. Use linear arithmetic over natural numbers and integers. Introduce `j`. Simplify using `only [nv]`. Use `split_ifs with hj`.

Rewrite using `[hJ_sub_left, hJ_sub_right, hJ_sub_right]`. Simplify using `only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]`. Evaluate the numerical expressions. Simplify using `only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]`. Simplify using `only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]`.

Conclude with `(D.mem u).A.T_prime.pos` after adjusting the coercions. Introduce `j`. Simplify using `only [nv]`. Use `split_ifs with hj`. Rewrite using `[hJ_sub_left, ← phi_hform, ← phi_hform, hxS _ (eR_mem_fix X u _), hxS _ (fR_mem_fix X u _)]`.

Simplify using the standard rewrite rules. Rewrite using `[← phi_hform, hxS _ (zR_mem_fix X u)]`. Simplify using the standard rewrite rules. Introduce `h0`. Apply `hx0` to reduce the goal to its premises.

Establish `hPu : IsUnit (X.B.I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)`. Establish `hφ : (fun i => X.B.I.φ v (x i)) = 0`. Establish `: X.B.I.P v *ᵥ rv X.B.I v x = fun i => X.B.I.φ v (x i)`. Unfold `rv`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]`.

Rewrite using `[← this, h0, mulVec_zero]`. Use function extensionality and compare the values at `i`. Use `congrFun hφ i` as an intermediate fact. Simplify using `using this`.
-/
theorem wuDefinite_holds : WuDefinite X u := by
  intro ι
  left
  intro x hx0 hxS

  have hherm : star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x := by
    have hJh := X.B.I.J_herm
    unfold Formalism.UG.IsHerm Formalism.UG.cT at hJh
    have hji : ∀ i j, starRingEnd X.B.I.E (X.B.I.J i j) = X.B.I.J j i := fun i j => by
      have := congrFun (congrFun hJh j) i
      simpa using this
    simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hji j i
    rw [starRingEnd_apply] at this
    rw [this]; ring
  obtain ⟨a, ha⟩ := (X.B.I.cm.fixed _).1 hherm
  refine ⟨a, ha, ?_⟩

  set ψ : X.B.I.F →+* ℂ := Complex.ofRealHom.comp ι
  have hψr : NumberField.ComplexEmbedding.IsReal ψ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext b; simp [ψ, NumberField.ComplexEmbedding.conjugate_coe_eq]
  set v : InfinitePlace X.B.I.F := InfinitePlace.mk ψ
  have hemb : v.embedding = ψ := NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψr
  have hval : ((ι a : ℝ) : ℂ) = hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x) := by
    rw [← phi_hform, ← ha, X.B.I.φ_over v a, hemb]; rfl
  have hre : ι a = (hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x)).re := by rw [← hval]; simp
  rw [hre]
  by_contra hle
  push_neg at hle

  let nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := fun j =>
    if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u)
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hb := card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv (rv X.B.I v x) ?_ ?_ ?_ hle ?_
  · rw [card_eps_false X v] at hb
    omega
  · intro j k hjk
    simp only [nv]
    split_ifs with hj hk hk
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]
      have hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩ := fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))
      have hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩ := fun h => hne h.symm
      simp [hne, hne']
    · rw [hJ_sub_left]
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u _).1, (X.zu_orth u _).2]
      simp
    · rw [hJ_sub_right]
      have h1 := hJ_crd X v (X.zu u) (X.eX ⟨k.1, hk⟩)
      have h2 := hJ_crd X v (X.zu u) (X.fY ⟨k.1, hk⟩)
      have e1 : (VS D).hT (X.zu u) (X.eX ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u _).1]; simp
      have e2 : (VS D).hT (X.zu u) (X.fY ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u _).2]; simp
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]
    · exfalso; apply hjk; ext; omega
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]
      norm_num
    · simp only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]
      simp only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]
      exact_mod_cast (D.mem u).A.T_prime.pos
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, ← phi_hform, ← phi_hform, hxS _ (eR_mem_fix X u _), hxS _ (fR_mem_fix X u _)]
      simp
    · rw [← phi_hform, hxS _ (zR_mem_fix X u)]; simp
  · intro h0
    apply hx0
    have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
    have hφ : (fun i => X.B.I.φ v (x i)) = 0 := by
      have : X.B.I.P v *ᵥ rv X.B.I v x = fun i => X.B.I.φ v (x i) := by
        unfold rv; rw [mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]
      rw [← this, h0, mulVec_zero]
    funext i
    have := congrFun hφ i
    simpa using this

end SettingDef

end Formalism.L2.SG.PoincareInHH.Cut
