import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LevelDeterminantOfTriangularChange

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

/- English proof (translation)
Unfold `ell`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : a.val + 1 < r`. Rewrite using `[dif_pos h] first`. Consider the case `simp [fvec, h, bvec, Matrix.mulVec_single_one]`.

Consider the case `simp [fvec, h, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[dif_neg h]`. Simplify using `[fvec, h]`.
-/
theorem ell_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    ell k r z g = ∑ a : Fin r, (g *ᵥ fvec k r z ⟨a.val + 1, by omega⟩) (eI k r a) := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h]
    first
      | simp [fvec, h, bvec, Matrix.mulVec_single_one]
      | simp [fvec, h, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  · rw [dif_neg h]
    simp [fvec, h]

section Lv2
variable {k r' : ℕ}

/- English proof (translation)
Simplify using `only [Hpk, sh, Fin.ext_iff, Fin.val_mk]`. Establish `e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔ (p.val < r' ∧ p.val + q.val = 2 * r' + k)`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Establish `e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔ (q.val < r' ∧ p.val + q.val = 2 * r' + k)`. Apply the tactic sequence `constructor <;> intro h <;> omega`.

Establish `e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔ (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val)`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Establish `e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k)`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Simplify using `only [e1, e2, e3, e4]`.
-/
theorem hpk_sh (p q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (sh p) (sh q) = Hpk k r' p q := by
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  have e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (p.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (q.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

/- English proof (translation)
Use `p.isLt` as an intermediate fact. Use `q.isLt` as an intermediate fact. Simplify using `only [Hpk, sh, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem hpk_out (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by
  have := p.isLt
  have := q.isLt
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)))`. Introduce `a b h`. Simplify using `only [sh, Fin.mk.injEq] at h`. Conclude with `Fin.ext (by omega)`. Rewrite using `[show ∑ q : Fin (2 * r' + k + 1), F (sh q) = ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p from (Finset.sum_map Finset.univ ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]`.

Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `p _ hp`. Apply `hF` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`.

Apply `hp` to reduce the goal to its premises. Use `p.isLt` as an intermediate fact. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]`. Use `⟨⟨p.val - 1, by omega⟩, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma sum_eq_sum_sh_of_zero_at_edges (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hF : ∀ p : Fin (2 * (1 + r') + k + 1), (p.val = 0 ∨ p.val = 2 * (1 + r') + k) → F p = 0) :
    ∑ p, F p = ∑ q : Fin (2 * r' + k + 1), F (sh q) := by
  have hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [sh, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  rw [show ∑ q : Fin (2 * r' + k + 1), F (sh q) =
      ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p
      from (Finset.sum_map Finset.univ
        ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hF
  by_contra hc
  apply hp
  have := p.isLt
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
  ext
  simp only [sh, Fin.val_mk]
  omega

/- English proof (translation)
Establish `h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧ (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1`. Use `q.isLt` as an intermediate fact. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [liftVec]`.

Rewrite using `[dif_pos h1]`. Conclude with `congrArg v (Fin.ext (by simp [sh]))`.
-/
private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `(sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_` and prove the remaining obligations. Introduce `j hj`. Establish `h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1)` using `by omega`.

Simplify using `only [liftVec, dif_neg h0, mul_zero]`. Simplify using `only [liftVec_apply_sh]`. Distinguish the cases in `hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k`. Establish `h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `by omega`. Simplify using `only [hpk_out p hp, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]`.

Establish `hp' : p = sh ⟨p.val - 1, by have` using `p.isLt; omega⟩ := by`. Use `ext`. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hp']`.

Simplify using `only [hpk_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]`.
-/
theorem hpk_lv (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      simp only [hpk_out p hp, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [hpk_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

/- English proof (translation)
Unfold `herm`. Rewrite using `[hpk_lv]`. Simplify using `only [dotProduct, Pi.star_apply]`. Use `(sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_` and prove the remaining obligations. Introduce `p hp`.

Establish `h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `by omega`. Simplify using `only [liftVec, dif_neg h0, mul_zero]`. Simplify using `only [liftVec_apply_sh]`.
-/
theorem herm_lv (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_lv]
  simp only [dotProduct, Pi.star_apply]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro p hp
    have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]

/- English proof (translation)
Unfold `herm`. Rewrite using `[hpk_lv]`. Simplify using `[e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`.

Apply the tactic sequence `split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)`.
-/
theorem hermitianForm_liftVec_firstVector (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
  unfold herm
  rw [hpk_lv]
  simp [e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)

/- English proof (translation)
Simplify using `[e0, bvec, a0, eI]`.
-/
theorem firstVector_apply_first (h : 0 < 1 + r') : e0 k r' (eI k (1 + r') ⟨0, h⟩) = 1 := by
  simp [e0, bvec, a0, eI]

/- English proof (translation)
Simplify using `[e0, bvec, a0, eI, Pi.single_apply]`.
-/
theorem firstVector_apply_succ (b : ℕ) (h : b + 1 < 1 + r') : e0 k r' (eI k (1 + r') ⟨b + 1, h⟩) = 0 := by
  simp [e0, bvec, a0, eI, Pi.single_apply]

/- English proof (translation)
Use `ext`. Simplify using `[eI, sh]`.
-/
theorem eI_succ (b : ℕ) (h : b + 1 < 1 + r') : eI k (1 + r') ⟨b + 1, h⟩ = sh (eI k r' ⟨b, by omega⟩) := by
  ext
  simp [eI, sh]

/- English proof (translation)
Establish `hp : 1 ≤ (sh p : Fin (2 * (1 + r') + k + 1)).val ∧ (sh p : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1`. Use `p.isLt` as an intermediate fact. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Establish `hq : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧ (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1`.

Use `q.isLt` as an intermediate fact. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [ιLev]`. Rewrite using `[dif_pos hp, dif_pos hq]`.

Conclude with `congrArg₂ m (Fin.ext (by simp [sh])) (Fin.ext (by simp [sh]))`.
-/
private lemma lev_apply_sh_sh (m : Mat k r') (p q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' m (sh p) (sh q) = m p q := by
  have hp : 1 ≤ (sh p : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh p : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := p.isLt
    simp only [sh, Fin.val_mk]
    omega
  have hq : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [ιLev]
  rw [dif_pos hp, dif_pos hq]
  exact congrArg₂ m (Fin.ext (by simp [sh])) (Fin.ext (by simp [sh]))

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `(sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_` and prove the remaining obligations. Introduce `j hj`. Establish `h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1)` using `by omega`.

Simplify using `only [liftVec, dif_neg h0, mul_zero]`. Simplify using `only [liftVec_apply_sh]`. Distinguish the cases in `hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k`. Establish `h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `by omega`. Establish `hz : ∀ q : Fin (2 * r' + k + 1), ιLev k 1 r' m p (sh q) = 0`.

Introduce `q`. Establish `hne : p ≠ sh q`. Introduce `he`. Rewrite `hp` using `[he]`. Use `q.isLt` as an intermediate fact.

Simplify using `only [sh, Fin.val_mk] at hp`. Use linear arithmetic over natural numbers and integers. Simplify using `only [ιLev, dif_neg h0, if_neg hne]`. Simplify using `only [hz, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]`. Establish `hp' : p = sh ⟨p.val - 1, by have` using `p.isLt; omega⟩ := by`.

Use `ext`. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hp']`. Simplify using `only [lev_apply_sh_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]`.
-/
private lemma lev_mulVec_liftVec_eq_liftVec_mulVec (m : Mat k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' m *ᵥ liftVec k 1 r' w = liftVec k 1 r' (m *ᵥ w) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      have hz : ∀ q : Fin (2 * r' + k + 1), ιLev k 1 r' m p (sh q) = 0 := by
        intro q
        have hne : p ≠ sh q := by
          intro he
          rw [he] at hp
          have := q.isLt
          simp only [sh, Fin.val_mk] at hp
          omega
        simp only [ιLev, dif_neg h0, if_neg hne]
      simp only [hz, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [lev_apply_sh_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

/- English proof (translation)
Unfold `HeisAct at hHA`. Rewrite using `[← Matrix.mulVec_mulVec, lev_mulVec_liftVec_eq_liftVec_mulVec]`. Unfold `heis0`. Rewrite using `[hHA, herm_lv, hermitianForm_liftVec_firstVector, zero_smul, add_zero]`.
-/
theorem hcol (hHA : HeisAct) (m : Mat k r') (X : HPar k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    (heis0 k r' X * ιLev k 1 r' m) *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (m *ᵥ w) - herm (Hpk k r') (m *ᵥ w) X.1 • e0 k r' := by
  unfold HeisAct at hHA
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec_eq_liftVec_mulVec]
  unfold heis0
  rw [hHA, herm_lv, hermitianForm_liftVec_firstVector, zero_smul, add_zero]

/- English proof (translation)
Rewrite using `[← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1)) (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]`. Use `congrArg₂ (· + ·) ?_ ?_` and prove the remaining obligations. Conclude with `congrArg F (Fin.ext (by simp))`. Conclude with `Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))`.
-/
theorem sum_fin_one_add_eq_add_sum {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1))
    (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg F (Fin.ext (by simp))
  · exact Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))

/- English proof (translation)
Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k`. Establish `h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `by omega`. Establish `hne : p ≠ sh i`. Introduce `he`.

Rewrite `hp` using `[he]`. Use `i.isLt` as an intermediate fact. Simplify using `only [sh, Fin.val_mk] at hp`. Use linear arithmetic over natural numbers and integers. Simplify using `only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]`.

Establish `hp' : p = sh ⟨p.val - 1, by have` using `p.isLt; omega⟩ := by`. Use `ext`. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hp', liftVec_apply_sh]`.

Simplify using `[bvec, Pi.single_apply, sh, Fin.ext_iff]`.
-/
private lemma liftVec_bvec_eq_bvec_sh (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' (bvec i) = bvec (sh i) := by
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    have hne : p ≠ sh i := by
      intro he
      rw [he] at hp
      have := i.isLt
      simp only [sh, Fin.val_mk] at hp
      omega
    simp only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
    simp [bvec, Pi.single_apply, sh, Fin.ext_iff]

/- English proof (translation)
Distinguish the cases in `ha : a.val < r'`. Establish `h1 : a.val + 1 < 1 + r'` using `by omega`. Simplify using `only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]`. Rewrite using `[eI_succ a.val h1]`. Conclude with `(liftVec_bvec_eq_bvec_sh _).symm`.

Establish `h1 : ¬ a.val + 1 < 1 + r'` using `by omega`. Simplify using `only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]`.
-/
theorem fvec_lift (z1 : Fin (2 * r' + k + 1) → ℂ) (a : Fin (1 + r')) :
    fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩ = liftVec k 1 r' (fvec k r' z1 ⟨a.val, by omega⟩) := by
  by_cases ha : a.val < r'
  · have h1 : a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]
    rw [eI_succ a.val h1]
    exact (liftVec_bvec_eq_bvec_sh _).symm
  · have h1 : ¬ a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]

/- English proof (translation)
Simplify using `[liftVec, eI]`.
-/
private lemma liftVec_apply_eI_zero_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) (h : 0 < 1 + r') :
    liftVec k 1 r' v (eI k (1 + r') ⟨0, h⟩) = 0 := by
  simp [liftVec, eI]

/- English proof (translation)
Establish `key : ∀ a : Fin (1 + r'), ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩) (eI k (1 + r') a) = liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) - herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' …`. Introduce `a`. Rewrite using `[fvec_lift, hcol hHA]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[ell_col, ell_col, sum_fin_one_add_eq_add_sum]`.

Use `congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]`. Use `beta_reduce`. Rewrite using `[key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]`.
-/
theorem ell_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by
  have key : ∀ a : Fin (1 + r'),
      ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩)
        (eI k (1 + r') a) =
      liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) -
        herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' (eI k (1 + r') a) := by
    intro a
    rw [fvec_lift, hcol hHA]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ell_col, ell_col, sum_fin_one_add_eq_add_sum]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)
  · beta_reduce
    rw [key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]
  · beta_reduce
    rw [key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]

/- English proof (translation)
Simplify using `only [lam, cStd]`. Rewrite using `[ell_lev hHA]`. Simplify using `only [mul_add, mul_neg, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]`. Evaluate the numerical expressions.
-/
theorem lam_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -2 * (herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1).im + lam k r' z1 m := by
  simp only [lam, cStd]
  rw [ell_lev hHA]
  simp only [mul_add, mul_neg, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  norm_num

/- English proof (translation)
Unfold `inWb at hz`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k`. Establish `h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `by omega`. Rewrite using `[hz p (by omega)]`.

Simplify using `only [liftVec, dif_neg h0]`. Establish `hp' : p = sh ⟨p.val - 1, by have` using `p.isLt; omega⟩ := by`. Use `ext`. Simplify using `only [sh, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hp', liftVec_apply_sh]`.
-/
theorem z_lift (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) :
    z = liftVec k 1 r' (fun q => z (sh q)) := by
  unfold inWb at hz
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    rw [hz p (by omega)]
    simp only [liftVec, dif_neg h0]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]

/- English proof (translation)
Unfold `inWb at hz ⊢`. Introduce `i hi`. Use `i.isLt` as an intermediate fact. Conclude with `hz (sh i) (by simp only [sh, Fin.val_mk]; omega)`.
-/
theorem shifted_mem_weightSpace (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) : inWb k r' (fun q => z (sh q)) := by
  unfold inWb at hz ⊢
  intro i hi
  have := i.isLt
  exact hz (sh i) (by simp only [sh, Fin.val_mk]; omega)

/- English proof (translation)
Unfold `Tz`. Rewrite using `[herm_lv]`.
-/
theorem tz_lift (z1 : Fin (2 * r' + k + 1) → ℂ) : Tz k (1 + r') (liftVec k 1 r' z1) = Tz k r' z1 := by
  unfold Tz
  rw [herm_lv]

end Lv2

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
