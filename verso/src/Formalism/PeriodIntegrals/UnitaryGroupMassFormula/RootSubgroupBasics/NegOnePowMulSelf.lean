import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.SuperdiagPairingAdjacent

open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

/- English proof (translation)
Establish `h` using `pv_spec p.1 p.2.1 i.val (by rw [p.2.2]; exact i.isLt)`. Rewrite `h` using `[p.2.2]`. Conclude with `h`.
-/
theorem pt_spec (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    pv p.1 i.val < r + 1 ∧ pv p.1 (pv p.1 i.val) = i.val ∧ ptEntry p.1 i.val (pv p.1 i.val) ≠ 0 := by
  have h := pv_spec p.1 p.2.1 i.val (by rw [p.2.2]; exact i.isLt)
  rw [p.2.2] at h
  exact h

def ptσ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : Fin (r + 1) := ⟨pv p.1 i.val, (pt_spec p i).1⟩

def ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ℂ :=
  (-1 : ℂ) ^ (r - (ptσ p i).val) * ptMat p i (ptσ p i)

/- English proof (translation)
The claim follows from `Fin.ext (pt_spec p i).2.1`.
-/
theorem ptσ_invol (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptσ p (ptσ p i) = i := Fin.ext (pt_spec p i).2.1

/- English proof (translation)
Unfold `ptζ`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) (pt_spec p i).2.2`.
-/
theorem ptζ_ne (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptζ p i ≠ 0 := by
  unfold ptζ
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pt_spec p i).2.2

/- English proof (translation)
Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  rw [← mul_pow]
  norm_num

/- English proof (translation)
Establish `hZ : Zhat k r z z' g i j = (-1 : ℂ) ^ (r - j.val) * ptMat p i j`. Establish `h` using `congrFun (congrFun hP i) j`. Simplify using `only [ZhatO] at h`. Rewrite using `[← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]`. Rewrite using `[hZ]`.

Use `split_ifs with hj`. Substitute `hj` using the available equality. Both sides reduce to the same expression. Apply the tactic sequence `have : ptEntry p.1 i.val j.val = 0 := by`. Assume the negation of the conclusion as `hne`.

Conclude with `hj (Fin.ext (ptEntry_ne_zero_imp p.1 i.val j.val hne))`. Apply the tactic sequence `show (-1 : ℂ) ^ (r - j.val) * ptEntry p.1 i.val j.val = 0`. Rewrite using `[this, mul_zero]`.
-/
theorem zhat_pt {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (i j : Fin (r + 1)) :
    Zhat k r z z' g i j = if j = ptσ p i then ptζ p i else 0 := by
  have hZ : Zhat k r z z' g i j = (-1 : ℂ) ^ (r - j.val) * ptMat p i j := by
    have h := congrFun (congrFun hP i) j
    simp only [ZhatO] at h
    rw [← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [hZ]
  split_ifs with hj
  · subst hj
    rfl
  · have : ptEntry p.1 i.val j.val = 0 := by
      by_contra hne
      exact hj (Fin.ext (ptEntry_ne_zero_imp p.1 i.val j.val hne))
    show (-1 : ℂ) ^ (r - j.val) * ptEntry p.1 i.val j.val = 0
    rw [this, mul_zero]

/- English proof (translation)
Establish `hs` using `p.2.2`. Establish `hi1lt` using `i1.isLt`. Break down `pv_adj p.1 p.2.1 i.val (by rw [hs]; omega) with ⟨h1, h2⟩ | h1` into its components or cases. Use `left`. Establish `hv : pv p.1 i1.val = pv p.1 (i.val + 1)` using `by rw [hi1]`.

Use `⟨by show pv p.1 i1.val + 1 = pv p.1 i.val; rw [hv]; exact h1, ?_⟩` and prove the remaining obligations. Unfold `ptζ`. Rewrite using `[ptσ_invol p i1, ptσ_invol p i]`. Apply the tactic sequence `show (-1 : ℂ) ^ (r - i1.val) * ptEntry p.1 (pv p.1 i1.val) i1.val = -((-1 : ℂ) ^ (r - i.val) * ptEntry p.1 (pv p.1 i.val) i.val)`. Rewrite using `[hv, hi1, h2]`.

Establish `hr : r - i.val = (r - (i.val + 1)) + 1` using `by omega`. Rewrite using `[hr, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `right show pv p.1 i.val < pv p.1 i1.val`. Rewrite using `[hi1]`.

Conclude with `h1`.
-/
theorem pt_adj (p : Point ℂ (r + 1)) (i i1 : Fin (r + 1)) (hi1 : i1.val = i.val + 1) :
    ((ptσ p i1).val + 1 = (ptσ p i).val ∧ ptζ p (ptσ p i1) = - ptζ p (ptσ p i)) ∨
      (ptσ p i).val < (ptσ p i1).val := by
  have hs := p.2.2
  have hi1lt := i1.isLt
  rcases pv_adj p.1 p.2.1 i.val (by rw [hs]; omega) with ⟨h1, h2⟩ | h1
  · left
    have hv : pv p.1 i1.val = pv p.1 (i.val + 1) := by rw [hi1]
    refine ⟨by show pv p.1 i1.val + 1 = pv p.1 i.val; rw [hv]; exact h1, ?_⟩
    unfold ptζ
    rw [ptσ_invol p i1, ptσ_invol p i]
    show (-1 : ℂ) ^ (r - i1.val) * ptEntry p.1 (pv p.1 i1.val) i1.val =
      -((-1 : ℂ) ^ (r - i.val) * ptEntry p.1 (pv p.1 i.val) i.val)
    rw [hv, hi1, h2]
    have hr : r - i.val = (r - (i.val + 1)) + 1 := by omega
    rw [hr, pow_succ]
    ring
  · right
    show pv p.1 i.val < pv p.1 i1.val
    rw [hi1]
    exact h1

/- English proof (translation)
Establish `hgi : g⁻¹ * g = 1` using `uh_inv_mul hg`. Establish `hxe : g⁻¹ * (g * x * g⁻¹) * g = x`. Combine the equalities or inequalities in the displayed calculation. Establish `ha : g * x * g⁻¹ ∈ RStab k r g` using `⟨hx.2, by rw [hxe]; exact hx.1⟩`. Establish `h` using `flag_rel hz hz' hg ha`.

Rewrite `h` using `[hxe]`. Conclude with `h`.
-/
theorem flag_rel_Rset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (hx : x ∈ Formalism.MainNotions.S.Rset k r g) :
    (flagMat k r z (g * x * g⁻¹))ᴴ * Zhat k r z z' g * flagMat k r z' x = Zhat k r z z' g := by
  have hgi : g⁻¹ * g = 1 := uh_inv_mul hg
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by
    calc g⁻¹ * (g * x * g⁻¹) * g = (g⁻¹ * g) * x * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
  have ha : g * x * g⁻¹ ∈ RStab k r g := ⟨hx.2, by rw [hxe]; exact hx.1⟩
  have h := flag_rel hz hz' hg ha
  rw [hxe] at h
  exact h

section AtPt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {p : Point ℂ (r + 1)}

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular hu, Finset.prod_eq_one fun i _ => hd i]`. Conclude with `isUnit_one`.
-/
private theorem isUnit_det_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : IsUnit u.det := by
  rw [Matrix.det_of_upperTriangular hu, Finset.prod_eq_one fun i _ => hd i]
  exact isUnit_one

/- English proof (translation)
Establish `hU` using `isUnit_det_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)`. Establish `hrel` using `flag_rel hz hz' hg ha`. Establish `hkey : Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) = ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hU, Matrix.conjTranspose_one, Matrix.one_mul]`.

Use `_ = ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by rw [hrel]`. Establish `hσ : ∀ l, (j = ptσ p l) ↔ (l = ptσ p j)`. Introduce `l`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Conclude with `(ptσ_invol p l).symm`. Introduce and unpack `rfl`. Conclude with `(ptσ_invol p j).symm`. Establish `h` using `congrFun (congrFun hkey i) j`. Simplify using `only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h`.

Conclude with `h`.
-/
theorem flag_entry (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1)) :
    ptζ p i * flagMat k r z' (g⁻¹ * a * g) (ptσ p i) j =
      star ((flagMat k r z a)⁻¹ (ptσ p j) i) * ptζ p (ptσ p j) := by
  have hU := isUnit_det_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
  have hrel := flag_rel hz hz' hg ha
  have hkey : Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) =
      ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by
    calc Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)
        = ((flagMat k r z a)⁻¹)ᴴ *
            ((flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
            Matrix.mul_nonsing_inv _ hU, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by rw [hrel]
  have hσ : ∀ l, (j = ptσ p l) ↔ (l = ptσ p j) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p j).symm
  have h := congrFun (congrFun hkey i) j
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h
  exact h

/- English proof (translation)
Establish `hU` using `isUnit_det_of_unitriangular u hu hd`. Use `letI : Invertible u := ⟨u⁻¹, Matrix.nonsing_inv_mul u hU, Matrix.mul_nonsing_inv u hU⟩`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hu`.
-/
private theorem blockTriangular_inv_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : u⁻¹.BlockTriangular id := by
  have hU := isUnit_det_of_unitriangular u hu hd
  letI : Invertible u := ⟨u⁻¹, Matrix.nonsing_inv_mul u hU, Matrix.mul_nonsing_inv u hU⟩
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

/- English proof (translation)
Establish `hx : g⁻¹ * a * g ∈ Nset k r` using `ha.2`. Establish `hU` using `isUnit_det_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)`. Establish `hrel` using `flag_rel hz hz' hg ha`. Establish `hkey : (flagMat k r z a)ᴴ * Zhat k r z z' g = Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc _ (flagMat k r z' (g⁻¹ * a * g)), Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]`. Use `_ = Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by rw [hrel]`. Establish `hσ : ∀ l, (n = ptσ p l) ↔ (l = ptσ p n)`. Introduce `l`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Conclude with `(ptσ_invol p l).symm`. Introduce and unpack `rfl`. Conclude with `(ptσ_invol p n).symm`. Establish `h` using `congrFun (congrFun hkey m) n`.

Simplify using `only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h`. Conclude with `h`.
-/
private theorem star_flagMat_mul_ptZeta_eq (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (m n : Fin (r + 1)) :
    star (flagMat k r z a (ptσ p n) m) * ptζ p (ptσ p n) =
      ptζ p m * (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p m) n := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have hU := isUnit_det_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
  have hrel := flag_rel hz hz' hg ha
  have hkey : (flagMat k r z a)ᴴ * Zhat k r z z' g =
      Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
    calc (flagMat k r z a)ᴴ * Zhat k r z z' g
        = (flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) *
            (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
          rw [Matrix.mul_assoc _ (flagMat k r z' (g⁻¹ * a * g)), Matrix.mul_nonsing_inv _ hU,
            Matrix.mul_one]
      _ = Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by rw [hrel]
  have hσ : ∀ l, (n = ptσ p l) ↔ (l = ptσ p n) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p n).symm
  have h := congrFun (congrFun hkey m) n
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h
  exact h

/- English proof (translation)
Establish `hlt' : ptσ p i < ptσ p j` using `hlt`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have h := flag_entry hz hz' hg hP ha (ptσ p i) j`. Rewrite `h` using `[ptσ_invol]`. Establish `hv` using `blockTriangular_inv_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)`.

Establish `h0 : (flagMat k r z a)⁻¹ (ptσ p j) (ptσ p i) = 0` using `hv hlt'`. Rewrite `h` using `[h0, star_zero, zero_mul]`. Conclude with `(mul_eq_zero.mp h).resolve_left (ptζ_ne p _)`. Establish `h` using `star_flagMat_mul_ptZeta_eq hz hz' hg hP ha j (ptσ p i)`. Rewrite `h` using `[ptσ_invol]`.

Establish `hx : g⁻¹ * a * g ∈ Nset k r` using `ha.2`. Establish `hv` using `blockTriangular_inv_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)`. Establish `h0 : (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p j) (ptσ p i) = 0` using `hv hlt'`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `star_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ptζ_ne p i))`.
-/
theorem flag_offblock (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1))
    (hlt : (ptσ p i).val < (ptσ p j).val) :
    flagMat k r z' (g⁻¹ * a * g) i j = 0 ∧ flagMat k r z a i j = 0 := by
  have hlt' : ptσ p i < ptσ p j := hlt
  refine ⟨?_, ?_⟩
  · have h := flag_entry hz hz' hg hP ha (ptσ p i) j
    rw [ptσ_invol] at h
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
    have h0 : (flagMat k r z a)⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (ptζ_ne p _)
  · have h := star_flagMat_mul_ptZeta_eq hz hz' hg hP ha j (ptσ p i)
    rw [ptσ_invol] at h
    have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
    have h0 : (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, mul_zero] at h
    exact star_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ptζ_ne p i))

end AtPt

end PI.AmpRootCommon
