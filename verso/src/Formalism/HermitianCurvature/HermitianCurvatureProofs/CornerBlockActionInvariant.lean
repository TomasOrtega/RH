import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearFormRadicalRankOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

/- English proof (translation)
Break down `x with (a | b) | c` into its components or cases. Establish `ha` using `a.isLt`. Simplify using `only [liftVec, Sum.elim_inl]`. Rewrite using `[dif_neg]`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.

Use linear arithmetic over natural numbers and integers. Establish `hb` using `b.isLt`. Simplify using `only [liftVec, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[dif_pos]`. Use `congr 1`.

Use `ext`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,`. Use the proof step `finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.

Use linear arithmetic over natural numbers and integers. Establish `hc` using `c.isLt`. Simplify using `only [liftVec, Sum.elim_inr]`. Rewrite using `[dif_neg]`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem liftVec_eB (u : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    liftVec k p ρ u (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) u) (fun _ => 0) x := by
  rcases x with (a | b) | c
  · have ha := a.isLt
    simp only [liftVec, Sum.elim_inl]
    rw [dif_neg]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega
  · have hb := b.isLt
    simp only [liftVec, Sum.elim_inl, Sum.elim_inr]
    rw [dif_pos]
    · congr 1
      ext
      simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
    · simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
  · have hc := c.isLt
    simp only [liftVec, Sum.elim_inr]
    rw [dif_neg]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega

/- English proof (translation)
Introduce `i hi`. Simplify using `only [liftVec]`. Use `split_ifs with h`. Conclude with `hz _ (by show i.val - p < ρ ∨ ρ + k < i.val - p; omega)`. Both sides reduce to the same expression.
-/
theorem inWb_liftVec {z : Fin (2 * ρ + k + 1) → ℂ} (hz : inWb k ρ z) : inWb k (p + ρ) (liftVec k p ρ z) := by
  intro i hi
  simp only [liftVec]
  split_ifs with h
  · exact hz _ (by show i.val - p < ρ ∨ ρ + k < i.val - p; omega)
  · rfl

/- English proof (translation)
Use `ext`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.
-/
theorem eI_X (a : Fin p) : eI k (p + ρ) (Fin.castAdd ρ a) = U.eB k p ρ (Sum.inl (Sum.inl a)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

/- English proof (translation)
Use `ext`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.
-/
theorem eI_V (a : Fin ρ) : eI k (p + ρ) (Fin.natAdd p a) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ a))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

/- English proof (translation)
Use `ext`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.
-/
theorem eI_V' (a : ℕ) (ha : a < ρ) (h : p + a < p + ρ) :
    eI k (p + ρ) ⟨p + a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨a, ha⟩))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

/- English proof (translation)
Use `ext`. Simplify using `only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]`.
-/
theorem eI_X' (a : ℕ) (ha : a < p) (h : a < p + ρ) :
    eI k (p + ρ) ⟨a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inl ⟨a, ha⟩)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

local macro "blks" : tactic => `(tactic| simp only [Ux3.block3_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
  Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
  Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr])

/- English proof (translation)
Apply the tactic sequence `rcases x with (a' | b') | c' <;> simp [U.embG, Ux6.block3_apply, Matrix.one_apply] <;> (try split_ifs) <;> simp_all`.
-/
private theorem embG_eB_inl_inl_apply_eq_ite (y : B.Mat k ρ) (a : Fin p) (x : U.Ix k p ρ) :
    U.embG k p ρ y (U.eB k p ρ (Sum.inl (Sum.inl a))) (U.eB k p ρ x) = if x = Sum.inl (Sum.inl a) then 1 else 0 := by
  rcases x with (a' | b') | c' <;> simp [U.embG, Ux6.block3_apply, Matrix.one_apply] <;> (try split_ifs) <;> simp_all

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Equiv.sum_comp (U.eB k p ρ)]`. Simplify using `only [U.embG, Ux6.block3_apply, liftVec_eB]`. Apply the tactic sequence `rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.one_apply]`.
-/
private theorem embG_mulVec_liftVec_eB_apply (y : B.Mat k ρ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.embG k p ρ y *ᵥ liftVec k p ρ z) (U.eB k p ρ x) =
      Sum.elim (Sum.elim (fun _ => 0) (y *ᵥ z)) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.embG, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [Formalism.QuantumDeterminants.ell]`. Rewrite using `[Fin.sum_univ_add, Finset.sum_eq_zero, zero_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Establish `hb` using `b.isLt`.

Establish `hV : eI k (p + ρ) (Fin.natAdd p b) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ b)))` using `eI_V b`. Distinguish the cases in `h : b.val + 1 < ρ`. Establish `h' : (Fin.natAdd p b).val + 1 < p + ρ` using `by simp; omega`. Establish `hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩)))` using `eI_V' (b.val + 1) h (by simp; omega)`. Rewrite using `[dif_pos h', dif_pos h, hV, hV']`.

Simplify using `[U.embG, Ux6.block3_apply]`. Establish `h' : ¬ (Fin.natAdd p b).val + 1 < p + ρ` using `by simp; omega`. Rewrite using `[dif_neg h', dif_neg h, hV, embG_mulVec_liftVec_eB_apply]`. Both sides reduce to the same expression. Introduce `a _`.

Establish `ha` using `a.isLt`. Rewrite using `[eI_X a]`. Use `split_ifs with h`. Take `⟨x, hx⟩` from `(U.eB k p ρ).surjective (eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h⟩)`. Rewrite using `[← hx, embG_eB_inl_inl_apply_eq_ite, if_neg]`.

Introduce and unpack `rfl`. Use `congrArg Fin.val hx` as an intermediate fact. Simplify using `[U.eB, eI] at this`. Rewrite using `[embG_mulVec_liftVec_eB_apply]`. Both sides reduce to the same expression.
-/
theorem ell_embG (z : Fin (2 * ρ + k + 1) → ℂ) (y : B.Mat k ρ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.embG k p ρ y) = ell k ρ z y := by
  simp only [Formalism.QuantumDeterminants.ell]
  rw [Fin.sum_univ_add, Finset.sum_eq_zero, zero_add]
  · apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    have hV : eI k (p + ρ) (Fin.natAdd p b) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ b))) := eI_V b
    by_cases h : b.val + 1 < ρ
    · have h' : (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      rw [dif_pos h', dif_pos h, hV, hV']
      simp [U.embG, Ux6.block3_apply]
    · have h' : ¬ (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      rw [dif_neg h', dif_neg h, hV, embG_mulVec_liftVec_eB_apply]
      rfl
  · intro a _
    have ha := a.isLt
    rw [eI_X a]
    split_ifs with h
    · obtain ⟨x, hx⟩ := (U.eB k p ρ).surjective (eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h⟩)
      rw [← hx, embG_eB_inl_inl_apply_eq_ite, if_neg]
      rintro rfl
      have := congrArg Fin.val hx
      simp [U.eB, eI] at this
    · rw [embG_mulVec_liftVec_eB_apply]
      rfl

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Equiv.sum_comp (U.eB k p ρ)]`. Simplify using `only [U.muP, Ux6.block3_apply, liftVec_eB]`. Apply the tactic sequence `rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.one_apply]`.
-/
private theorem muP_mulVec_liftVec_eB_apply (q : Matrix (Fin p) (Fin p) ℂ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.muP k p ρ q *ᵥ liftVec k p ρ z) (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) z) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.muP, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [Formalism.QuantumDeterminants.ell, U.supS]`. Rewrite using `[Fin.sum_univ_add]`. Use `(congrArg₂ HAdd.hAdd ?_ (Finset.sum_eq_zero fun b _ => ?_)).trans (add_zero _)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Establish `ha` using `a.isLt`. Rewrite using `[eI_X a]`. Distinguish the cases in `h : a.val + 1 < p`. Establish `h' : (Fin.castAdd ρ a).val + 1 < p + ρ` using `by simp; omega`. Establish `hX' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ = U.eB k p ρ (Sum.inl (Sum.inl ⟨a.val + 1, h⟩))` using `eI_X' (a.val + 1) h h'`.

Rewrite using `[dif_pos h', dif_pos h, hX']`. Simplify using `[U.muP, Ux6.block3_apply]`. Rewrite using `[dif_neg h] split_ifs with h'`. Establish `hρ : 0 < ρ` using `by simp at h'; omega`. Establish `hV' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨0, hρ⟩)))`.

Use `ext`. Apply the tactic sequence `simp [U.eB, eI] <;> omega`. Rewrite using `[hV']`. Simplify using `[U.muP, Ux6.block3_apply]`. Rewrite using `[muP_mulVec_liftVec_eB_apply]`.

Both sides reduce to the same expression. Establish `hb` using `b.isLt`. Rewrite using `[eI_V b]`. Use `split_ifs with h'`. Establish `h : b.val + 1 < ρ` using `by simp at h'; omega`.

Establish `hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩)))` using `eI_V' (b.val + 1) h (by simp; omega)`. Establish `hne : eI k ρ b ≠ eI k ρ ⟨b.val + 1, h⟩`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[eI] at this`.

Rewrite using `[hV']`. Simplify using `[U.muP, Ux6.block3_apply, Matrix.one_apply, hne]`. Rewrite using `[muP_mulVec_liftVec_eB_apply]`. Conclude with `hz _ (Or.inl (by simp [eI]))`.
-/
theorem ell_muP (z : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (q : Matrix (Fin p) (Fin p) ℂ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.muP k p ρ q) = U.supS q := by
  simp only [Formalism.QuantumDeterminants.ell, U.supS]
  rw [Fin.sum_univ_add]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_eq_zero fun b _ => ?_)).trans (add_zero _)
  · apply Finset.sum_congr rfl
    intro a _
    have ha := a.isLt
    rw [eI_X a]
    by_cases h : a.val + 1 < p
    · have h' : (Fin.castAdd ρ a).val + 1 < p + ρ := by simp; omega
      have hX' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inl ⟨a.val + 1, h⟩)) := eI_X' (a.val + 1) h h'
      rw [dif_pos h', dif_pos h, hX']
      simp [U.muP, Ux6.block3_apply]
    · rw [dif_neg h]
      split_ifs with h'
      · have hρ : 0 < ρ := by simp at h'; omega
        have hV' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
            U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨0, hρ⟩))) := by
          ext
          simp [U.eB, eI] <;> omega
        rw [hV']
        simp [U.muP, Ux6.block3_apply]
      · rw [muP_mulVec_liftVec_eB_apply]
        rfl
  · have hb := b.isLt
    rw [eI_V b]
    split_ifs with h'
    · have h : b.val + 1 < ρ := by simp at h'; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      have hne : eI k ρ b ≠ eI k ρ ⟨b.val + 1, h⟩ := by
        intro e
        have := congrArg Fin.val e
        simp [eI] at this
      rw [hV']
      simp [U.muP, Ux6.block3_apply, Matrix.one_apply, hne]
    · rw [muP_mulVec_liftVec_eB_apply]
      exact hz _ (Or.inl (by simp [eI]))

/- English proof (translation)
Simplify using `only [Formalism.QuantumDeterminants.psi, h]`.
-/
theorem psi_of_ell {r r' : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r)
    (g' : B.Mat k r') (h : ell k r z g = ell k r' z' g') : psi k r z cStd g = psi k r' z' cStd g' := by
  simp only [Formalism.QuantumDeterminants.psi, h]

/- English proof (translation)
Introduce `k p ρ z' u hz`. Simplify using `only [Formalism.QuantumDeterminants.psi, G.psi, U.betaU, ell_muP z' hz]`. Use `show (starRingEnd ℂ) (Complex.exp _) = _`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`.

Simplify using `[neg_mul, Complex.ofReal_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_measure_preserving : PsiMuP := by
  intro k p ρ z' u hz
  simp only [Formalism.QuantumDeterminants.psi, G.psi, U.betaU, ell_muP z' hz]
  show (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [neg_mul, Complex.ofReal_neg]
  ring

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : i ≠ j` using `ne_of_gt hij`. Establish `h2 : ¬ i < j` using `not_lt.mpr (le_of_lt hij)`. Simplify using `[G.upper, G.strictUpper, Matrix.one_apply, h1, h2]`. Simplify using `[G.upper, G.strictUpper]`.
-/
theorem upper_isUpUni (u : G.UT p → ℂ) : Formalism.DoubleCosetMeasures.IsUpUni (G.upper u) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
    simp [G.upper, G.strictUpper, Matrix.one_apply, h1, h2]
  · simp [G.upper, G.strictUpper]

/- English proof (translation)
The claim follows from `(Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨x, rfl⟩)`.
-/
theorem rn_nset (x : U.RC k p ρ) : U.Rn k p ρ x ∈ QuantumDeterminants.Nset k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨x, rfl⟩)

/- English proof (translation)
Introduce `k p ρ z' ν' u x hz hν`. Establish `hz0` using `inWb_liftVec (p := p) hz`. Establish `hcl` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)`. Establish `h1` using `embG_nset (p := p) hν`. Establish `h2` using `Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset (k := k) (ρ := ρ) _ (upper_isUpUni u)`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ (hcl.mul_mem _ h1 _ h2) (rn_nset x), Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ h1 h2, psi_of_ell _ z' _ ν' (ell_embG z' ν')]`.
-/
theorem psi_right_equivariant : PsiRight := by
  intro k p ρ z' ν' u x hz hν
  have hz0 := inWb_liftVec (p := p) hz
  have hcl := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)
  have h1 := embG_nset (p := p) hν
  have h2 := Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset (k := k) (ρ := ρ) _ (upper_isUpUni u)
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ (hcl.mul_mem _ h1 _ h2) (rn_nset x),
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ h1 h2, psi_of_ell _ z' _ ν' (ell_embG z' ν')]

/- English proof (translation)
Establish `h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1` using `rfl`. Establish `hv' : yᴴ *ᵥ (Hpk k ρ *ᵥ v) = Hpk k ρ *ᵥ v`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (G.wMat p * (Matrix.of x.1)ᴴ * yᴴ * Hpk k ρ) *ᵥ v = (G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ v`. Simplify using `only [← Matrix.mulVec_mulVec, hv']`.

Rewrite using `[h1, Matrix.conjTranspose_mul, Matrix.neg_mulVec, Matrix.neg_mulVec, ← Matrix.mul_assoc, h2]`.
-/
theorem corner_block_action_invariant (y : B.Mat k ρ) (x : U.RC k p ρ) (v : Fin (2 * ρ + k + 1) → ℂ) (hy : yᴴ * Hpk k ρ * y = Hpk k ρ)
    (hv : y *ᵥ v = v) :
    (-(G.wMat p * (Matrix.of (rcAct y x).1)ᴴ * Hpk k ρ)) *ᵥ v = (-(G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ)) *ᵥ v := by
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have hv' : yᴴ *ᵥ (Hpk k ρ *ᵥ v) = Hpk k ρ *ᵥ v := by
    calc yᴴ *ᵥ (Hpk k ρ *ᵥ v) = yᴴ *ᵥ (Hpk k ρ *ᵥ (y *ᵥ v)) := by rw [hv]
      _ = (yᴴ * Hpk k ρ * y) *ᵥ v := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Hpk k ρ *ᵥ v := by rw [hy]
  have h2 : (G.wMat p * (Matrix.of x.1)ᴴ * yᴴ * Hpk k ρ) *ᵥ v = (G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ v := by
    simp only [← Matrix.mulVec_mulVec, hv']
  rw [h1, Matrix.conjTranspose_mul, Matrix.neg_mulVec, Matrix.neg_mulVec, ← Matrix.mul_assoc, h2]

/- English proof (translation)
Introduce `k p ρ z' h' x hz hh`. Establish `hz0` using `inWb_liftVec (p := p) hz`. Apply `psi_of_ell` to reduce the goal to its premises. Rewrite using `[Ux3.rn_eq, Ux3.rn_eq, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0]`. Distinguish the cases in `hp : 0 < p`.

Rewrite using `[dif_pos hp, dif_pos hp]`. Distinguish the cases in `hρ : 0 < ρ`. Rewrite using `[dif_pos hρ, dif_pos hρ]`. Establish `e` using `congrFun (corner_block_action_invariant h' x (bvec (eI k ρ ⟨0, hρ⟩)) hh.1 (hh.2.1 ⟨0, hρ⟩).1) ⟨p - 1, by omega⟩`. Establish `e2 : ∀ M : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ, M ⟨p - 1, by omega⟩ ⟨0, by omega⟩ = (M *ᵥ bvec (eI k ρ ⟨0, hρ⟩)) ⟨p - 1, by omega⟩`.

Introduce `M`. Simplify using `only [bvec, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Conclude with `(e2 _).trans (e.trans (e2 _).symm)`. Rewrite using `[dif_neg hρ, dif_neg hρ]`.

Establish `hlow : U.lowV k p ρ (liftVec k p ρ z') = z'`. Use function extensionality and compare the values at `q; simp only [U.lowV, liftVec]; rw [dif_pos (by omega)]; congr 1; ext; simp`. Rewrite using `[hlow]`. Conclude with `congrFun (corner_block_action_invariant h' x z' hh.1 hh.2.2) _`. Rewrite using `[dif_neg hp, dif_neg hp]`.
-/
theorem psi_right_action_comm : PsiRnAct := by
  intro k p ρ z' h' x hz hh
  have hz0 := inWb_liftVec (p := p) hz
  apply psi_of_ell
  rw [Ux3.rn_eq, Ux3.rn_eq, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0]
  by_cases hp : 0 < p
  · rw [dif_pos hp, dif_pos hp]
    by_cases hρ : 0 < ρ
    · rw [dif_pos hρ, dif_pos hρ]
      have e := congrFun (corner_block_action_invariant h' x (bvec (eI k ρ ⟨0, hρ⟩)) hh.1 (hh.2.1 ⟨0, hρ⟩).1) ⟨p - 1, by omega⟩
      have e2 : ∀ M : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ,
          M ⟨p - 1, by omega⟩ ⟨0, by omega⟩ = (M *ᵥ bvec (eI k ρ ⟨0, hρ⟩)) ⟨p - 1, by omega⟩ := by
        intro M; simp only [bvec, Matrix.mulVec_single_one]; rfl
      exact (e2 _).trans (e.trans (e2 _).symm)
    · rw [dif_neg hρ, dif_neg hρ]
      have hlow : U.lowV k p ρ (liftVec k p ρ z') = z' := by
        funext q; simp only [U.lowV, liftVec]; rw [dif_pos (by omega)]; congr 1; ext; simp
      rw [hlow]
      exact congrFun (corner_block_action_invariant h' x z' hh.1 hh.2.2) _
  · rw [dif_neg hp, dif_neg hp]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
