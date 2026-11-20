import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke GlobalTheory.ParHeckeSource GlobalTheory.ParahoricConjBlocks

noncomputable section

namespace GlobalTheory.LowerHecke

/- English proof (translation)
Simplify using `only [fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel`.
-/
theorem lowU_conj_blocks {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (M W : Matrix D D k) (ν : Matrix D A k) (a : Matrix A A k) (b : Matrix A D k) (c : Matrix D A k) (e : Matrix D D k) :
    fromBlocks 1 0 0 M * fromBlocks 1 0 (-ν) 1 * fromBlocks a b c e * fromBlocks 1 0 0 W =
      fromBlocks a (b * W) (M * (c - ν * a)) (M * (e - ν * b) * W) := by
  simp only [fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel

end GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj`. Use `set w := torusElt k D ϖ (indic s) with hw`. Establish `hjI : IsIntM j.1` using `isIntM_of_mem_parahoric hj`. Establish `hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1` using `(mem_parahoric.1 hj).2`. Establish `hjd : valuation k j.1.det = 1` using `val_det_of_mem_KO (mem_parahoric.1 hj).1`.

Take `⟨ha, he⟩` from `(val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd`. Take `⟨haI, hbI, hcI, heI⟩` from `isIntM_toBlocks hjI`. Use `set a := j.1.toBlocks₁₁ with ha_def`. Use `set b := j.1.toBlocks₁₂ with hb_def`. Use `set c := j.1.toBlocks₂₁ with hc_def`.

Use `set e := j.1.toBlocks₂₂ with he_def`. Establish `hcM : ∀ i l, valuation k (c i l) < 1` using `fun i l => hjl i l`. Establish `ha0 : IsUnit a.det`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Rewrite `ha` using `[h0, map_zero]`.

Conclude with `zero_ne_one ha`. Establish `hainvI : IsIntM a⁻¹` using `isIntM_inv haI ha`. Establish `hinva : a⁻¹ * a = 1` using `Matrix.nonsing_inv_mul a ha0`. Use `letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0`. Use `set E := e - c * a⁻¹ * b with hE_def`.

Establish `hjE : j.1.det = a.det * E.det`. Rewrite using `[← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]`. Establish `hEd : valuation k E.det = 1`. Rewrite `hjd` using `[hjE, map_mul, ha, one_mul]`. Conclude with `hjd`.

Establish `hEI : IsIntM E` using `isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)`. Establish `hEu : IsUnit E` using `(Matrix.isUnit_iff_isUnit_det E).2 (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)`. Use `set E' : GL D k := hEu.unit with hE'_def`. Establish `hE'v : E'.1 = E` using `hEu.unit_spec`. Establish `hE'K : E' ∈ KO k D` using `mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)`.

Take `⟨g, ⟨hgR, hgK⟩, -⟩` from `hR.2 E' hE'K`. Take `⟨hκg, hκ'g, hgeq⟩` from `hκ g hgR`. Use `⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩` and prove the remaining obligations. Introduce and unpack `ν ⟨μ, hμ, hνμ⟩`. Establish `hν : ν = c * a⁻¹ - g.1 * μ` using `by rw [← hνμ]; abel`.

Use `set K1 := κ g with hK1`. Use `set K2 := κ' g with hK2`. Establish `hm : (w⁻¹ * K1⁻¹) * g = K2` using `by rw [hgeq]; group`. Establish `hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹` using `by rw [← hm]; group`. Establish `hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) = emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)`.

Rewrite using `[mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk, inv_one, ← emb_mul_emb]`. Simplify using `only [mul_assoc, hw]`. Rewrite using `[hX]`. Use `set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM`. Establish `hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 = fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1)`.

Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]`. Conclude with `lowU_conj_blocks _ _ _ _ _ _ _`. Establish `h21 : M * (c - ν * a) = K2.1 * (μ * a)`. Rewrite using `[hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]`. Establish `he' : e - ν * b = E + g.1 * μ * b` using `by rw [hν, hE_def, Matrix.sub_mul]; abel`.

Establish `h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1)`. Rewrite using `[he', Matrix.mul_add, Matrix.add_mul]`. Use `congr 1`. Rewrite using `[hM, ← hm', ← hE'v]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`.

Rewrite using `[← hm, hM]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Establish `hwI : IsIntM w.1`. Establish `h` using `inv_torusElt_int (D := D) hϖ s`. Rewrite `h` using `[val_inv_torusElt]`.

Rewrite using `[hw, val_torusElt]`. Simplify using `using h`. Establish `hμa : ∀ i l, valuation k ((μ * a) i l) < 1` using `GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)`. Establish `hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1` using `val_lt_mul (isIntM_of_mem_KO hκ'g) hμa`. Establish `hwdet : (w⁻¹).1.det * w.1.det = 1`.

Rewrite using `[← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]`. Use `mem_parahoric_of ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hXv, h21, h22]`. Use `isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩` and prove the remaining obligations. Introduce `i l`.

Conclude with `add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l) (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)`. Establish `hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det = (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det)`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one, val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul, Matrix.det_mul]`. Simplify using `only [Matrix.det_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hdet, hwdet, mul_one, map_mul, hjd, mul_one]`. Conclude with `val_det_of_mem_KO (inv_mem hκg)`. Introduce `i l`. Rewrite using `[hXv, fromBlocks_apply₂₁, h21]`. Conclude with `hll i l`.
-/
theorem exists_lowU_diag_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj
  set w := torusElt k D ϖ (indic s) with hw
  have hjI : IsIntM j.1 := isIntM_of_mem_parahoric hj
  have hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1 := (mem_parahoric.1 hj).2
  have hjd : valuation k j.1.det = 1 := val_det_of_mem_KO (mem_parahoric.1 hj).1
  obtain ⟨ha, he⟩ := (val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd
  obtain ⟨haI, hbI, hcI, heI⟩ := isIntM_toBlocks hjI
  set a := j.1.toBlocks₁₁ with ha_def
  set b := j.1.toBlocks₁₂ with hb_def
  set c := j.1.toBlocks₂₁ with hc_def
  set e := j.1.toBlocks₂₂ with he_def
  have hcM : ∀ i l, valuation k (c i l) < 1 := fun i l => hjl i l
  have ha0 : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at ha; exact zero_ne_one ha
  have hainvI : IsIntM a⁻¹ := isIntM_inv haI ha
  have hinva : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha0
  letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0
  set E := e - c * a⁻¹ * b with hE_def
  have hjE : j.1.det = a.det * E.det := by
    rw [← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hEd : valuation k E.det = 1 := by
    rw [hjE, map_mul, ha, one_mul] at hjd; exact hjd
  have hEI : IsIntM E := isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).2
    (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)
  set E' : GL D k := hEu.unit with hE'_def
  have hE'v : E'.1 = E := hEu.unit_spec
  have hE'K : E' ∈ KO k D := mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)
  obtain ⟨g, ⟨hgR, hgK⟩, -⟩ := hR.2 E' hE'K
  obtain ⟨hκg, hκ'g, hgeq⟩ := hκ g hgR

  refine ⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩
  rintro ν ⟨μ, hμ, hνμ⟩
  have hν : ν = c * a⁻¹ - g.1 * μ := by rw [← hνμ]; abel
  set K1 := κ g with hK1
  set K2 := κ' g with hK2
  have hm : (w⁻¹ * K1⁻¹) * g = K2 := by rw [hgeq]; group
  have hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹ := by rw [← hm]; group
  have hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w) := by
    rw [mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk,
      inv_one, ← emb_mul_emb]
    simp only [mul_assoc, hw]
  rw [hX]
  set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM
  have hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 =
      fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]
    exact lowU_conj_blocks _ _ _ _ _ _ _
  have h21 : M * (c - ν * a) = K2.1 * (μ * a) := by
    rw [hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]
  have he' : e - ν * b = E + g.1 * μ * b := by rw [hν, hE_def, Matrix.sub_mul]; abel
  have h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1) := by
    rw [he', Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [hM, ← hm', ← hE'v]; simp only [Units.val_mul, Matrix.mul_assoc]
    · rw [← hm, hM]; simp only [Units.val_mul, Matrix.mul_assoc]
  have hwI : IsIntM w.1 := by
    have h := inv_torusElt_int (D := D) hϖ s
    rw [val_inv_torusElt] at h
    rw [hw, val_torusElt]; simpa using h
  have hμa : ∀ i l, valuation k ((μ * a) i l) < 1 := GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)
  have hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1 := val_lt_mul (isIntM_of_mem_KO hκ'g) hμa
  have hwdet : (w⁻¹).1.det * w.1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hXv, h21, h22]
    refine isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩
    intro i l
    exact add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l)
      (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)
  · have hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det =
        (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one,
        val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul,
        Matrix.det_mul]
      simp only [Matrix.det_one]; ring
    rw [hdet, hwdet, mul_one, map_mul, hjd, mul_one]
    exact val_det_of_mem_KO (inv_mem hκg)
  · intro i l
    rw [hXv, fromBlocks_apply₂₁, h21]
    exact hll i l

end GlobalTheory.LowerHecke

end
