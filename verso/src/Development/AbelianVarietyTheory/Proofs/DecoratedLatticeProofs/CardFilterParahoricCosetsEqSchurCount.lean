import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k]

/- English proof (translation)
Rewrite using `[mul_apply]`. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun m _ => by`. Rewrite using `[mul_comm]`. Conclude with `GlobalTheory.DatumEigen.val_mul_lt (hP _ _) (hc _ _)`.
-/
theorem val_lt_mul_right {l m n : Type} [Fintype m] {c : Matrix l m k} {P : Matrix m n k}
    (hc : ∀ i j, valuation k (c i j) < 1) (hP : IsIntM P) (i j) : valuation k ((c * P) i j) < 1 := by
  rw [mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun m _ => by
    rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hP _ _) (hc _ _)

/- English proof (translation)
Introduce `i j` and use `(show valuation k (M i j) ≤ 1 from (h i j).le)`.
-/
theorem isIntM_of_lt {m n : Type} {M : Matrix m n k} (h : ∀ i j, valuation k (M i j) < 1) : IsIntM M :=
  fun i j => (show valuation k (M i j) ≤ 1 from (h i j).le)

section Alg
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def nlow (v : Matrix D A k) : GL (A ⊕ D) k :=
  ⟨fromBlocks 1 0 v 1, fromBlocks 1 0 (-v) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_nlow (v : Matrix D A k) : (nlow v).val = fromBlocks 1 0 v 1 := rfl

end Alg

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/- English proof (translation)
Use `mem_parahoric_of ?_ ?_ fun i j => by simpa [val_nlow] using hv i j` and prove the remaining obligations. Rewrite using `[val_nlow]`. Conclude with `isIntM_fromBlocks_iff.2 ⟨isIntM_one, isIntM_zero, isIntM_of_lt hv, isIntM_one⟩`. Rewrite using `[val_nlow, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, map_one]`.
-/
theorem nlow_mem {v : Matrix D' A k} (hv : ∀ i j, valuation k (v i j) < 1) : nlow v ∈ parahoric k A D' := by
  refine mem_parahoric_of ?_ ?_ fun i j => by simpa [val_nlow] using hv i j
  · rw [val_nlow]; exact isIntM_fromBlocks_iff.2 ⟨isIntM_one, isIntM_zero, isIntM_of_lt hv, isIntM_one⟩
  · rw [val_nlow, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, map_one]

/- English proof (translation)
Establish `hlt : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Rewrite using `[val_torusElt]`. Introduce `i j`. Rewrite using `[diagonal_apply]`. Use `split_ifs`.

Use `show valuation k _ ≤ 1`. Rewrite using `[map_zpow₀]`. Apply the tactic sequence `exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)`. Conclude with `zero_mem _`.
-/
theorem torus_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) :
    IsIntM (torusElt k D ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

/- English proof (translation)
Establish `hu : IsUnit x.toBlocks₁₁.det` using `isUnit_iff_ne_zero.2 hx.det_ne`. Establish `hxe` using `fromBlocks_toBlocks x`. Use `set a := x.toBlocks₁₁`. Use `set b := x.toBlocks₁₂`. Use `set c := x.toBlocks₂₁`.

Use `set e := x.toBlocks₂₂`. Rewrite using `[schur, ← hxe, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]`. Rewrite using `[val_nlow, fromBlocks_multiply]`. Simplify using `only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]`. Use `congr 1`.

Rewrite using `[Matrix.neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, neg_add_cancel]`. Rewrite using `[Matrix.neg_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem nlow_mul_eq {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) :
    (nlow (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹))).val * x = fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x) := by
  have hu : IsUnit x.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hx.det_ne
  have hxe := fromBlocks_toBlocks x
  set a := x.toBlocks₁₁
  set b := x.toBlocks₁₂
  set c := x.toBlocks₂₁
  set e := x.toBlocks₂₂
  rw [schur, ← hxe, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  rw [val_nlow, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · rw [Matrix.neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, neg_add_cancel]
  · rw [Matrix.neg_mul]; abel

/- English proof (translation)
Establish `hxI : IsIntM x` using `hx.1`. Take `⟨i11, i12, -, -⟩` from `isIntM_toBlocks hxI`. Establish `inv11 : IsIntM x.toBlocks₁₁⁻¹` using `isIntM_inv i11 hx.2.1`. Establish `hu : IsUnit x.toBlocks₁₁.det` using `isUnit_iff_ne_zero.2 hx.det_ne`. Establish `hS` using `schur_int hx`.

Establish `e : V * fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x) = fromBlocks (V.toBlocks₁₁ * x.toBlocks₁₁) (V.toBlocks₁₁ * x.toBlocks₁₂ + V.toBlocks₁₂ * schur x) (V.toBlocks₂₁ * x.toBlocks₁₁) (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x)` using `by conv_lhs => rw [← fromBlocks_toBlocks V]`. Rewrite using `[fromBlocks_multiply]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hI, -, hl⟩`. Take `⟨-, -, -, d⟩` from `isIntM_fromBlocks_iff.1 (show IsIntM _ from hI)`. Establish `hR : ∀ i l, valuation k (V.toBlocks₂₁ i l) < 1`. Establish `e2 : V.toBlocks₂₁ = V.toBlocks₂₁ * x.toBlocks₁₁ * x.toBlocks₁₁⁻¹`. Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]`.

Introduce `i l`. Rewrite using `[e2]`. Conclude with `val_lt_mul_right (fun a b => by simpa using hl a b) inv11 i l`. Use `⟨hR, ?_⟩` and prove the remaining obligations. Establish `e3 : V.toBlocks₂₂ * schur x = (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x) - V.toBlocks₂₁ * x.toBlocks₁₂` using `by abel`.

Rewrite using `[e3]`. Conclude with `isIntM_sub d (isIntM_mul (isIntM_of_lt hR) i12)`. Introduce and unpack `⟨hR, hUS⟩`. Establish `iR` using `isIntM_of_lt hR`. Use `⟨isIntM_fromBlocks_iff.2 ⟨isIntM_mul h11 i11, ?_, isIntM_mul iR i11, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `fun a b => add_mem (isIntM_mul h11 i12 a b) (isIntM_mul h12 hS a b)`. Conclude with `fun a b => add_mem (isIntM_mul iR i12 a b) (hUS a b)`. Rewrite using `[toBlocks_fromBlocks₁₁, det_mul, map_mul, hd, hx.2.1, one_mul]`. Introduce `i l`. Rewrite using `[fromBlocks_apply₂₁]`.

Conclude with `val_lt_mul_right hR i11 i l`.
-/
theorem inSupp_mul_iff {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) (V : Matrix (A ⊕ D') (A ⊕ D') k)
    (h11 : IsIntM V.toBlocks₁₁) (hd : valuation k V.toBlocks₁₁.det = 1) (h12 : IsIntM V.toBlocks₁₂) :
    InSupp (V * fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x)) ↔
      (∀ i l, valuation k (V.toBlocks₂₁ i l) < 1) ∧ IsIntM (V.toBlocks₂₂ * schur x) := by
  have hxI : IsIntM x := hx.1
  obtain ⟨i11, i12, -, -⟩ := isIntM_toBlocks hxI
  have inv11 : IsIntM x.toBlocks₁₁⁻¹ := isIntM_inv i11 hx.2.1
  have hu : IsUnit x.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hx.det_ne
  have hS := schur_int hx
  have e : V * fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x) = fromBlocks (V.toBlocks₁₁ * x.toBlocks₁₁)
      (V.toBlocks₁₁ * x.toBlocks₁₂ + V.toBlocks₁₂ * schur x) (V.toBlocks₂₁ * x.toBlocks₁₁)
      (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x) := by
    conv_lhs => rw [← fromBlocks_toBlocks V]
    rw [fromBlocks_multiply]; simp
  rw [e]
  constructor
  · rintro ⟨hI, -, hl⟩
    obtain ⟨-, -, -, d⟩ := isIntM_fromBlocks_iff.1 (show IsIntM _ from hI)
    have hR : ∀ i l, valuation k (V.toBlocks₂₁ i l) < 1 := by
      have e2 : V.toBlocks₂₁ = V.toBlocks₂₁ * x.toBlocks₁₁ * x.toBlocks₁₁⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
      intro i l; rw [e2]
      exact val_lt_mul_right (fun a b => by simpa using hl a b) inv11 i l
    refine ⟨hR, ?_⟩
    have e3 : V.toBlocks₂₂ * schur x =
        (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x) - V.toBlocks₂₁ * x.toBlocks₁₂ := by abel
    rw [e3]; exact isIntM_sub d (isIntM_mul (isIntM_of_lt hR) i12)
  · rintro ⟨hR, hUS⟩
    have iR := isIntM_of_lt hR
    refine ⟨isIntM_fromBlocks_iff.2 ⟨isIntM_mul h11 i11, ?_, isIntM_mul iR i11, ?_⟩, ?_, ?_⟩
    · exact fun a b => add_mem (isIntM_mul h11 i12 a b) (isIntM_mul h12 hS a b)
    · exact fun a b => add_mem (isIntM_mul iR i12 a b) (hUS a b)
    · rw [toBlocks_fromBlocks₁₁, det_mul, map_mul, hd, hx.2.1, one_mul]
    · intro i l; rw [fromBlocks_apply₂₁]; exact val_lt_mul_right hR i11 i l

/- English proof (translation)
Take `⟨y11, y12, -, -⟩` from `isIntM_toBlocks (isIntM_of_mem_parahoric hY)`. Establish `hv : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val = fromBlocks Y.val.toBlocks₁₁ (Y.val.toBlocks₁₂ * (E⁻¹ * T).val) ((T⁻¹).val * Y.val.toBlocks₂₁) 1`. Rewrite using `[Units.val_mul, Units.val_mul, val_dg, val_dg, fromBlocks_diag_mul, mul_fromBlocks_diag]`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]`. Use `congr 1`.

Rewrite using `[← hEY, ← Units.val_mul, ← Units.val_mul, show T⁻¹ * E * (E⁻¹ * T) = 1 by group, Units.val_one]`. Use `mem_parahoric_of ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hv]`. Establish `hq : IsIntM (E⁻¹ * T).val`. Rewrite using `[Units.val_mul]`.

Conclude with `isIntM_mul (isIntM_of_mem_KO (inv_mem hE)) hT`. Conclude with `isIntM_fromBlocks_iff.2 ⟨y11, isIntM_mul y12 hq, isIntM_of_lt hl, isIntM_one⟩`. Establish `h1 : (T⁻¹).val.det * T.val.det = 1`. Rewrite using `[← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]`. Establish `e : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val.det = ((T⁻¹).val.det * T.val.det) * Y.val.det * (E⁻¹).val.det`.

Rewrite using `[Units.val_mul, Units.val_mul, det_mul, det_mul, det_dg, det_dg, Units.val_mul, det_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, h1, one_mul, map_mul, val_det_of_mem_KO (mem_parahoric.1 hY).1, val_det_of_mem_KO (inv_mem hE), one_mul]`. Introduce `i l`. Rewrite using `[hv]`.

Simplify using `using hl i l`.
-/
theorem key_mem {Y : GL (A ⊕ D') k} (hY : Y ∈ parahoric k A D') {E T : GL D' k} (hE : E ∈ KO k D')
    (hEY : E.val = Y.val.toBlocks₂₂) (hT : IsIntM T.val)
    (hl : ∀ i l, valuation k (((T⁻¹).val * Y.val.toBlocks₂₁) i l) < 1) :
    dg A T⁻¹ * Y * dg A (E⁻¹ * T) ∈ parahoric k A D' := by
  obtain ⟨y11, y12, -, -⟩ := isIntM_toBlocks (isIntM_of_mem_parahoric hY)
  have hv : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val =
      fromBlocks Y.val.toBlocks₁₁ (Y.val.toBlocks₁₂ * (E⁻¹ * T).val) ((T⁻¹).val * Y.val.toBlocks₂₁) 1 := by
    rw [Units.val_mul, Units.val_mul, val_dg, val_dg, fromBlocks_diag_mul, mul_fromBlocks_diag]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    congr 1
    rw [← hEY, ← Units.val_mul, ← Units.val_mul, show T⁻¹ * E * (E⁻¹ * T) = 1 by group, Units.val_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hv]
    have hq : IsIntM (E⁻¹ * T).val := by
      rw [Units.val_mul]; exact isIntM_mul (isIntM_of_mem_KO (inv_mem hE)) hT
    exact isIntM_fromBlocks_iff.2 ⟨y11, isIntM_mul y12 hq, isIntM_of_lt hl, isIntM_one⟩
  · have h1 : (T⁻¹).val.det * T.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have e : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val.det = ((T⁻¹).val.det * T.val.det) * Y.val.det * (E⁻¹).val.det := by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, det_dg, det_dg, Units.val_mul, det_mul]; ring
    rw [e, h1, one_mul, map_mul, val_det_of_mem_KO (mem_parahoric.1 hY).1, val_det_of_mem_KO (inv_mem hE), one_mul]
  · intro i l
    rw [hv]; simpa using hl i l

end GlobalTheory.ParHeckeTarget

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource
open Classical

/- English proof (translation)
Introduce `k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ s R d hR RK hRK x hx`. Rewrite `hR`, the goal using `[mtor_eq_dg]`. Use `set T := torusElt k D' ϖ (indic s) with hTdef`. Establish `hT : IsIntM T.val` using `torus_int hϖ s`. Use `set S := schur x with hSdef`.

Establish `hν : ∀ i l, valuation k ((-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) i l) < 1`. Take `⟨i11, -, -, -⟩` from `isIntM_toBlocks (show IsIntM x from hx.1)`. Introduce `i l`. Rewrite using `[Matrix.neg_apply, Valuation.map_neg]`. Conclude with `val_lt_mul_right (fun a b => hx.2.2 a b) (isIntM_inv i11 hx.2.1) i l`.

Use `set c := nlow (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) with hcdef`. Establish `hc : c ∈ parahoric k A D'` using `nlow_mem hν`. Establish `hcx : c.val * x = fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 S` using `nlow_mul_eq hx`. Establish `hJR : ∀ j ∈ R, j ∈ parahoric k A D'` using `fun j hj => (hR.1 j hj).1`. Establish `hcond : ∀ j ∈ parahoric k A D', InSupp (((j * dg A T)⁻¹).val * x) ↔ (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) ∧ IsIntM ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂ * S)`.

Introduce `j hj`. Establish `hY : (c * j)⁻¹ ∈ parahoric k A D'` using `inv_mem (mul_mem hc hj)`. Establish `e1 : (j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ * c` using `by rw [map_inv]; group`. Establish `e2 : (dg A T⁻¹ * (c * j)⁻¹).val = fromBlocks ((c * j)⁻¹).val.toBlocks₁₁ ((c * j)⁻¹).val.toBlocks₁₂ ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂)`. Rewrite using `[Units.val_mul, val_dg, fromBlocks_diag_mul]`.

Take `⟨y11, y12, -, -⟩` from `isIntM_toBlocks (isIntM_of_mem_parahoric hY)`. Rewrite using `[e1, Units.val_mul (dg A T⁻¹ * (c * j)⁻¹) c, Matrix.mul_assoc, hcx, inSupp_mul_iff hx _ (by rw [e2, toBlocks_fromBlocks₁₁]; exact y11) (by rw [e2, toBlocks_fromBlocks₁₁]; exact (GlobalTheory.DatumEigen.val_det_blocks hY).1) (by rw [e2, toBlocks_fromBlocks₁₂]; exact y12), e2, toBl …`. Establish `hkey : ∀ j ∈ parahoric k A D', (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) → (c * j * dg A T)⁻¹ * dg A ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ parahoric k A D'` using `fun j hj hl => by`. Establish `hY : (c * j)⁻¹ ∈ parahoric k A D'` using `inv_mem (mul_mem hc hj)`. Use `key_mem hY (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY) (lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY) hT hl` as an intermediate fact.

Rewrite using `[show (c * j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ by rw [map_inv]; group]`. Conclude with `this`. Set `pick : GL (A ⊕ D') k → GL D' k` to `fun j => if h : ∃ g, g ∈ RK ∧ g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' then h.choose else 1`. Establish `spec : ∀ j ∈ parahoric k A D', pick j ∈ RK ∧ (pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D'` using `fun j hj => by`. Establish `hY : (c * j)⁻¹ ∈ parahoric k A D'` using `inv_mem (mul_mem hc hj)`.

Establish `h` using `(hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY))).exists`. Simplify using `only [pick, dif_pos h]`. Conclude with `h.choose_spec`. Establish `uniq : ∀ j ∈ parahoric k A D', ∀ g ∈ RK, g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' → pick j = g` using `fun j hj g hg h => (hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear (inv_mem (mul_mem hc hj))))).unique (spec j hj) ⟨hg, h⟩`. Apply `Finset.card_nbij pick` to reduce the goal to its premises.

Introduce `j hj`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hj ⊢`. Take `⟨hjR, hin⟩` from `hj`. Establish `hJ` using `hJR j hjR`. Establish `hY : (c * j)⁻¹ ∈ parahoric k A D'` using `inv_mem (mul_mem hc hJ)`.

Take `⟨-, h22⟩` from `(hcond j hJ).1 hin`. Take `⟨hg, hK⟩` from `spec j hJ`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Establish `e : ((pick j)⁻¹).val = ((pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T)).val * ((T⁻¹).val * (lowerDiagonalBlockAsGL ((c * j)⁻¹)).val)`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`.

Use `congr 1`. Use `group`. Establish `: IsIntM (((pick j)⁻¹).val * S)`. Rewrite using `[e, Matrix.mul_assoc, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY]`. Conclude with `isIntM_mul (isIntM_of_mem_KO hK) h22`.

Conclude with `this`. Introduce `j₁ hj₁ j₂ hj₂ he`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hj₁ hj₂`. Take `⟨h1R, h1⟩` from `hj₁`. Take `⟨h2R, h2⟩` from `hj₂`.

Establish `hJ1` using `hJR _ h1R`. Establish `hJ2` using `hJR _ h2R`. Establish `m1` using `hkey j₁ hJ1 ((hcond j₁ hJ1).1 h1).1`. Establish `m2` using `hkey j₂ hJ2 ((hcond j₂ hJ2).1 h2).1`. Take `⟨-, hK1⟩` from `spec j₁ hJ1`.

Take `⟨-, hK2⟩` from `spec j₂ hJ2`. Rewrite `hK1` using `[he]`. Establish `hm : (j₁ * dg A T)⁻¹ * (j₂ * dg A T) ∈ parahoric k A D'`. Use `mul_mem (mul_mem (mul_mem m1 (dg_mem (inv_mem hK1))) (dg_mem hK2)) (inv_mem m2)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_mul, map_inv]`. Use `group`. Conclude with `(hR.2 j₂ hJ2).unique ⟨h1R, hm⟩ ⟨h2R, by simp⟩`. Introduce `g hg`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hg`.

Take `⟨hgR, hSg⟩` from `hg`. Take `⟨κ, hκ, κ', hκ', hgdef⟩` from `hRK.1 g hgR`. Establish `hj₀ : c⁻¹ * dg A κ ∈ parahoric k A D'` using `mul_mem (inv_mem hc) (dg_mem hκ)`. Take `⟨j, ⟨hjR, hm⟩, -⟩` from `hR.2 _ hj₀`. Use `set n := (j * dg A T)⁻¹ * (c⁻¹ * dg A κ * dg A T) with hndef`.

Establish `hJ` using `hJR j hjR`. Establish `hY : (c * j)⁻¹ ∈ parahoric k A D'` using `inv_mem (mul_mem hc hJ)`. Establish `eV : dg A T⁻¹ * (c * j)⁻¹ = n * dg A (κ * T)⁻¹`. Rewrite using `[hndef]`. Simplify using `only [map_mul, map_inv]`.

Use `group`. Establish `hb : ∀ (P : Matrix (A ⊕ D') (A ⊕ D') k), P = (dg A T⁻¹ * (c * j)⁻¹).val → P.toBlocks₂₁ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁ ∧ P.toBlocks₂₂ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂`. Introduce and unpack `P rfl`. Rewrite using `[Units.val_mul, val_dg, fromBlocks_diag_mul, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]`. Conclude with `⟨rfl, rfl⟩`.

Take `⟨h21, h22⟩` from `hb _ (by rw [eV])`. Rewrite `h21` using `[Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₁]`. Rewrite `h22` using `[Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₂]`. Establish `hE : lowerDiagonalBlockAsGL ((c * j)⁻¹) = T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹` using `by ext1`. Rewrite using `[lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY, Units.val_mul, Units.val_mul, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hm, Matrix.mul_assoc, h22, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.

Establish `hpick : pick j = g`. Use `uniq j hJ g hgR ?_` and prove the remaining obligations. Rewrite using `[hE, hgdef, show (κ * T * κ')⁻¹ * ((T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹)⁻¹ * T) = κ'⁻¹ * (lowerDiagonalBlockAsGL n)⁻¹ by group]`. Conclude with `mul_mem (inv_mem hκ') (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hm))`. Use `⟨j, ?_, hpick⟩` and prove the remaining obligations.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]`. Use `⟨hjR, (hcond j hJ).2 ⟨fun i l => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← h21]`. Conclude with `(mem_parahoric.1 hm).2 i l`. Rewrite using `[← h22, show (κ * T)⁻¹ = κ' * g⁻¹ by rw [hgdef]; group, Units.val_mul κ' g⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc]`.

Conclude with `isIntM_mul (isIntM_mul (isIntM_toBlocks (isIntM_of_mem_parahoric hm)).2.2.2 (isIntM_of_mem_KO hκ')) hSg`.
-/
theorem card_filter_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ s R d hR RK hRK x hx
  rw [mtor_eq_dg] at hR ⊢
  set T := torusElt k D' ϖ (indic s) with hTdef
  have hT : IsIntM T.val := torus_int hϖ s
  set S := schur x with hSdef
  have hν : ∀ i l, valuation k ((-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) i l) < 1 := by
    obtain ⟨i11, -, -, -⟩ := isIntM_toBlocks (show IsIntM x from hx.1)
    intro i l
    rw [Matrix.neg_apply, Valuation.map_neg]
    exact val_lt_mul_right (fun a b => hx.2.2 a b) (isIntM_inv i11 hx.2.1) i l
  set c := nlow (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) with hcdef
  have hc : c ∈ parahoric k A D' := nlow_mem hν
  have hcx : c.val * x = fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 S := nlow_mul_eq hx
  have hJR : ∀ j ∈ R, j ∈ parahoric k A D' := fun j hj => (hR.1 j hj).1
  have hcond : ∀ j ∈ parahoric k A D', InSupp (((j * dg A T)⁻¹).val * x) ↔
      (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) ∧
        IsIntM ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂ * S) := by
    intro j hj
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
    have e1 : (j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ * c := by rw [map_inv]; group
    have e2 : (dg A T⁻¹ * (c * j)⁻¹).val = fromBlocks ((c * j)⁻¹).val.toBlocks₁₁ ((c * j)⁻¹).val.toBlocks₁₂
        ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂) := by
      rw [Units.val_mul, val_dg, fromBlocks_diag_mul]
    obtain ⟨y11, y12, -, -⟩ := isIntM_toBlocks (isIntM_of_mem_parahoric hY)
    rw [e1, Units.val_mul (dg A T⁻¹ * (c * j)⁻¹) c, Matrix.mul_assoc, hcx,
      inSupp_mul_iff hx _ (by rw [e2, toBlocks_fromBlocks₁₁]; exact y11)
        (by rw [e2, toBlocks_fromBlocks₁₁]; exact (GlobalTheory.DatumEigen.val_det_blocks hY).1)
        (by rw [e2, toBlocks_fromBlocks₁₂]; exact y12),
      e2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  have hkey : ∀ j ∈ parahoric k A D', (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) →
      (c * j * dg A T)⁻¹ * dg A ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ parahoric k A D' := fun j hj hl => by
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
    have := key_mem hY (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY) (lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY) hT hl
    rw [show (c * j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ by rw [map_inv]; group]
    exact this
  let pick : GL (A ⊕ D') k → GL D' k := fun j =>
    if h : ∃ g, g ∈ RK ∧ g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' then h.choose else 1
  have spec : ∀ j ∈ parahoric k A D', pick j ∈ RK ∧ (pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' :=
    fun j hj => by
      have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
      have h := (hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY))).exists
      simp only [pick, dif_pos h]; exact h.choose_spec
  have uniq : ∀ j ∈ parahoric k A D', ∀ g ∈ RK, g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' → pick j = g :=
    fun j hj g hg h => (hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear (inv_mem (mul_mem hc hj))))).unique (spec j hj) ⟨hg, h⟩
  apply Finset.card_nbij pick
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hj ⊢
    obtain ⟨hjR, hin⟩ := hj
    have hJ := hJR j hjR
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hJ)
    obtain ⟨-, h22⟩ := (hcond j hJ).1 hin
    obtain ⟨hg, hK⟩ := spec j hJ
    refine ⟨hg, ?_⟩
    have e : ((pick j)⁻¹).val = ((pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T)).val *
        ((T⁻¹).val * (lowerDiagonalBlockAsGL ((c * j)⁻¹)).val) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    have : IsIntM (((pick j)⁻¹).val * S) := by
      rw [e, Matrix.mul_assoc, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY]
      exact isIntM_mul (isIntM_of_mem_KO hK) h22
    exact this
  · intro j₁ hj₁ j₂ hj₂ he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj₁ hj₂
    obtain ⟨h1R, h1⟩ := hj₁
    obtain ⟨h2R, h2⟩ := hj₂
    have hJ1 := hJR _ h1R
    have hJ2 := hJR _ h2R
    have m1 := hkey j₁ hJ1 ((hcond j₁ hJ1).1 h1).1
    have m2 := hkey j₂ hJ2 ((hcond j₂ hJ2).1 h2).1
    obtain ⟨-, hK1⟩ := spec j₁ hJ1
    obtain ⟨-, hK2⟩ := spec j₂ hJ2
    rw [he] at hK1
    have hm : (j₁ * dg A T)⁻¹ * (j₂ * dg A T) ∈ parahoric k A D' := by
      have := mul_mem (mul_mem (mul_mem m1 (dg_mem (inv_mem hK1))) (dg_mem hK2)) (inv_mem m2)
      convert this using 1
      simp only [map_mul, map_inv]; group
    exact (hR.2 j₂ hJ2).unique ⟨h1R, hm⟩ ⟨h2R, by simp⟩
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hg
    obtain ⟨hgR, hSg⟩ := hg
    obtain ⟨κ, hκ, κ', hκ', hgdef⟩ := hRK.1 g hgR
    have hj₀ : c⁻¹ * dg A κ ∈ parahoric k A D' := mul_mem (inv_mem hc) (dg_mem hκ)
    obtain ⟨j, ⟨hjR, hm⟩, -⟩ := hR.2 _ hj₀
    set n := (j * dg A T)⁻¹ * (c⁻¹ * dg A κ * dg A T) with hndef
    have hJ := hJR j hjR
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hJ)
    have eV : dg A T⁻¹ * (c * j)⁻¹ = n * dg A (κ * T)⁻¹ := by
      rw [hndef]; simp only [map_mul, map_inv]; group
    have hb : ∀ (P : Matrix (A ⊕ D') (A ⊕ D') k), P = (dg A T⁻¹ * (c * j)⁻¹).val →
        P.toBlocks₂₁ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁ ∧
          P.toBlocks₂₂ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂ := by
      rintro P rfl
      rw [Units.val_mul, val_dg, fromBlocks_diag_mul, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
      exact ⟨rfl, rfl⟩
    obtain ⟨h21, h22⟩ := hb _ (by rw [eV])
    rw [Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₁] at h21
    rw [Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₂] at h22
    have hE : lowerDiagonalBlockAsGL ((c * j)⁻¹) = T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹ := by
      ext1
      rw [lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY, Units.val_mul, Units.val_mul, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hm, Matrix.mul_assoc, h22, ← Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have hpick : pick j = g := by
      refine uniq j hJ g hgR ?_
      rw [hE, hgdef, show (κ * T * κ')⁻¹ * ((T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹)⁻¹ * T) = κ'⁻¹ * (lowerDiagonalBlockAsGL n)⁻¹ by group]
      exact mul_mem (inv_mem hκ') (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hm))
    refine ⟨j, ?_, hpick⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    refine ⟨hjR, (hcond j hJ).2 ⟨fun i l => ?_, ?_⟩⟩
    · rw [← h21]; exact (mem_parahoric.1 hm).2 i l
    · rw [← h22, show (κ * T)⁻¹ = κ' * g⁻¹ by rw [hgdef]; group, Units.val_mul κ' g⁻¹, ← Matrix.mul_assoc,
        Matrix.mul_assoc]
      exact isIntM_mul (isIntM_mul (isIntM_toBlocks (isIntM_of_mem_parahoric hm)).2.2.2 (isIntM_of_mem_KO hκ')) hSg

end GlobalTheory.ParHeckeTarget
