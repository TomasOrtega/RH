import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HTAaLbMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatB

open Alg LatA

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

/- English proof (translation)
Introduce `c` and use `⟨by rw [map_add, (hv c).1, (hw c).1, add_zero], by rw [map_add, (hv c).2, (hw c).2, add_zero]⟩`.
-/
theorem inW_add {v w : (VS D).V} (hv : InW X v) (hw : InW X w) : InW X (v + w) := fun c =>
  ⟨by rw [map_add, (hv c).1, (hw c).1, add_zero], by rw [map_add, (hv c).2, (hw c).2, add_zero]⟩

/- English proof (translation)
Introduce `e` and use `⟨by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).1, mul_zero], by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).2, mul_zero]⟩`.
-/
theorem inW_sum (s : Finset (Fin D.R.rS)) (c : Fin D.R.rS → D.host.E) (v : Fin D.R.rS → (VS D).V)
    (hv : ∀ d, InW X (v d)) : InW X (∑ d ∈ s, c d • v d) := fun e =>
  ⟨by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).1, mul_zero],
   by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).2, mul_zero]⟩

/- English proof (translation)
Use `set v := pW X (n (X.fY a)) + ∑ d, Bq (X := X) n d a • xq X n d with hv`. Establish `hvW : InW X v` using `inW_add (pW_inW X _) (inW_sum _ _ _ fun d => xq_inW (X := X) d)`. Establish `horth : ∀ w, InW X w → (VS D).hT v w = 0`. Introduce `w hw`. Rewrite using `[hv, map_add, LinearMap.add_apply, hT_sumL, omega_rel hn a hw]`.

Simplify using `only [neg_add_cancel]`. Establish `hall : ∀ y, (VS D).hT v y = 0`. Introduce `y`. Rewrite using `[decomp X y, map_add, map_add, hT_sumR, hT_sumR, horth _ (pW_inW X y)]`. Establish `h1 : ∀ c, (VS D).hT v (X.eX c) = 0` using `fun c => by rw [hsw, (hvW c).1, star_zero]`.

Establish `h2 : ∀ c, (VS D).hT v (X.fY c) = 0` using `fun c => by rw [hsw, (hvW c).2, star_zero]`. Simplify using `only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]`. Establish `hv0 : v = 0` using `(VS D).nondeg.1 v hall`. Conclude with `eq_neg_of_add_eq_zero_left hv0`.
-/
theorem pW_nf (hn : NFl X u n) (a : Fin D.R.rS) :
    pW X (n (X.fY a)) = -∑ d, Bq (X := X) n d a • xq X n d := by
  set v := pW X (n (X.fY a)) + ∑ d, Bq (X := X) n d a • xq X n d with hv
  have hvW : InW X v := inW_add (pW_inW X _) (inW_sum _ _ _ fun d => xq_inW (X := X) d)
  have horth : ∀ w, InW X w → (VS D).hT v w = 0 := by
    intro w hw
    rw [hv, map_add, LinearMap.add_apply, hT_sumL, omega_rel hn a hw]
    simp only [neg_add_cancel]
  have hall : ∀ y, (VS D).hT v y = 0 := by
    intro y
    rw [decomp X y, map_add, map_add, hT_sumR, hT_sumR, horth _ (pW_inW X y)]
    have h1 : ∀ c, (VS D).hT v (X.eX c) = 0 := fun c => by rw [hsw, (hvW c).1, star_zero]
    have h2 : ∀ c, (VS D).hT v (X.fY c) = 0 := fun c => by rw [hsw, (hvW c).2, star_zero]
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  have hv0 : v = 0 := (VS D).nondeg.1 v hall
  exact eq_neg_of_add_eq_zero_left hv0

/- English proof (translation)
Use `conv_lhs => rw [nw hn hw]`. Rewrite using `[pW_add, pW_sum_e, add_zero, pW_of_inW X hw]`.
-/
theorem pW_nw (hn : NFl X u n) {w : (VS D).V} (hw : InW X w) : pW X (n w) = w := by
  conv_lhs => rw [nw hn hw]
  rw [pW_add, pW_sum_e, add_zero, pW_of_inW X hw]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [pW]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pW_add, pW_smul, ih]`.
-/
theorem pW_sum (s : Finset (Fin D.R.rS)) (c : Fin D.R.rS → D.host.E) (v : Fin D.R.rS → (VS D).V) :
    pW X (∑ d ∈ s, c d • v d) = ∑ d ∈ s, c d • pW X (v d) := by
  induction s using Finset.induction_on with
  | empty => simp [pW]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pW_add, pW_smul, ih]

/- English proof (translation)
Establish `hdet : X0.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]`. Simplify using `[hd]`. Establish `hU : IsUnit X0.det` using `by rw [hdet]; exact isUnit_one`. Establish `hXY : X0 * X0⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hU`.

Establish `hYup : ∀ b a, a < b → X0⁻¹ b a = 0`. Establish `hbt : X0.BlockTriangular id` using `fun i j hij => hup i j hij`. Use `haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU`. Conclude with `fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h`. Use `⟨hYup, fun a => ?_⟩` and prove the remaining obligations.

Establish `h` using `congrFun (congrFun hXY a) a`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul]`. Establish `hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0`. Use `Finset.sum_eq_zero fun e he => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1` into its components or cases.

Rewrite using `[hup a e h1, zero_mul]`. Rewrite using `[hYup e a h1, mul_zero]`. Rewrite `h` using `[hz, add_zero]`. Conclude with `h`.
-/
theorem inv_up (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) : (∀ b a, a < b → X0⁻¹ b a = 0) ∧ ∀ a, X0⁻¹ a a = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
    simp [hd]
  have hU : IsUnit X0.det := by rw [hdet]; exact isUnit_one
  have hXY : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hYup : ∀ b a, a < b → X0⁻¹ b a = 0 := by
    have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
    haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
    exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h
  refine ⟨hYup, fun a => ?_⟩
  have h := congrFun (congrFun hXY a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [hYup e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

end LatB

open LatB LatA Alg in

/- English proof (translation)
Introduce `D X u n hn hLQ`. Take `⟨hXs, hxs, hMs⟩` from `hLQ`. Establish `hup : ∀ b a, a < b → Xq X n b a = 0` using `fun b a h => Xq_lower hn h`. Establish `hd : ∀ a, Xq X n a a = 1` using `Xq_diag hn`. Establish `hXs' : ∀ b a, b < a → Xq X n b a ∈ aaD D b * (aaD D a)⁻¹` using `hXs`.

Establish `hMs' : ∀ b a, Mq X n b a ∈ aaD D b * aaD D a` using `hMs`. Establish `hXinv` using `shape_inv (Xq X n) hup hd hXs'`. Take `⟨hYup, hYd⟩` from `inv_up (Xq X n) hup hd`. Establish `hdet : IsUnit (Xq X n).det` using `by rw [Xq_det hn]; exact isUnit_one`. Establish `hAeq : Xq X n * Mq X n = Aq X n`.

Unfold `Mq`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hdet]`. Establish `hA : ∀ b a, Aq X n b a ∈ aaD D b * aaD D a`. Rewrite using `[← hAeq]`. Conclude with `shape_mul (Xq X n) (Mq X n) hup hd hXs' hMs'`.

Establish `hBeq : Bq (X` using `X) n = ((Xq X n)⁻¹)ᴴ := by`. Establish `h` using `XB hn`. Rewrite using `[Matrix.conjTranspose_nonsing_inv]`. Conclude with `(Matrix.inv_eq_right_inv h).symm`. Establish `hB : ∀ d a, Bq (X` using `X) n d a ∈ (aaD D d)⁻¹ * aaD D a := by`.

Introduce `d a`. Rewrite using `[hBeq, Matrix.conjTranspose_apply]`. Break down `lt_trichotomy a d with h | h | h` into its components or cases. Rewrite using `[mul_comm]`. Conclude with `SS_mul (SS_aaD a) (SS_inv (SS_aaD d)) _ (hXinv a d h)`.

Substitute `h` using the available equality. Rewrite using `[hYd, star_one, mul_comm]`. Conclude with `one_mem_aa a`. Rewrite using `[hYup a d h, star_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `hsub : ∀ x ∈ (VS D).L0, n x ∈ (VS D).L0`. Introduce `x hx`. Take `⟨hf, he, hw⟩` from `(mem_hermitianStandardLattice_iff_pairing_integral X x).1 hx`. Establish `hwW : InW X (pW X x)` using `pW_inW X x`. Establish `hnx : n x = ∑ c, (VS D).hT (X.fY c) x • n (X.eX c) + ∑ c, (VS D).hT (X.eX c) x • n (X.fY c) + n (pW X x)` using `by conv_lhs => rw [decomp X x]`.

Simplify using `only [map_add, map_sum, map_smul]`. Rewrite using `[mem_hermitianStandardLattice_iff_pairing_integral X]`. Use `⟨fun b => ?_, fun b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hnx, map_add, map_add, hT_sumR, hT_sumR, row hn b hwW]`. Use `Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)) (hT_aaLb_mem X (hxs b) hw)` and prove the remaining obligations.

Use `show (VS D).hT (X.fY c) x * Xq X n b c ∈ aaD D b`. Break down `lt_trichotomy c b with h | h | h` into its components or cases. Rewrite using `[hup b c h, mul_zero]`. Conclude with `Submodule.zero_mem _`. Substitute `h` using the available equality.

Rewrite using `[hd, mul_one]`. Conclude with `hf c`. Establish `e : aaD D c * (aaD D b * (aaD D c)⁻¹) = aaD D b`. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ (aa_ne c), mul_one]`. Rewrite using `[← e]`.

Conclude with `FractionalIdeal.mul_mem_mul (hf c) (hXs' b c h)`. Use `show (VS D).hT (X.eX c) x * Aq X n b c ∈ aaD D b`. Establish `e : (aaD D c)⁻¹ * (aaD D b * aaD D c) = aaD D b`. Rewrite using `[mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]`. Rewrite using `[← e]`.

Conclude with `FractionalIdeal.mul_mem_mul (he c) (hA b c)`. Rewrite using `[hnx, map_add, map_add, hT_sumR, hT_sumR]`. Establish `h1 : ∀ c, (VS D).hT (X.eX b) (n (X.eX c)) = 0` using `fun c => by`. Rewrite using `[Xq_expand hn c, hT_sumR]`. Simplify using `only [X.ee, mul_zero, Finset.sum_const_zero]`.

Establish `h2 : (VS D).hT (X.eX b) (n (pW X x)) = 0`. Rewrite using `[nw hn hwW, map_add, hT_sumR, (hwW b).1, zero_add]`. Simplify using `only [X.ee, mul_zero, Finset.sum_const_zero]`. Simplify using `only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, add_zero]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations.

Use `show (VS D).hT (X.eX c) x * Bq (X := X) n b c ∈ (aaD D b)⁻¹`. Establish `e : (aaD D c)⁻¹ * ((aaD D b)⁻¹ * aaD D c) = (aaD D b)⁻¹`. Rewrite using `[mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]`. Rewrite using `[← e]`. Conclude with `FractionalIdeal.mul_mem_mul (he c) (hB b c)`.

Rewrite using `[hnx, pW_add, pW_add, pW_sum, pW_sum, pW_nw hn hwW]`. Establish `h1 : ∀ c, pW X (n (X.eX c)) = 0` using `fun c => by rw [Xq_expand hn c, pW_sum_e]`. Simplify using `only [h1, smul_zero, Finset.sum_const_zero, zero_add, pW_nf hn]`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) hw` and prove the remaining obligations. Rewrite using `[smul_neg, Finset.smul_sum]`.

Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `smul_aaLb X ?_ (hxs d)` and prove the remaining obligations. Establish `e : (aaD D c)⁻¹ * ((aaD D d)⁻¹ * aaD D c) = (aaD D d)⁻¹`. Rewrite using `[mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]`.

Rewrite using `[← e]`. Conclude with `FractionalIdeal.mul_mem_mul (he c) (hB d c)`. Establish `hle : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 ≤ (VS D).L0`. Introduce `y hy`. Rewrite `hy` using `[Formalism.HermitianLatticesTheory.isomAct_mem_gmap]`.

Use `hsub _ hy` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0` using `(VS D).baseLattice_isUnimodular`. Establish `hUg : Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap n (VS D).L0) = Formalism.HermitianLatticesTheory.gmap n (VS D).L0`. Rewrite using `[Formalism.MainNotions.BridgeLemma₂.c3sub_dual_gmap _ n hn.1, hU0]`.

Use `le_antisymm hle ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[← hUg, Formalism.HermitianLatticesTheory.isomAct_mem_dual]`. Rewrite `hx` using `[← hU0, Formalism.HermitianLatticesTheory.isomAct_mem_dual]`. Conclude with `fun y hy => hx y (hle hy)`.
-/
theorem dictLatB_holds : DictLatB := by
  intro D X u n hn hLQ
  obtain ⟨hXs, hxs, hMs⟩ := hLQ
  have hup : ∀ b a, a < b → Xq X n b a = 0 := fun b a h => Xq_lower hn h
  have hd : ∀ a, Xq X n a a = 1 := Xq_diag hn
  have hXs' : ∀ b a, b < a → Xq X n b a ∈ aaD D b * (aaD D a)⁻¹ := hXs
  have hMs' : ∀ b a, Mq X n b a ∈ aaD D b * aaD D a := hMs
  have hXinv := shape_inv (Xq X n) hup hd hXs'
  obtain ⟨hYup, hYd⟩ := inv_up (Xq X n) hup hd
  have hdet : IsUnit (Xq X n).det := by rw [Xq_det hn]; exact isUnit_one
  have hAeq : Xq X n * Mq X n = Aq X n := by
    unfold Mq; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hA : ∀ b a, Aq X n b a ∈ aaD D b * aaD D a := by
    rw [← hAeq]; exact shape_mul (Xq X n) (Mq X n) hup hd hXs' hMs'
  have hBeq : Bq (X := X) n = ((Xq X n)⁻¹)ᴴ := by
    have h := XB hn
    rw [Matrix.conjTranspose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv h).symm
  have hB : ∀ d a, Bq (X := X) n d a ∈ (aaD D d)⁻¹ * aaD D a := by
    intro d a
    rw [hBeq, Matrix.conjTranspose_apply]
    rcases lt_trichotomy a d with h | h | h
    · rw [mul_comm]; exact SS_mul (SS_aaD a) (SS_inv (SS_aaD d)) _ (hXinv a d h)
    · subst h; rw [hYd, star_one, mul_comm]; exact one_mem_aa a
    · rw [hYup a d h, star_zero]; exact Submodule.zero_mem _

  have hsub : ∀ x ∈ (VS D).L0, n x ∈ (VS D).L0 := by
    intro x hx
    obtain ⟨hf, he, hw⟩ := (mem_hermitianStandardLattice_iff_pairing_integral X x).1 hx
    have hwW : InW X (pW X x) := pW_inW X x
    have hnx : n x = ∑ c, (VS D).hT (X.fY c) x • n (X.eX c) + ∑ c, (VS D).hT (X.eX c) x • n (X.fY c) +
        n (pW X x) := by
      conv_lhs => rw [decomp X x]
      simp only [map_add, map_sum, map_smul]
    rw [mem_hermitianStandardLattice_iff_pairing_integral X]
    refine ⟨fun b => ?_, fun b => ?_, ?_⟩
    · rw [hnx, map_add, map_add, hT_sumR, hT_sumR, row hn b hwW]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_)
        (Submodule.sum_mem _ fun c _ => ?_)) (hT_aaLb_mem X (hxs b) hw)
      · show (VS D).hT (X.fY c) x * Xq X n b c ∈ aaD D b
        rcases lt_trichotomy c b with h | h | h
        · rw [hup b c h, mul_zero]; exact Submodule.zero_mem _
        · subst h; rw [hd, mul_one]; exact hf c
        · have e : aaD D c * (aaD D b * (aaD D c)⁻¹) = aaD D b := by
            rw [mul_comm, mul_assoc, inv_mul_cancel₀ (aa_ne c), mul_one]
          rw [← e]; exact FractionalIdeal.mul_mem_mul (hf c) (hXs' b c h)
      · show (VS D).hT (X.eX c) x * Aq X n b c ∈ aaD D b
        have e : (aaD D c)⁻¹ * (aaD D b * aaD D c) = aaD D b := by
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
        rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hA b c)
    · rw [hnx, map_add, map_add, hT_sumR, hT_sumR]
      have h1 : ∀ c, (VS D).hT (X.eX b) (n (X.eX c)) = 0 := fun c => by
        rw [Xq_expand hn c, hT_sumR]; simp only [X.ee, mul_zero, Finset.sum_const_zero]
      have h2 : (VS D).hT (X.eX b) (n (pW X x)) = 0 := by
        rw [nw hn hwW, map_add, hT_sumR, (hwW b).1, zero_add]
        simp only [X.ee, mul_zero, Finset.sum_const_zero]
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
      refine Submodule.sum_mem _ fun c _ => ?_
      show (VS D).hT (X.eX c) x * Bq (X := X) n b c ∈ (aaD D b)⁻¹
      have e : (aaD D c)⁻¹ * ((aaD D b)⁻¹ * aaD D c) = (aaD D b)⁻¹ := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
      rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hB b c)
    · rw [hnx, pW_add, pW_add, pW_sum, pW_sum, pW_nw hn hwW]
      have h1 : ∀ c, pW X (n (X.eX c)) = 0 := fun c => by rw [Xq_expand hn c, pW_sum_e]
      simp only [h1, smul_zero, Finset.sum_const_zero, zero_add, pW_nf hn]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) hw
      rw [smul_neg, Finset.smul_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d _ => ?_)
      rw [smul_smul]
      refine smul_aaLb X ?_ (hxs d)
      have e : (aaD D c)⁻¹ * ((aaD D d)⁻¹ * aaD D c) = (aaD D d)⁻¹ := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
      rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hB d c)

  have hle : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 ≤ (VS D).L0 := by
    intro y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := hsub _ hy
    rwa [LinearEquiv.apply_symm_apply] at this
  have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
  have hUg : Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap n (VS D).L0) = Formalism.HermitianLatticesTheory.gmap n (VS D).L0 := by
    rw [Formalism.MainNotions.BridgeLemma₂.c3sub_dual_gmap _ n hn.1, hU0]
  refine le_antisymm hle ?_
  intro x hx
  rw [← hUg, Formalism.HermitianLatticesTheory.isomAct_mem_dual]
  rw [← hU0, Formalism.HermitianLatticesTheory.isomAct_mem_dual] at hx
  exact fun y hy => hx y (hle hy)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
