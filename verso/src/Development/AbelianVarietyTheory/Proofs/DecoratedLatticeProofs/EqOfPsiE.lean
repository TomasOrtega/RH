import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstVec

/- English proof (translation)
Establish `key : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∀ b, j' < b → T b j' = 0) → ∀ a, j ≤ a → T a j = if a = j then T j j * S j' j' * T j' j' else 0` using `fun j j' e H a ha => by`. Establish `e1 : T a j = ∑ b, T a j * S j' b * T b j'`. Use `congrFun (congrFun h j') j'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, this, mul_one]`.

Rewrite using `[e1, Finset.sum_eq_single j']`. Use `split_ifs with h1`. Rewrite using `[h1]`. Rewrite using `[hu j j' e a j' (by rw [Fin.le_def] at *; have := mt Fin.ext h1; omega), zero_mul]`. Introduce `b _ hb`.

Break down `lt_or_gt_of_ne hb with h1 | h1` into its components or cases. Rewrite using `[hu j j' e a b (by rw [Fin.le_def, Fin.lt_def] at *; omega), zero_mul]`. Rewrite using `[H b h1, mul_zero]`. Conclude with `fun h => absurd (Finset.mem_univ _) h`. Establish `tri : ∀ j : Fin (σ + 1), ∀ b, j < b → T b j = 0` using `fun j => by`.

Proceed by induction on `j using Fin.reverseInduction with`. Consider the case `last => exact fun b hb => absurd (Fin.le_last b) (not_le.2 hb)`. Consider the case `cast j ih => exact fun b hb => by rw [key j.castSucc j.succ rfl ih b hb.le, if_neg hb.ne']`. Establish `triS : S.BlockTriangular id`. Use `letI := invertibleOfLeftInverse T S h`.

Rewrite using `[← Matrix.inv_eq_left_inv h]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular fun a b hab => tri b a hab`. Establish `diag : ∀ j : Fin (σ + 1), T j j = 1` using `fun j => by`. Proceed by induction on `j using Fin.reverseInduction with`. Consider the case `last => exact hl`.

Consider the case `cast j ih`. Establish `h1` using `hs j.castSucc j.succ rfl`. Rewrite `h1` using `[Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ, if_pos (show j.succ.1 = j.castSucc.1 + 1 from rfl)]`. Rewrite using `[key j.castSucc j.succ rfl (tri _) _ le_rfl, if_pos rfl, h1, ih, one_mul]`. Conclude with `fun b _ hb => if_neg fun e => hb (Fin.ext e)`.

Conclude with `fun h => absurd (Finset.mem_univ _) h`. Introduce `a _ ha`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with e`. Break down `lt_or_gt_of_ne ha with h2 | h2` into its components or cases.

Rewrite using `[show S j.succ b = 0 from triS (show b < j.succ by`. Rewrite `h2`, the goal using `[Fin.lt_def]`. Simplify using `only [Fin.val_castSucc, Fin.val_succ] at h2 e ⊢`. Use the proof step `omega), mul_zero]`. Rewrite using `[tri _ a h2, zero_mul]`.

Both sides reduce to the same expression. Conclude with `fun h => absurd (Finset.mem_univ _) h`. Introduce `a`. Use `split_ifs with e`. Rewrite using `[e, diag]`.

Conclude with `tri 0 a (Fin.pos_iff_ne_zero.2 e)`.
-/
theorem first_col {K : Type} [CommRing K] {σ : ℕ} (T S : Matrix (Fin (σ + 1)) (Fin (σ + 1)) K) (h : S * T = 1)
    (hl : T (Fin.last σ) (Fin.last σ) = 1) (hu : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → ∀ a b, b ≤ a → T a j * S j' b = 0)
    (hs : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∑ a : Fin (σ + 1), ∑ b : Fin (σ + 1),
      if b.1 = a.1 + 1 then T a j * S j' b else 0) = 1) : ∀ a, T a 0 = if a = 0 then 1 else 0 := by
  have key : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∀ b, j' < b → T b j' = 0) → ∀ a, j ≤ a →
      T a j = if a = j then T j j * S j' j' * T j' j' else 0 := fun j j' e H a ha => by
    have e1 : T a j = ∑ b, T a j * S j' b * T b j' := by
      have := congrFun (congrFun h j') j'
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_one]
    rw [e1, Finset.sum_eq_single j']
    · split_ifs with h1
      · rw [h1]
      · rw [hu j j' e a j' (by rw [Fin.le_def] at *; have := mt Fin.ext h1; omega), zero_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h1 | h1
      · rw [hu j j' e a b (by rw [Fin.le_def, Fin.lt_def] at *; omega), zero_mul]
      · rw [H b h1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  have tri : ∀ j : Fin (σ + 1), ∀ b, j < b → T b j = 0 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact fun b hb => absurd (Fin.le_last b) (not_le.2 hb)
    | cast j ih => exact fun b hb => by rw [key j.castSucc j.succ rfl ih b hb.le, if_neg hb.ne']
  have triS : S.BlockTriangular id := by
    letI := invertibleOfLeftInverse T S h
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.blockTriangular_inv_of_blockTriangular fun a b hab => tri b a hab
  have diag : ∀ j : Fin (σ + 1), T j j = 1 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact hl
    | cast j ih =>
      have h1 := hs j.castSucc j.succ rfl
      rw [Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ, if_pos (show j.succ.1 = j.castSucc.1 + 1 from rfl)] at h1
      · rw [key j.castSucc j.succ rfl (tri _) _ le_rfl, if_pos rfl, h1, ih, one_mul]
      · exact fun b _ hb => if_neg fun e => hb (Fin.ext e)
      · exact fun h => absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with e
        · rcases lt_or_gt_of_ne ha with h2 | h2
          · rw [show S j.succ b = 0 from triS (show b < j.succ by
              rw [Fin.lt_def] at h2 ⊢; simp only [Fin.val_castSucc, Fin.val_succ] at h2 e ⊢; omega), mul_zero]
          · rw [tri _ a h2, zero_mul]
        · rfl
      · exact fun h => absurd (Finset.mem_univ _) h
  intro a
  split_ifs with e
  · rw [e, diag]
  · exact tri 0 a (Fin.pos_iff_ne_zero.2 e)

variable {D : D7} {S S₀ S₀' : HSp D}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `hψ`. Establish `h0 : s - s' ≠ 0` using `sub_ne_zero.2 hne`. Establish `h1` using `h (y * incA D (s - s')⁻¹)`. Establish `e : y * incA D (s - s')⁻¹ * incA D s = y + y * incA D (s - s')⁻¹ * incA D s'`.

Establish `: incA D (s - s')⁻¹ * (incA D s - incA D s') = 1` using `by rw [← map_sub, ← map_mul, inv_mul_cancel₀ h0, map_one]`. Take the linear combination `y * this`. Rewrite `h1` using `[e, psiE_add]`. Establish `h2 : psiE ψ (y * incA D (s - s')⁻¹ * incA D s') * psiE ψ (-(y * incA D (s - s')⁻¹ * incA D s')) = 1`. Rewrite using `[← psiE_add, add_neg_cancel, psiE_zero]`.

Conclude with `hy (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans (one_mul _).symm))`.
-/
theorem eq_of_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∃ s : AE D, psiE ψ s ≠ 1) {s s' : D.host.E}
    (h : ∀ t : AE D, psiE ψ (t * incA D s) = psiE ψ (t * incA D s')) : s = s' := by
  by_contra hne
  obtain ⟨y, hy⟩ := hψ
  have h0 : s - s' ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (y * incA D (s - s')⁻¹)
  have e : y * incA D (s - s')⁻¹ * incA D s = y + y * incA D (s - s')⁻¹ * incA D s' := by
    have : incA D (s - s')⁻¹ * (incA D s - incA D s') = 1 := by rw [← map_sub, ← map_mul, inv_mul_cancel₀ h0, map_one]
    linear_combination y * this
  rw [e, psiE_add] at h1
  have h2 : psiE ψ (y * incA D (s - s')⁻¹ * incA D s') * psiE ψ (-(y * incA D (s - s')⁻¹ * incA D s')) = 1 := by
    rw [← psiE_add, add_neg_cancel, psiE_zero]
  exact hy (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans (one_mul _).symm))

section

variable {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ) {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E}

/- English proof (translation)
Take `⟨k, hk⟩` from `Function.ne_iff.1 hz'`. Use `⟨Matrix.single i k (t * incA D (z' k)⁻¹), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.single_mulVec]`. Express the relevant statement in the definitionally equal form `Function.update (0 : Fin ρ → AE D) i (t * incA D (z' k)⁻¹ * incA D (z' k)) = _`. Rewrite using `[mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one]`.

Both sides reduce to the same expression.
-/
theorem exists_b (hz' : z' ≠ 0) (i : Fin ρ) (t : AE D) : ∃ b : Mx D ρ S₀'.rank, b *ᵥ ratV z' = Pi.single i t := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hz'
  refine ⟨Matrix.single i k (t * incA D (z' k)⁻¹), ?_⟩
  rw [Matrix.single_mulVec]
  change Function.update (0 : Fin ρ → AE D) i (t * incA D (z' k)⁻¹ * incA D (z' k)) = _
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one]
  rfl

/- English proof (translation)
Establish `e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z'` using `(ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))`. Rewrite using `[coefX, ← mulVec_mulVec, ← mulVec_mulVec, e]`.
-/
theorem coefX_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (n : GA D S) :
    coefX d z n = d.pX *ᵥ (mt S n *ᵥ (d'.j0 *ᵥ ratV z')) := by
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  rw [coefX, ← mulVec_mulVec, ← mulVec_mulVec, e]

/- English proof (translation)
Establish `e0 : d.pX *ᵥ (d'.j0 *ᵥ ratV z') = 0`. Use `coefX_eq d d' hz 1` as an intermediate fact. Rewrite `this` using `[GlobalTheory.MixModel.mt_one, one_mulVec, coefX, GlobalTheory.MixModel.mt_one, Matrix.one_mul, d.pX_j0, zero_mulVec]`. Conclude with `this.symm`. Rewrite using `[coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.nB_j0, add_mulVec, mulVec_add, e0, zero_add]`.

Simplify using `only [mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem coefX_nB' (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (b : Mx D ρ S₀'.rank) :
    coefX d z (d'.nB b) = (d.pX ⬝ d'.jX) *ᵥ (b *ᵥ ratV z') := by
  have e0 : d.pX *ᵥ (d'.j0 *ᵥ ratV z') = 0 := by
    have := coefX_eq d d' hz 1
    rw [GlobalTheory.MixModel.mt_one, one_mulVec, coefX, GlobalTheory.MixModel.mt_one, Matrix.one_mul, d.pX_j0, zero_mulVec] at this
    exact this.symm
  rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.nB_j0, add_mulVec, mulVec_add, e0, zero_add]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Apply `rat_injective` to reduce the goal to its premises. Rewrite using `[rat_mul, rat_mul]`. Express the relevant statement in the definitionally equal form `d'.jX = d.jX ⬝ (d.pX ⬝ d'.jX)`. Use extensionality with `k i : 2`. Take `⟨b, hb⟩` from `exists_b hz' i 1`.

Establish `e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z'` using `(ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))`. Take `⟨u, -, b₁, c, hn⟩` from `Decomp.flag_decomp d (hN _ (d'.nB_mem_NFlag b))`. Establish `h1 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ ((u.1 ⬝ b₁) *ᵥ ratV z)`. Rewrite using `[hn, mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, add_mulVec, mulVec_mulVec]`. Establish `h2 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d'.jX *ᵥ Pi.single i 1`.

Rewrite using `[e, mulVec_mulVec, d'.nB_j0, add_mulVec, ← mulVec_mulVec, hb]`. Establish `h3` using `add_left_cancel (h2.symm.trans h1)`. Establish `h4 : (d.jX ⬝ (d.pX ⬝ d'.jX)) *ᵥ Pi.single i 1 = d'.jX *ᵥ Pi.single i 1`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, h3, mulVec_mulVec _ d.pX, d.pX_jX, one_mulVec]`. Use `congrFun h4 k` as an intermediate fact.

Simplify using `only [mulVec_single_one] at this`. Conclude with `this.symm`.
-/
theorem e_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz' : z' ≠ 0) (hN : ∀ n ∈ flagN d', n ∈ flagN d) : d'.e = d.e * (d.qX * d'.e) := by
  apply rat_injective
  rw [rat_mul, rat_mul]
  change d'.jX = d.jX ⬝ (d.pX ⬝ d'.jX)
  ext k i : 2
  obtain ⟨b, hb⟩ := exists_b hz' i 1
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  obtain ⟨u, -, b₁, c, hn⟩ := Decomp.flag_decomp d (hN _ (d'.nB_mem_NFlag b))
  have h1 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ ((u.1 ⬝ b₁) *ᵥ ratV z) := by
    rw [hn, mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, add_mulVec, mulVec_mulVec]
  have h2 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d'.jX *ᵥ Pi.single i 1 := by
    rw [e, mulVec_mulVec, d'.nB_j0, add_mulVec, ← mulVec_mulVec, hb]
  have h3 := add_left_cancel (h2.symm.trans h1)
  have h4 : (d.jX ⬝ (d.pX ⬝ d'.jX)) *ᵥ Pi.single i 1 = d'.jX *ᵥ Pi.single i 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h3, mulVec_mulVec _ d.pX, d.pX_jX, one_mulVec]
  have := congrFun h4 k
  simp only [mulVec_single_one] at this
  exact this.symm

end

/- English proof (translation)
Take `_ | σ` from `ρ`. Conclude with `r.elim0`. Take `rfl : r = 0` from `Fin.ext hr`. Establish `hne` using `GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ`. Establish `e1` using `e_eq d d' hz hz' fun n => (hN n).2`.

Establish `e2` using `e_eq d' d hz.symm hz0 fun n => (hN n).1`. Establish `q1 : d'.qX * d'.e = 1` using `d'.e'e`. Establish `hT : (rat (d.qX * d'.e) : Mx D _ _) = d.pX ⬝ d'.jX` using `rat_mul _ _`. Generalize the expression as in `d.qX * d'.e = T at e1 hT`. Generalize the expression as in `hS : d'.qX * d.e = S' at e2`.

Establish `hST : S' * T = 1` using `by rw [← hS, Matrix.mul_assoc, ← e1, q1]`. Establish `hX : d.jX = d'.jX ⬝ rat S'` using `(congrArg rat e2).trans (rat_mul _ _)`. Establish `hTS : (rat T : Mx D _ _) ⬝ rat S' = 1` using `by rw [← rat_mul, mul_eq_one_comm.1 hST, rat_one]`. Establish `hell : ∀ y : Fin (σ + 1) → AE D, ell D (σ + 1) ⬝ᵥ y = y (Fin.last σ)` using `fun y => by`. Rewrite using `[dotProduct, Finset.sum_eq_single (Fin.last σ)]`.

Simplify using `[ell]`. Introduce `b _ hb`. Rewrite using `[ell, if_neg fun e => hb (Fin.ext (by simpa using e)), zero_mul]`. Conclude with `fun h => absurd (Finset.mem_univ _) h`. Establish `hA : ∀ (j j' : Fin (σ + 1)) (t : AE D), j'.1 = j.1 + 1 → ∃ u ∈ UX D (σ + 1), u.1 = 1 + Matrix.single j j' t ∧ blockX d (d'.levi u) = 1 + Matrix.of fun a b => t * incA D (T a j * S' j' b)` using `fun j j' t e => by`.

Take `⟨u, hu, hu1⟩` from `Decomp.exists_unit (D := D) (T := Matrix.single j j' t) fun a b hab => Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; rw [Fin.le_def] at hab; omega)`. Use `⟨u, hu, hu1, ?_⟩` and prove the remaining obligations. Rewrite using `[blockX, hX, ← Matrix.mul_assoc (mt S _), d'.levi_jX, hu1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS]`. Use `congr 1`. Use extensionality with `a b : 2`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j', Matrix.mul_single_apply_same, Matrix.of_apply, map_mul]`. Express the relevant statement in the definitionally equal form `incA D (T a j) * t * incA D (S' j' b) = _`. Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]`.

Conclude with `fun h => absurd (Finset.mem_univ _) h`. Establish `H` using `first_col T S' hST ?_ ?_ ?_`. Rewrite using `[e1, Matrix.mul_apply]`. Simplify using `only [H, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `eq_of_psiE hne fun t => ?_` and prove the remaining obligations.

Take `⟨b, hb⟩` from `exists_b hz' (Fin.last σ) t`. Establish `h1` using `hc _ ((hN _).2 (d'.nB_mem_NFlag b))`. Establish `h2 : blockX d (d'.nB b) = 1`. Rewrite using `[blockX, hX, ← Matrix.mul_assoc (mt S _), d'.nB_jX, ← hX, d.pX_jX]`. Rewrite `h1` using `[psiBes_nB, psiBes, simpleSum, h2, upSum_one, zero_add, coefX_nB' d d' hz, hb, hell, hell, ← hT, mulVec_single]`.

Simplify using `only [map_one, one_mul, Pi.single_eq_same, mul_one] at h1 ⊢`. Rewrite using `[mul_comm t]`. Conclude with `h1`. Introduce `j j' e a b hab`. Take `⟨u, hu, -, h2⟩` from `hA j j' 1 e`.

Take `⟨u₁, hu₁, b₁, c, hn⟩` from `Decomp.flag_decomp d ((hN _).2 (d'.levi_mem_NFlag hu))`. Rewrite `h2` using `[blockX, hn, Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`. Establish `h3` using `congrFun (congrFun h2 a) b`. Rewrite `h3` using `[Matrix.add_apply, Matrix.of_apply, one_mul]`. Establish `h4 : u₁.1 a b = (1 : Mx D (σ + 1) (σ + 1)) a b`.

Break down `eq_or_lt_of_le hab with rfl | h` into its components or cases. Rewrite using `[(hu₁ b b).2, Matrix.one_apply_eq]`. Rewrite using `[(hu₁ a b).1 h, Matrix.one_apply_ne h.ne']`. Rewrite `h3` using `[h4, left_eq_add]`. Conclude with `incA_injective (h3.trans (map_zero _).symm)`.

Introduce `j j' e`. Use `eq_of_psiE hne fun t => ?_` and prove the remaining obligations. Take `⟨u, hu, h1, h2⟩` from `hA j j' t e`. Establish `h3` using `hc _ ((hN _).2 (d'.levi_mem_NFlag hu))`. Establish `h4 : coefX d z (d'.levi u) = 0`.

Use `coefX_nB' d d' hz 0` as an intermediate fact. Rewrite `this` using `[zero_mulVec, mulVec_zero, coefX_eq d d' hz, d'.nB_zero, GlobalTheory.MixModel.mt_one, one_mulVec]`. Rewrite using `[coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.wittDecomp_levi_inclAnisotropic, this]`. Establish `hadd : ∀ M : Mx D (σ + 1) (σ + 1), upSum (1 + M) = upSum M` using `fun M => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs with h`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega), zero_add]`.

Both sides reduce to the same expression. Establish `h5 : upSum (Matrix.single j j' t : Mx D (σ + 1) (σ + 1)) = t`. Rewrite using `[upSum, Finset.sum_eq_single j, Finset.sum_eq_single j', if_pos e, Matrix.single_apply_same]`. Conclude with `fun b _ hb => if_neg fun e' => hb (Fin.ext (e'.trans e.symm))`. Conclude with `fun h => absurd (Finset.mem_univ _) h`.

Conclude with `fun a _ ha => Finset.sum_eq_zero fun b _ => by`. Rewrite using `[Matrix.single_apply_of_row_ne ha.symm, ite_self]`. Conclude with `fun h => absurd (Finset.mem_univ _) h`. Rewrite `h3` using `[psiBes_levi, psiUni, h1, hadd, h5, psiBes, simpleSum, h2, h4, hadd, dotProduct_zero, add_zero, map_one, one_mul]`. Rewrite using `[map_one, mul_one, ← h3]`.

Use `congr 1`. Simplify using `only [upSum, map_sum, Finset.mul_sum, Matrix.of_apply]`. Apply the tactic sequence `exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp`.
-/
theorem first_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ)
    {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E} (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz0 : z ≠ 0) (hz' : z' ≠ 0)
    (hN : ∀ n, n ∈ flagN d ↔ n ∈ flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n)
    (r : Fin ρ) (hr : r.1 = 0) (k : Fin S.rank) : d'.e k r = d.e k r := by
  obtain _ | σ := ρ
  · exact r.elim0
  obtain rfl : r = 0 := Fin.ext hr
  have hne := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
  have e1 := e_eq d d' hz hz' fun n => (hN n).2
  have e2 := e_eq d' d hz.symm hz0 fun n => (hN n).1
  have q1 : d'.qX * d'.e = 1 := d'.e'e
  have hT : (rat (d.qX * d'.e) : Mx D _ _) = d.pX ⬝ d'.jX := rat_mul _ _
  generalize d.qX * d'.e = T at e1 hT
  generalize hS : d'.qX * d.e = S' at e2
  have hST : S' * T = 1 := by rw [← hS, Matrix.mul_assoc, ← e1, q1]
  have hX : d.jX = d'.jX ⬝ rat S' := (congrArg rat e2).trans (rat_mul _ _)
  have hTS : (rat T : Mx D _ _) ⬝ rat S' = 1 := by rw [← rat_mul, mul_eq_one_comm.1 hST, rat_one]
  have hell : ∀ y : Fin (σ + 1) → AE D, ell D (σ + 1) ⬝ᵥ y = y (Fin.last σ) := fun y => by
    rw [dotProduct, Finset.sum_eq_single (Fin.last σ)]
    · simp [ell]
    · intro b _ hb
      rw [ell, if_neg fun e => hb (Fin.ext (by simpa using e)), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hA : ∀ (j j' : Fin (σ + 1)) (t : AE D), j'.1 = j.1 + 1 → ∃ u ∈ UX D (σ + 1), u.1 = 1 + Matrix.single j j' t ∧
      blockX d (d'.levi u) = 1 + Matrix.of fun a b => t * incA D (T a j * S' j' b) := fun j j' t e => by
    obtain ⟨u, hu, hu1⟩ := Decomp.exists_unit (D := D) (T := Matrix.single j j' t) fun a b hab =>
      Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; rw [Fin.le_def] at hab; omega)
    refine ⟨u, hu, hu1, ?_⟩
    rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.levi_jX, hu1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hT,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS]
    congr 1
    ext a b : 2
    rw [Matrix.mul_apply, Finset.sum_eq_single j', Matrix.mul_single_apply_same, Matrix.of_apply, map_mul]
    · change incA D (T a j) * t * incA D (S' j' b) = _
      ring
    · intro c _ hc
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have H := first_col T S' hST ?_ ?_ ?_
  · rw [e1, Matrix.mul_apply]
    simp only [H, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine eq_of_psiE hne fun t => ?_
    obtain ⟨b, hb⟩ := exists_b hz' (Fin.last σ) t
    have h1 := hc _ ((hN _).2 (d'.nB_mem_NFlag b))
    have h2 : blockX d (d'.nB b) = 1 := by
      rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.nB_jX, ← hX, d.pX_jX]
    rw [psiBes_nB, psiBes, simpleSum, h2, upSum_one, zero_add, coefX_nB' d d' hz, hb, hell, hell, ← hT, mulVec_single] at h1
    simp only [map_one, one_mul, Pi.single_eq_same, mul_one] at h1 ⊢
    rw [mul_comm t]
    exact h1
  · intro j j' e a b hab
    obtain ⟨u, hu, -, h2⟩ := hA j j' 1 e
    obtain ⟨u₁, hu₁, b₁, c, hn⟩ := Decomp.flag_decomp d ((hN _).2 (d'.levi_mem_NFlag hu))
    rw [blockX, hn, Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h2
    have h3 := congrFun (congrFun h2 a) b
    rw [Matrix.add_apply, Matrix.of_apply, one_mul] at h3
    have h4 : u₁.1 a b = (1 : Mx D (σ + 1) (σ + 1)) a b := by
      rcases eq_or_lt_of_le hab with rfl | h
      · rw [(hu₁ b b).2, Matrix.one_apply_eq]
      · rw [(hu₁ a b).1 h, Matrix.one_apply_ne h.ne']
    rw [h4, left_eq_add] at h3
    exact incA_injective (h3.trans (map_zero _).symm)
  · intro j j' e
    refine eq_of_psiE hne fun t => ?_
    obtain ⟨u, hu, h1, h2⟩ := hA j j' t e
    have h3 := hc _ ((hN _).2 (d'.levi_mem_NFlag hu))
    have h4 : coefX d z (d'.levi u) = 0 := by
      have := coefX_nB' d d' hz 0
      rw [zero_mulVec, mulVec_zero, coefX_eq d d' hz, d'.nB_zero, GlobalTheory.MixModel.mt_one, one_mulVec] at this
      rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.wittDecomp_levi_inclAnisotropic, this]
    have hadd : ∀ M : Mx D (σ + 1) (σ + 1), upSum (1 + M) = upSum M := fun M =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        split_ifs with h
        · rw [Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega), zero_add]
        · rfl
    have h5 : upSum (Matrix.single j j' t : Mx D (σ + 1) (σ + 1)) = t := by
      rw [upSum, Finset.sum_eq_single j, Finset.sum_eq_single j', if_pos e, Matrix.single_apply_same]
      · exact fun b _ hb => if_neg fun e' => hb (Fin.ext (e'.trans e.symm))
      · exact fun h => absurd (Finset.mem_univ _) h
      · exact fun a _ ha => Finset.sum_eq_zero fun b _ => by
          rw [Matrix.single_apply_of_row_ne ha.symm, ite_self]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [psiBes_levi, psiUni, h1, hadd, h5, psiBes, simpleSum, h2, h4, hadd, dotProduct_zero, add_zero, map_one, one_mul] at h3
    rw [map_one, mul_one, ← h3]
    congr 1
    simp only [upSum, map_sum, Finset.mul_sum, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

end GlobalTheory.FirstVec

end
