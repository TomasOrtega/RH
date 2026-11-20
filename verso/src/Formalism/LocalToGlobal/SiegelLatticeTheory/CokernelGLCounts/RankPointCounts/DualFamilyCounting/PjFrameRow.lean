import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf

section Gen

variable {r k : ℕ}

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Simplify using `[Qm, colQ]`.
-/
theorem Qm_mulVec_sum (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) (t : Fin (2 * r + k + 1) → ℂ) :
    Qm e f wf z0 *ᵥ t = ∑ j, t j • colQ e f wf z0 j := by
  ext i
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm]
  simp [Qm, colQ]

/- English proof (translation)
Simplify using `[GBasic.sgn, wI]`.
-/
theorem sgn_wI_last : GBasic.sgn k r (wI k r (Fin.last k)) = -1 := by
  simp [GBasic.sgn, wI]

/- English proof (translation)
Establish `h1 : y = Qm e f wf z0 *ᵥ (Qi ε e f wf z0 *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Qm_mul_Qi hF, Matrix.one_mulVec]`. Rewrite `h1` using `[Qm_mulVec_sum]`. Use `conv_lhs => rw [h1]`. Establish `hzero : ∀ j, (∀ c : Fin (k + 1), j ≠ wI k r c) → (Qi ε e f wf z0 *ᵥ y) j • colQ e f wf z0 j = 0`.

Introduce `j hj`. Break down `idx_cases j with ⟨a, rfl⟩ | ⟨c, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[Qi_mulVec_eI, hyf, zero_smul]`. Conclude with `absurd rfl (hj c)`. Rewrite using `[Qi_mulVec, sig_esI_eq, colQ_eI, hye, mul_zero, zero_smul]`.

Establish `hinj : Function.Injective (wI k r)` using `fun a b h => Fin.ext (by`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[wI] at this`. Conclude with `this)`. Use `set F : Fin (2 * r + k + 1) → (Fin (2 * r + k + 1) → ℂ) := fun j => (Qi ε e f wf z0 *ᵥ y) j • colQ e f wf z0 j with hFdef`.

Establish `hsum : ∑ j, F j = ∑ c : Fin (k + 1), F (wI k r c)`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (wI k r))) (fun j _ hj => hzero j (fun c hc => hj (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc.symm⟩)))]`. Conclude with `Finset.sum_image (fun a _ b _ h => hinj h)`. Use `show ∑ j, F j = _`. Rewrite using `[hsum, Fin.sum_univ_castSucc, sub_eq_add_neg]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hc : (Fin.castSucc c).val < k` using `c.isLt`. Simplify using `only [hFdef]`. Rewrite using `[Qi_mulVec, sig_wI_eq, sgn_wI _ hc, one_mul, colQ_wI _ _ _ _ _ hc]`.

Both sides reduce to the same expression. Simplify using `only [hFdef]`. Rewrite using `[Qi_mulVec, sig_wI_eq, sgn_wI_last, colQ_wI_last _ _ _ _ _ (by simp), neg_one_mul, neg_smul]`.
-/
theorem decomp0 {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (y : Fin (2 * r + k + 1) → ℂ) (hye : ∀ a, hJ ε (e a) y = 0) (hyf : ∀ a, hJ ε (f a) y = 0) :
    y = ∑ c, hJ ε (wf c) y • wf c - hJ ε z0 y • z0 := by
  have h1 : y = Qm e f wf z0 *ᵥ (Qi ε e f wf z0 *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Qm_mul_Qi hF, Matrix.one_mulVec]
  rw [Qm_mulVec_sum] at h1
  conv_lhs => rw [h1]

  have hzero : ∀ j, (∀ c : Fin (k + 1), j ≠ wI k r c) →
      (Qi ε e f wf z0 *ᵥ y) j • colQ e f wf z0 j = 0 := by
    intro j hj
    rcases idx_cases j with ⟨a, rfl⟩ | ⟨c, rfl⟩ | ⟨a, rfl⟩
    · rw [Qi_mulVec_eI, hyf, zero_smul]
    · exact absurd rfl (hj c)
    · rw [Qi_mulVec, sig_esI_eq, colQ_eI, hye, mul_zero, zero_smul]
  have hinj : Function.Injective (wI k r) := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp [wI] at this; exact this)
  set F : Fin (2 * r + k + 1) → (Fin (2 * r + k + 1) → ℂ) := fun j => (Qi ε e f wf z0 *ᵥ y) j • colQ e f wf z0 j
    with hFdef
  have hsum : ∑ j, F j = ∑ c : Fin (k + 1), F (wI k r c) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (wI k r))) (fun j _ hj => hzero j (fun c hc =>
      hj (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc.symm⟩)))]
    exact Finset.sum_image (fun a _ b _ h => hinj h)
  show ∑ j, F j = _
  rw [hsum, Fin.sum_univ_castSucc, sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    have hc : (Fin.castSucc c).val < k := c.isLt
    simp only [hFdef]
    rw [Qi_mulVec, sig_wI_eq, sgn_wI _ hc, one_mul, colQ_wI _ _ _ _ _ hc]
    rfl
  · simp only [hFdef]
    rw [Qi_mulVec, sig_wI_eq, sgn_wI_last, colQ_wI_last _ _ _ _ _ (by simp), neg_one_mul, neg_smul]

end Gen

end Formalism.L2.SG.Pf.NcReal.JX.FR

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Unfold `hJ`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
theorem fr_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem fr_smul_r (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem fr_smul_l (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hJ]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fr_add_r, ih]`.
-/
theorem fr_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fr_add_r, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hJ]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ← ih]`. Simplify using `[hJ, add_dotProduct]`.
-/
theorem fr_sum_l {ι : Type*} (s : Finset ι) (y : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε (∑ i ∈ s, f i) y = ∑ i ∈ s, hJ ε (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [hJ, add_dotProduct]

end Lin

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hF` using `isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw`. Establish `h` using `decomp0 hF y hye hyf`. Use `conv_lhs => rw [h]`. Rewrite using `[sub_eq_add_neg]`.

Use `congr 1`. Unfold `z0v`. Rewrite using `[fr_smul_l, smul_smul, ← neg_smul]`. Use `congr 1`. Establish `hs : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) = ((T : ℂ))⁻¹`.

Rewrite using `[← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hT.le, Complex.ofReal_inv]`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decomp {n r k : ℕ} (hn : n = 2 * r + k + 1) {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
    {wf : Fin k → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) (y : Fin n → ℂ) (hye : ∀ a, hJ ε (e a) y = 0) (hyf : ∀ a, hJ ε (f a) y = 0) :
    y = ∑ c, hJ ε (wf c) y • wf c + (-(hJ ε z y) / (T : ℂ)) • z := by
  subst hn
  have hF := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have h := decomp0 hF y hye hyf
  conv_lhs => rw [h]
  rw [sub_eq_add_neg]
  congr 1
  unfold z0v
  rw [fr_smul_l, smul_smul, ← neg_smul]
  congr 1
  have hs : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) = ((T : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hT.le, Complex.ofReal_inv]
  rw [Complex.star_def, Complex.conj_ofReal]
  calc -((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε z y * (((Real.sqrt T)⁻¹ : ℝ) : ℂ))
      = -(hJ ε z y * ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * (((Real.sqrt T)⁻¹ : ℝ) : ℂ))) := by ring
    _ = -hJ ε z y / (T : ℂ) := by rw [hs]; ring

end Formalism.L2.SG.Pf.NcReal.JX.FR

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HidaSetting

variable {D : D7} (X : HidaSetting D)

def sv (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) : Fin (D.R.k + 1) → Fin X.B.I.n → ℂ :=
  Fin.snoc (α := fun _ => Fin X.B.I.n → ℂ) (X.wfr u v) (ProductExactness.zV X u v)

/- English proof (translation)
Simplify using `[sv]`.
-/
theorem sv_cs (u v) (c : Fin D.R.k) : sv X u v (Fin.castSucc c) = X.wfr u v c := by
  simp [sv]
/- English proof (translation)
Simplify using `[sv]`.
-/
theorem sv_last (u v) : sv X u v (Fin.last D.R.k) = ProductExactness.zV X u v := by
  simp [sv]

/- English proof (translation)
Proceed by induction on `c using Fin.lastCases with`. Consider the case `last => rw [sv_last]`. Conclude with `fX_ez X u v a`. Consider the case `cast c => rw [sv_cs]`. Conclude with `fX_ew X u v a c`.
-/
theorem sv_perp_e (u v) (a : Fin D.R.rS) (c : Fin (D.R.k + 1)) : hJ (X.B.I.ε v) (eV X v a) (sv X u v c) = 0 := by
  induction c using Fin.lastCases with
  | last => rw [sv_last]; exact fX_ez X u v a
  | cast c => rw [sv_cs]; exact fX_ew X u v a c

/- English proof (translation)
Proceed by induction on `c using Fin.lastCases with`. Consider the case `last => rw [sv_last]`. Conclude with `fX_fz X u v a`. Consider the case `cast c => rw [sv_cs]`. Conclude with `fX_fw X u v a c`.
-/
theorem sv_perp_f (u v) (a : Fin D.R.rS) (c : Fin (D.R.k + 1)) :
    hJ (X.B.I.ε v) (ProductExactness.pV X v a) (sv X u v c) = 0 := by
  induction c using Fin.lastCases with
  | last => rw [sv_last]; exact fX_fz X u v a
  | cast c => rw [sv_cs]; exact fX_fw X u v a c

def Mco (u w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ :=
  fun c' c => Fin.snoc (α := fun _ => ℂ) (fun c'' => hJ (X.B.I.ε v) (X.wfr u v c'') (sv X w v c))
    (-(hJ (X.B.I.ε v) (ProductExactness.zV X u v) (sv X w v c)) / ((Tw u : ℝ) : ℂ)) c'

/- English proof (translation)
Establish `h` using `decomp (nX X) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (sv X w v c) (sv_perp_e X w v · c) (sv_perp_f X w v · c)`. Use `conv_lhs => rw [h]`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[Mco, sv_cs, sv_last]`.
-/
theorem sv_decomp (u w v) (c : Fin (D.R.k + 1)) : sv X w v c = ∑ c', Mco X u w v c' c • sv X u v c' := by
  have h := decomp (nX X) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (sv X w v c) (sv_perp_e X w v · c)
    (sv_perp_f X w v · c)
  conv_lhs => rw [h]
  rw [Fin.sum_univ_castSucc]
  simp [Mco, sv_cs, sv_last]

end HidaSetting

end Formalism.L2.SG.Pf.NcReal.JX.FR

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HidaSetting

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Rewrite using `[sv_decomp X u w v c, Matrix.mulVec_sum, fr_sum_r]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, fr_smul_r, mul_comm]`.
-/
theorem row_w (u w v) (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (x : Fin X.B.I.n → ℂ) (c : Fin (D.R.k + 1)) :
    hJ (X.B.I.ε v) x (g *ᵥ sv X w v c) = ∑ c', hJ (X.B.I.ε v) x (g *ᵥ sv X u v c') * Mco X u w v c' c := by
  rw [sv_decomp X u w v c, Matrix.mulVec_sum, fr_sum_r]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Matrix.mulVec_smul, fr_smul_r, mul_comm]

def Gu (u : D.what₂.Word) : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ :=
  Matrix.diagonal (Fin.snoc (α := fun _ => ℂ) (fun _ => 1) (-((Tw u : ℝ) : ℂ)))

/- English proof (translation)
Unfold `Gu`. Rewrite using `[Matrix.diagonal_apply]`. Proceed by induction on `c using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `d using Fin.lastCases with`.

Consider the case `last => rw [sv_last, frame_real_z_z_eq_neg, if_pos rfl, Fin.snoc_last]`. Consider the case `cast d`. Rewrite using `[sv_last, sv_cs, fX_zw, if_neg (fun h => Fin.castSucc_ne_last d h.symm)]`. Consider the case `cast c`. Proceed by induction on `d using Fin.lastCases with`.

Consider the case `last`. Rewrite using `[sv_last, sv_cs, hJ_swap, fX_zw, star_zero, if_neg (Fin.castSucc_ne_last c)]`. Consider the case `cast d`. Rewrite using `[sv_cs, sv_cs, fX_ww]`. Distinguish the cases in `h : c = d`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun h' => h (Fin.castSucc_injective _ h'))]`.
-/
theorem gram_sv (u v) (c d : Fin (D.R.k + 1)) : hJ (X.B.I.ε v) (sv X u v c) (sv X u v d) = Gu u c d := by
  unfold Gu
  rw [Matrix.diagonal_apply]
  induction c using Fin.lastCases with
  | last =>
    induction d using Fin.lastCases with
    | last => rw [sv_last, frame_real_z_z_eq_neg, if_pos rfl, Fin.snoc_last]
    | cast d =>
      rw [sv_last, sv_cs, fX_zw, if_neg (fun h => Fin.castSucc_ne_last d h.symm)]
  | cast c =>
    induction d using Fin.lastCases with
    | last =>
      rw [sv_last, sv_cs, hJ_swap, fX_zw, star_zero, if_neg (Fin.castSucc_ne_last c)]
    | cast d =>
      rw [sv_cs, sv_cs, fX_ww]
      by_cases h : c = d
      · subst h; simp
      · rw [if_neg h, if_neg (fun h' => h (Fin.castSucc_injective _ h'))]

/- English proof (translation)
Use extensionality with `c d`. Rewrite using `[← gram_sv X w v c d, sv_decomp X u w v c, sv_decomp X u w v d, fr_sum_l]`. Repeatedly rewrite using `[fr_smul_l, fr_sum_r, fr_smul_r, gram_sv X u v]`. Rewrite using `[Matrix.mul_apply]`. Repeatedly rewrite using `[Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_M (u w v) : (Mco X u w v)ᴴ * Gu u * Mco X u w v = Gu w := by
  ext c d
  rw [← gram_sv X w v c d, sv_decomp X u w v c, sv_decomp X u w v d, fr_sum_l]
  simp_rw [fr_smul_l, fr_sum_r, fr_smul_r, gram_sv X u v]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun c' _ => ?_
  ring

/- English proof (translation)
Simplify using `[Gu, Matrix.det_diagonal, Fin.prod_univ_castSucc]`.
-/
theorem det_Gu (u : D.what₂.Word) : (Gu (D := D) u).det = -((Tw u : ℝ) : ℂ) := by
  simp [Gu, Matrix.det_diagonal, Fin.prod_univ_castSucc]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (gram_M X u w v)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, det_Gu, det_Gu]`. Establish `hT : (0 : ℝ) < Tw u` using `ProductExactness.Tw_pos u`. Establish `e : (Complex.normSq (Mco X u w v).det : ℂ) = star (Mco X u w v).det * (Mco X u w v).det`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Both sides reduce to the same expression. Establish `h2 : (Complex.normSq (Mco X u w v).det : ℂ) * (Tw u : ℂ) = (Tw w : ℂ)`. Rewrite using `[e]`. Take the linear combination `(-1 : ℂ) * h`. Establish `h3 : Complex.normSq (Mco X u w v).det * Tw u = Tw w` using `by exact_mod_cast h2`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem normSq_det_M (u w v) : Complex.normSq (Mco X u w v).det = Tw w / Tw u := by
  have h := congrArg Matrix.det (gram_M X u w v)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, det_Gu, det_Gu] at h
  have hT : (0 : ℝ) < Tw u := ProductExactness.Tw_pos u
  have e : (Complex.normSq (Mco X u w v).det : ℂ) = star (Mco X u w v).det * (Mco X u w v).det := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have h2 : (Complex.normSq (Mco X u w v).det : ℂ) * (Tw u : ℂ) = (Tw w : ℂ) := by
    rw [e]; linear_combination (-1 : ℂ) * h
  have h3 : Complex.normSq (Mco X u w v).det * Tw u = Tw w := by exact_mod_cast h2
  field_simp
  linarith

end HidaSetting

end Formalism.L2.SG.Pf.NcReal.JX.FR

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.LsNc5

section Lin2

variable (r k : ℕ)

abbrev Aidx : Type := (LtPair r × Bool) ⊕ ((LtPair r × Bool) ⊕ Fin r)

def embA : Aidx r → CIdx r k
  | Sum.inl p => Sum.inl (Sum.inl p)
  | Sum.inr q => Sum.inr (Sum.inr q)

variable {r k}

def rowOf (κ : CIdx r k → ℝ) : Fin r → Fin (k + 1) → ℂ := fun b =>
  Fin.snoc (α := fun _ => ℂ) (fun j => (⟨κ (Sum.inr (Sum.inl (b, j, false))), κ (Sum.inr (Sum.inl (b, j, true)))⟩ : ℂ))
    (⟨κ (Sum.inl (Sum.inr (b, false))), κ (Sum.inl (Sum.inr (b, true)))⟩ : ℂ)

def assemble (κA : Aidx r → ℝ) (R : Fin r → Fin (k + 1) → ℂ) : CIdx r k → ℝ
  | Sum.inl (Sum.inl p) => κA (Sum.inl p)
  | Sum.inl (Sum.inr (b, t)) => reim (R b (Fin.last k)) t
  | Sum.inr (Sum.inl (b, j, t)) => reim (R b (Fin.castSucc j)) t
  | Sum.inr (Sum.inr q) => κA (Sum.inr q)

/- English proof (translation)
Apply the tactic sequence `cases t <;> simp [reim]`.
-/
theorem reim_mk (x y : ℝ) (t : Bool) : reim (⟨x, y⟩ : ℂ) t = if t then y else x := by
  cases t <;> simp [reim]

def Psi (r k : ℕ) : (CIdx r k → ℝ) ≃ₗ[ℝ] (Aidx r → ℝ) × (Fin r → Fin (k + 1) → ℂ) where
  toFun κ := (fun a => κ (embA r k a), rowOf κ)
  invFun p := assemble p.1 p.2
  map_add' κ κ' := by
    refine Prod.ext rfl ?_
    funext b c
    induction c using Fin.lastCases <;> simp [rowOf] <;> apply Complex.ext <;> simp
  map_smul' s κ := by
    refine Prod.ext rfl ?_
    funext b c
    induction c using Fin.lastCases <;> simp [rowOf] <;> apply Complex.ext <;> simp
  left_inv κ := by
    funext i
    rcases i with ((p | ⟨b, t⟩) | (⟨b, j, t⟩ | q))
    · rfl
    · simp only [assemble, rowOf, Fin.snoc_last, reim_mk]; cases t <;> rfl
    · simp only [assemble, rowOf, Fin.snoc_castSucc, reim_mk]; cases t <;> rfl
    · rfl
  right_inv p := by
    obtain ⟨κA, R⟩ := p
    refine Prod.ext ?_ ?_
    · funext a; rcases a with p | q <;> rfl
    · funext b c
      induction c using Fin.lastCases with
      | last => simp only [rowOf, Fin.snoc_last, assemble]; apply Complex.ext <;> simp [reim]
      | cast j => simp only [rowOf, Fin.snoc_castSucc, assemble]; apply Complex.ext <;> simp [reim]

def Fc (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (Fin r → Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin r → Fin (k + 1) → ℂ) :=
  LinearMap.pi fun b => (Matrix.vecMulLinear M) ∘ₗ LinearMap.proj b

def Lmap (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (CIdx r k → ℝ) →ₗ[ℝ] (CIdx r k → ℝ) :=
  (Psi r k).symm.toLinearMap ∘ₗ (LinearMap.prodMap LinearMap.id ((Fc (r := r) M).restrictScalars ℝ)) ∘ₗ
    (Psi r k).toLinearMap

/- English proof (translation)
Establish `h : Matrix.vecMulLinear M = Matrix.toLin' Mᵀ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]`.

Rewrite using `[h, LinearMap.det_toLin', Matrix.det_transpose]`.
-/
theorem det_vecMulLinear (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : LinearMap.det (Matrix.vecMulLinear M) = M.det := by
  have h : Matrix.vecMulLinear M = Matrix.toLin' Mᵀ := by
    apply LinearMap.ext
    intro v
    funext i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [h, LinearMap.det_toLin', Matrix.det_transpose]

/- English proof (translation)
Use `show LinearMap.det ((Psi r k).symm.toLinearMap ∘ₗ (LinearMap.prodMap LinearMap.id ((Fc (r := r) M).restrictScalars ℝ)) ∘ₗ (Psi r k).symm.symm.toLinearMap) = _`. Rewrite using `[LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Fc, LinearMap.det_pi]`. Simplify using `[det_vecMulLinear, Finset.prod_const, map_pow]`.
-/
theorem det_Lmap (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    LinearMap.det (Lmap (r := r) M) = Complex.normSq M.det ^ r := by
  show LinearMap.det ((Psi r k).symm.toLinearMap ∘ₗ
      (LinearMap.prodMap LinearMap.id ((Fc (r := r) M).restrictScalars ℝ)) ∘ₗ (Psi r k).symm.symm.toLinearMap) = _
  rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Fc, LinearMap.det_pi]
  simp [det_vecMulLinear, Finset.prod_const, map_pow]

end Lin2

end Formalism.L2.SG.Pf.NcReal.JX.FR

namespace Formalism.L2.SG.Pf.NcReal.JX.FR

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Proceed by induction on `c using Fin.lastCases with`. Consider the case `last`. Simplify using `only [rowOf, Fin.snoc_last, kapV]`. Rewrite using `[sv_last]`. Apply the tactic sequence `apply Complex.ext <;> simp [reim, yVec] <;> rfl`.

Consider the case `cast j`. Simplify using `only [rowOf, Fin.snoc_castSucc, kapV]`. Rewrite using `[sv_cs]`. Apply the tactic sequence `apply Complex.ext <;> simp [reim, phiMat]`.
-/
theorem rowOf_kapV (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) (s : X.B.I.Ginf) (b : Fin D.R.rS)
    (c : Fin (D.R.k + 1)) :
    rowOf (fun i => kapV X u v s i) b c = hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (s v) *ᵥ sv X u v c) := by
  induction c using Fin.lastCases with
  | last =>
    simp only [rowOf, Fin.snoc_last, kapV]
    rw [sv_last]
    apply Complex.ext <;> simp [reim, yVec] <;> rfl
  | cast j =>
    simp only [rowOf, Fin.snoc_castSucc, kapV]
    rw [sv_cs]
    apply Complex.ext <;> simp [reim, phiMat]

/- English proof (translation)
Apply the tactic sequence `rcases a with ⟨p, t⟩ | (⟨p, t⟩ | q) <;> simp only [embA, kapV]`.
-/
theorem kapV_A (u w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) (s : X.B.I.Ginf) (a : Aidx D.R.rS) :
    kapV X w v s (embA D.R.rS D.R.k a) = kapV X u v s (embA D.R.rS D.R.k a) := by
  rcases a with ⟨p, t⟩ | (⟨p, t⟩ | q) <;> simp only [embA, kapV]

/- English proof (translation)
Introduce `D X u w v`. Use `⟨Lmap (r := D.R.rS) (k := D.R.k) (Mco X u w v), fun s => ?_, ?_⟩` and prove the remaining obligations. Apply `(Psi D.R.rS D.R.k).injective` to reduce the goal to its premises. Establish `hL : ∀ κ, Psi D.R.rS D.R.k (Lmap (r` using `D.R.rS) (Mco X u w v) κ) = (LinearMap.prodMap LinearMap.id ((Fc (r := D.R.rS) (Mco X u w v)).restrictScalars ℝ)) (Psi D.R.rS D.R.k κ) := by`. Introduce `κ`.

Simplify using `only [Lmap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]`. Rewrite using `[hL]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a show kapV X w v s (embA D.R.rS D.R.k a) = kapV X u v s (embA D.R.rS D.R.k a)`. Conclude with `kapV_A X u w v s a`.

Use function extensionality and compare the values at `b c show rowOf (fun i => kapV X w v s i) b c = (rowOf (fun i => kapV X u v s i) b ᵥ* Mco X u w v) c`. Rewrite using `[rowOf_kapV, row_w X u w v (uMat (s v)) (LsNc5.fV X v b) c, Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[rowOf_kapV]`. Rewrite using `[det_Lmap, normSq_det_M, abs_of_nonneg]`.

Establish `hu : (0 : ℝ) < Tw u` using `ProductExactness.Tw_pos u`. Establish `hw : (0 : ℝ) < Tw w` using `ProductExactness.Tw_pos w`. Check the signs of the components of the expression.
-/
theorem frameRow_holds : FrameRow := by
  intro D X u w v
  refine ⟨Lmap (r := D.R.rS) (k := D.R.k) (Mco X u w v), fun s => ?_, ?_⟩
  · apply (Psi D.R.rS D.R.k).injective
    have hL : ∀ κ, Psi D.R.rS D.R.k (Lmap (r := D.R.rS) (Mco X u w v) κ) =
        (LinearMap.prodMap LinearMap.id ((Fc (r := D.R.rS) (Mco X u w v)).restrictScalars ℝ)) (Psi D.R.rS D.R.k κ) := by
      intro κ
      simp only [Lmap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply]
    rw [hL]
    refine Prod.ext ?_ ?_
    · funext a
      show kapV X w v s (embA D.R.rS D.R.k a) = kapV X u v s (embA D.R.rS D.R.k a)
      exact kapV_A X u w v s a
    · funext b c
      show rowOf (fun i => kapV X w v s i) b c = (rowOf (fun i => kapV X u v s i) b ᵥ* Mco X u w v) c
      rw [rowOf_kapV, row_w X u w v (uMat (s v)) (LsNc5.fV X v b) c, Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [rowOf_kapV]
  · rw [det_Lmap, normSq_det_M, abs_of_nonneg]
    have hu : (0 : ℝ) < Tw u := ProductExactness.Tw_pos u
    have hw : (0 : ℝ) < Tw w := ProductExactness.Tw_pos w
    positivity

end Final

end Formalism.L2.SG.Pf.NcReal.JX.FR
