import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `[Matrix.updateRow_apply, Fin.castSucc_ne_last]`. Introduce `i j hij`. Establish `hij' : i < j` using `hij`.

Establish `hi : i ≠ Fin.last n` using `ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))`. Rewrite using `[Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]`.
-/
theorem det_updateRow_one_last {n : ℕ} (v : Fin (n + 1) → k) :
    (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) v).det = v (Fin.last n) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [Matrix.updateRow_apply, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]

/- English proof (translation)
Take `⟨m, hm⟩` from `Function.ne_iff.mp hw`. Establish `hm' : w m ≠ 0` using `by simpa using hm`. Establish `hM : ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))).det ≠ 0`. Rewrite using `[Matrix.det_permute', det_updateRow_one_last, Equiv.swap_apply_right]`. Use `mul_ne_zero ?_ hm'` and prove the remaining obligations.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap m (Fin.last n))) with h | h <;> simp [h]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩` and prove the remaining obligations. Use `show ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))) (Fin.last n) j = w j`. Simplify using `[Matrix.submatrix_apply, Matrix.updateRow_self, Equiv.swap_apply_self]`.
-/
theorem exists_last_row {n : ℕ} (w : Fin (n + 1) → k) (hw : w ≠ 0) :
    ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hw
  have hm' : w m ≠ 0 := by simpa using hm
  have hM : ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))).det ≠ 0 := by
    rw [Matrix.det_permute', det_updateRow_one_last, Equiv.swap_apply_right]
    refine mul_ne_zero ?_ hm'
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap m (Fin.last n))) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))) (Fin.last n) j = w j
  simp [Matrix.submatrix_apply, Matrix.updateRow_self, Equiv.swap_apply_self]

/- English proof (translation)
Introduce `n w hw j`. Establish `h` using `exists_last_row w hw`. Unfold `sec`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec j`.
-/
theorem secSpec : SecSpec k := by
  intro n w hw j
  have h := exists_last_row w hw
  unfold sec
  rw [dif_pos h]
  exact h.choose_spec j

/- English proof (translation)
Simplify using `only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]`.
-/
theorem cj_mul {n : ℕ} (a b : GL (Fin (n + 1)) k) (x : Mx k n) : cj (a * b) x = cj a (cj b x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[cj]`.
-/
theorem cj_one {n : ℕ} (x : Mx k n) : cj (1 : GL (Fin (n + 1)) k) x = x := by
  simp [cj]

def cjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by rw [← cj_mul, inv_mul_cancel, cj_one]
  right_inv x := by rw [← cj_mul, mul_inv_cancel, cj_one]
  continuous_toFun := by unfold cj; fun_prop
  continuous_invFun := by unfold cj; fun_prop

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsLocallyConstant F ∧ HasCompactSupport F at hF`. Establish `hι : Topology.IsClosedEmbedding (fun y : Mx k n => (y, w))`. Use `⟨isEmbedding_prodMkLeft w, ?_⟩` and prove the remaining obligations. Establish `hr : Set.range (fun y : Mx k n => (y, w)) = Set.univ ×ˢ {w}`. Use extensionality with `⟨a, b⟩`.

Simplify using `[eq_comm]`. Rewrite using `[hr]`. Conclude with `isClosed_univ.prod isClosed_singleton`. Establish `hemb` using `hι.comp (cjHomeo g).isClosedEmbedding`. Conclude with `⟨hF.1.comp_continuous hemb.continuous, hF.2.comp_isClosedEmbedding hemb⟩`.
-/
theorem slice_cj_mem {n : ℕ} {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) (g : GL (Fin (n + 1)) k)
    (w : Vc k n) : (fun x => F (cj g x, w)) ∈ SB (Mx k n) := by
  change IsLocallyConstant F ∧ HasCompactSupport F at hF
  have hι : Topology.IsClosedEmbedding (fun y : Mx k n => (y, w)) := by
    refine ⟨isEmbedding_prodMkLeft w, ?_⟩
    have hr : Set.range (fun y : Mx k n => (y, w)) = Set.univ ×ˢ {w} := by
      ext ⟨a, b⟩
      simp [eq_comm]
    rw [hr]
    exact isClosed_univ.prod isClosed_singleton
  have hemb := hι.comp (cjHomeo g).isClosedEmbedding
  exact ⟨hF.1.comp_continuous hemb.continuous, hF.2.comp_isClosedEmbedding hemb⟩

/- English proof (translation)
Introduce `n Λ hΛ F hF w hw s hs`. Unfold `phi`. Rewrite using `[if_neg hw]`. Establish `hrow : ∀ (g : GL (Fin (n + 1)) k) (j : Fin (n + 1)), (eLast k n ᵥ* (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) j = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j`. Introduce `g j`.

Simplify using `[eLast, Matrix.vecMul, dotProduct, Pi.single_apply]`. Establish `ht : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j` using `secSpec n w hw`. Establish `e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n ᵥ* (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k)`. Use function extensionality and compare the values at `j`. Rewrite using `[hrow, hrow, ht, hs]`.

Establish `hp : sec w * s⁻¹ ∈ Mir k n`. Express the relevant statement in the definitionally equal form `eLast k n ᵥ* ((sec w * s⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n`. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]`. Establish `hf : (fun x => F (cj (sec w)⁻¹ x, w)) ∈ SB (Mx k n)` using `slice_cj_mem hF (sec w)⁻¹ w`. Rewrite using `[← hΛ _ hp _ hf]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp]`. Rewrite using `[← cj_mul, inv_mul_cancel_left]`.
-/
theorem phiIndep : PhiIndep k := by
  intro n Λ hΛ F hF w hw s hs
  unfold phi
  rw [if_neg hw]
  have hrow : ∀ (g : GL (Fin (n + 1)) k) (j : Fin (n + 1)),
      (eLast k n ᵥ* (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) j = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    intro g j
    simp [eLast, Matrix.vecMul, dotProduct, Pi.single_apply]
  have ht : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j :=
    secSpec n w hw
  have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      = eLast k n ᵥ* (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    funext j
    rw [hrow, hrow, ht, hs]
  have hp : sec w * s⁻¹ ∈ Mir k n := by
    change eLast k n ᵥ* ((sec w * s⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have hf : (fun x => F (cj (sec w)⁻¹ x, w)) ∈ SB (Mx k n) := slice_cj_mem hF (sec w)⁻¹ w
  rw [← hΛ _ hp _ hf]
  congr 1
  funext x
  simp only [Function.comp]
  rw [← cj_mul, inv_mul_cancel_left]

/- English proof (translation)
Introduce `n Λ F _ G _ a b`. Use function extensionality and compare the values at `w`. Unfold `phi`. Simplify using `only [Pi.add_apply, Pi.smul_apply]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[← map_smul, ← map_smul, ← map_add]`. Use `congr 1`.
-/
theorem phiLin : PhiLin k := by
  intro n Λ F _ G _ a b
  funext w
  unfold phi
  simp only [Pi.add_apply, Pi.smul_apply]
  split_ifs
  · simp
  · rw [← map_smul, ← map_smul, ← map_add]
    congr 1

/- English proof (translation)
Introduce `n Λ hΛ F hF h w`. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Simplify using `[phi, Matrix.mulVec_zero]`. Establish `hw' : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w ≠ 0`.

Introduce `h0`. Apply `hw` to reduce the goal to its premises. Establish `e : ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) = w`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]`. Rewrite using `[← e, h0, Matrix.mulVec_zero]`.

Rewrite using `[phiIndep n Λ hΛ F hF _ hw' (sec w * h) ?_]`. Unfold `phi`. Rewrite using `[if_neg hw]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only`. Rewrite using `[← cj_mul, _root_.mul_inv_rev]`. Introduce `j`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]`.

Conclude with `Finset.sum_congr rfl fun x _ => by rw [secSpec n w hw x, mul_comm]`.
-/
theorem phiEquiv : PhiEquiv k := by
  intro n Λ hΛ F hF h w
  by_cases hw : w = 0
  · subst hw
    simp [phi, Matrix.mulVec_zero]
  · have hw' : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w ≠ 0 := by
      intro h0
      apply hw
      have e : ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ
          ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [phiIndep n Λ hΛ F hF _ hw' (sec w * h) ?_]
    · unfold phi
      rw [if_neg hw]
      congr 1
      funext x
      dsimp only
      rw [← cj_mul, _root_.mul_inv_rev]
    · intro j
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun x _ => by rw [secSpec n w hw x, mul_comm]

/- English proof (translation)
Introduce `_ _ ν _ n Λ hΛ F hF h`. Unfold `lt`. Establish `e : ∀ w, phi Λ (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w = phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w)` using `fun w => hE n Λ hΛ F hF h w`. Simplify using `only [e]`. Establish `hd : ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ).det ≠ 0`.

Rewrite using `[Matrix.det_transpose]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero`. Establish `key` using `integral_comp_mulVec_eq_smul ν (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) (fun v => phi Λ F v)`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = Matrix.GeneralLinearGroup.det h`. Use `ext`.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Matrix.det_transpose _`. Rewrite `key` using `[hdet]`. Conclude with `key.trans (by simp [Complex.real_smul])`.
-/
theorem ltEquiv (hE : PhiEquiv k) : LtEquiv k := by
  intro _ _ ν _ n Λ hΛ F hF h
  unfold lt
  have e : ∀ w, phi Λ (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w
      = phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) := fun w => hE n Λ hΛ F hF h w
  simp only [e]
  have hd : ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  have key := integral_comp_mulVec_eq_smul ν (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) (fun v => phi Λ F v)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd)
      = Matrix.GeneralLinearGroup.det h := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_transpose _
  rw [hdet] at key
  exact key.trans (by simp [Complex.real_smul])

end PositivityTheory.RgUd.AB.Pf
