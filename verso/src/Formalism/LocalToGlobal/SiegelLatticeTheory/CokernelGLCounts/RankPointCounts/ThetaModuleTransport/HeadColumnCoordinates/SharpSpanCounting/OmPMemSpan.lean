import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.AdjLast

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

/- English proof (translation)
Establish `hadj : (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = 0`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]`. Establish `hcast : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc`. Use function extensionality and compare the values at `a`. Both sides reduce to the same expression.

Establish `h2 : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det`. Rewrite using `[Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos (Nat.le_succ r), hcast]`. Rewrite using `[← h2, hD0, mul_zero]`. Establish `hterm : ∀ b b', (H.Zhat f f').adjugate b (Fin.last r) * (M.L.cj ((H.Zhat f f').adjugate b' (Fin.last r)) * H.h (f' b) (f' b')) = 0`. Introduce `b b'`.

Distinguish the cases in `hb : b = Fin.last r`. Substitute `hb` using the available equality. Rewrite using `[hadj, zero_mul]`. Rewrite using `[hF'.1 b b' (Or.inl hb), mul_zero, mul_zero]`. Unfold `omP`.

Rewrite using `[H.h_smul_left, h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_left]`. Simplify using `only [h_sum_right, Finset.mul_sum, hterm, Finset.sum_const_zero, mul_zero]`.
-/
theorem h_omP_omP (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD0 : H.Dl f f' r = 0) : H.h (omP H f f') (omP H f f') = 0 := by
  have hadj : (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    have hcast : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := by
      funext a
      rfl
    have h2 : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
      rw [Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos (Nat.le_succ r), hcast]
    rw [← h2, hD0, mul_zero]
  have hterm : ∀ b b', (H.Zhat f f').adjugate b (Fin.last r) *
      (M.L.cj ((H.Zhat f f').adjugate b' (Fin.last r)) * H.h (f' b) (f' b')) = 0 := by
    intro b b'
    by_cases hb : b = Fin.last r
    · subst hb
      rw [hadj, zero_mul]
    · rw [hF'.1 b b' (Or.inl hb), mul_zero, mul_zero]
  unfold omP
  rw [H.h_smul_left, h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_left]
  simp only [h_sum_right, Finset.mul_sum, hterm, Finset.sum_const_zero, mul_zero]

/- English proof (translation)
Establish `hDl : H.Dl f f' (r + 1) = (H.Zhat f f').det`. Simplify using `[Formalism.MainNotions.S.Loc.HermSp.Dl, Fin.castLE_rfl, Matrix.submatrix_id_id]`. Establish `hz : ∀ b, H.h (f (Fin.last r)) (f' b) = M.L.cj (H.Zhat f f' (Fin.last r) b)` using `fun b => H.h_herm _ _`. Establish `hsum : ∑ b, M.L.cj ((H.Zhat f f').adjugate b (Fin.last r)) * M.L.cj (H.Zhat f f' (Fin.last r) b) = M.L.cj (H.Zhat f f').det`. Establish `h1` using `congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) (Fin.last r)) (Fin.last r)`.

Rewrite `h1` using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Rewrite using `[← h1, map_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [map_mul, mul_comm]`. Unfold `omP`. Rewrite using `[h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_right]`.

Simplify using `only [hz]`. Rewrite using `[hsum, ← map_mul, ← hDl, Ring.inverse_mul_cancel _ hD, map_one]`.
-/
theorem h_z_omP (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    H.h (f (Fin.last r)) (omP H f f') = 1 := by
  have hDl : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    simp [Formalism.MainNotions.S.Loc.HermSp.Dl, Fin.castLE_rfl, Matrix.submatrix_id_id]
  have hz : ∀ b, H.h (f (Fin.last r)) (f' b) = M.L.cj (H.Zhat f f' (Fin.last r) b) := fun b => H.h_herm _ _
  have hsum : ∑ b, M.L.cj ((H.Zhat f f').adjugate b (Fin.last r)) * M.L.cj (H.Zhat f f' (Fin.last r) b) =
      M.L.cj (H.Zhat f f').det := by
    have h1 := congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) (Fin.last r)) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    rw [← h1, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [map_mul, mul_comm]
  unfold omP
  rw [h_smul_right, Formalism.MainNotions.S.Loc.HermSp.om', h_sum_right]
  simp only [hz]
  rw [hsum, ← map_mul, ← hDl, Ring.inverse_mul_cancel _ hD, map_one]

/- English proof (translation)
Unfold `omP`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Unfold `Formalism.MainNotions.S.Loc.HermSp.om'`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)`.
-/
theorem omP_mem_span (f f' : Fin (r + 1) → V) :
    omP H f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold omP
  apply Submodule.smul_mem
  unfold Formalism.MainNotions.S.Loc.HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

/- English proof (translation)
Establish `hsubL : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y`. Introduce `x x' y`. Rewrite using `[sub_eq_add_neg, H.h_add_left, ← neg_one_smul E x', H.h_smul_left]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzo : H.h (f (Fin.last r)) (omP H f f') = 1` using `h_z_omP H f f' hD`.

Establish `hoz : H.h (omP H f f') (f (Fin.last r)) = 1`. Rewrite using `[H.h_herm, hzo, map_one]`. Establish `hoo : H.h (omP H f f') (omP H f f') = 0` using `h_omP_omP H f f' T' hF' hD0`. Establish `hwz : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (f (Fin.last r)) = 0`. Rewrite using `[hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hF.2, hoz, hβ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hwo : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f') = 0`. Rewrite using `[hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hzo, hoo, ← hα]`. Expand and normalize the polynomial expressions, which then agree. Establish `hom : H.om' f f' = H.Dl f f' (r + 1) • omP H f f'`.

Unfold `omP`. Rewrite using `[smul_smul, Ring.mul_inverse_cancel _ hD, one_smul]`. Apply `mem_X_of H f f' T T' hF hF' hD hD0` to reduce the goal to its premises. Conclude with `Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩)) (Submodule.smul_mem _ _ (omP_mem_span H f f')))`. Introduce `a`.

Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality. Conclude with `hwz`. Take `⟨a', rfl⟩` from `Fin.exists_castSucc_eq.2 ha`. Establish `hxa : f a'.castSucc ∈ H.X f` using `Submodule.subset_span ⟨a', rfl⟩`.

Establish `e1 : H.h u (f a'.castSucc) = 0` using `hX _ hxa`. Establish `e2 : H.h (f (Fin.last r)) (f a'.castSucc) = 0` using `hF.1 _ _ (Or.inr (Fin.castSucc_ne_last a'))`. Establish `e3 : H.h (omP H f f') (f a'.castSucc) = 0` using `(omP_mem H f f' hD) _ hxa`. Rewrite using `[hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hom, H.h_smul_left, H.h_herm (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f'), hwo, map_zero, mul_zero]`.
-/
theorem decomp (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f))
    (α β : E) (hα : α = H.h u (omP H f f'))
    (hβ : β = H.h u (f (Fin.last r)) + algebraMap F E T * α) :
    u - (α • f (Fin.last r) + β • omP H f f') ∈ H.X f := by
  have hsubL : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y := by
    intro x x' y
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E x', H.h_smul_left]
    ring
  have hzo : H.h (f (Fin.last r)) (omP H f f') = 1 := h_z_omP H f f' hD
  have hoz : H.h (omP H f f') (f (Fin.last r)) = 1 := by
    rw [H.h_herm, hzo, map_one]
  have hoo : H.h (omP H f f') (omP H f f') = 0 := h_omP_omP H f f' T' hF' hD0
  have hwz : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (f (Fin.last r)) = 0 := by
    rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hF.2, hoz, hβ]
    ring
  have hwo : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f') = 0 := by
    rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, hzo, hoo, ← hα]
    ring
  have hom : H.om' f f' = H.Dl f f' (r + 1) • omP H f f' := by
    unfold omP
    rw [smul_smul, Ring.mul_inverse_cancel _ hD, one_smul]
  apply mem_X_of H f f' T T' hF hF' hD hD0
  · exact Submodule.sub_mem _ hu (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
  · intro a
    by_cases ha : a = Fin.last r
    · subst ha
      exact hwz
    · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
      have hxa : f a'.castSucc ∈ H.X f := Submodule.subset_span ⟨a', rfl⟩
      have e1 : H.h u (f a'.castSucc) = 0 := hX _ hxa
      have e2 : H.h (f (Fin.last r)) (f a'.castSucc) = 0 := hF.1 _ _ (Or.inr (Fin.castSucc_ne_last a'))
      have e3 : H.h (omP H f f') (f a'.castSucc) = 0 := (omP_mem H f f' hD) _ hxa
      rw [hsubL, H.h_add_left, H.h_smul_left, H.h_smul_left, e1, e2, e3]
      ring
  · rw [hom, H.h_smul_left, H.h_herm (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f'), hwo, map_zero,
      mul_zero]

/- English proof (translation)
Establish `hmem` using `decomp H f f' T T' hF hF' hD hD0 u hu u.2 _ _ rfl rfl`. Rewrite using `[← sub_eq_zero, ← map_smul, ← map_smul, ← map_add, ← map_sub, Formalism.MainNotions.S.Loc.HermSp.mkW, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `hmem`.
-/
theorem mkW_decomp (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f u = H.h u (omP H f f') • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * H.h u (omP H f f')) •
        H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hmem := decomp H f f' T T' hF hF' hD hD0 u hu u.2 _ _ rfl rfl
  rw [← sub_eq_zero, ← map_smul, ← map_smul, ← map_add, ← map_sub, Formalism.MainNotions.S.Loc.HermSp.mkW,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact hmem

end Formalism.L2.SG.LocalCountModules.LocCntCommon
