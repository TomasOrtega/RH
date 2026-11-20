import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CoordGHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordU
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DecompU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

/- English proof (translation)
Rewrite using `[gramC_eq H f f' T T' hF hF', Matrix.det_transpose]`. Take `⟨s, hs, hdet⟩` from `gram_det H f f' T T' hF hF' hD1`. Establish `hsu : IsUnit s` using `⟨⟨s, s, hs, hs⟩, rfl⟩`. Establish `: (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s`. Rewrite using `[← hdet, mul_assoc, hs, mul_one]`.

Rewrite using `[this]`. Conclude with `hGd.mul hsu`.
-/
theorem unit_gramCU {f f' : Fin (r + 1) → V} {T T' : F}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hGd : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hGd.mul hsu

/- English proof (translation)
Use `set qi := algebraMap F E ((g.q : F)⁻¹) with hqi`. Set `B : Matrix (Ix r) (Ix r) E` to `Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))`. Establish `hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j`. Rewrite using `[mmfam_some H hs]`. Use function extensionality and compare the values at `i`.

Break down `i with a | a` into its components or cases. Simplify using `[B, Fintype.sum_sum_type, Matrix.one_apply]`. Simplify using `[B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]`. Both sides reduce to the same expression. Establish `hqu : IsUnit qi`.

Use `⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `qi_mul_q g`. Establish `hB : IsUnit B.det`. Simplify using `only [B]`.

Rewrite using `[Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `hqu.pow _`. Establish `hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T')`. Rewrite using `[gramC_eq H _ _ _ _ hF hF']`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hG` using `unit_gramCU H hF hF' hD1 hGd`. Rewrite using `[hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]`. Establish `hBc : IsUnit (B.map M.L.cj).det`. Establish `: (B.map M.L.cj).det = M.L.cj B.det`.

Rewrite using `[show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hB.map _`. Conclude with `(hB.mul hG).mul hBc`.
-/
theorem unit_gramHU {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hGd : IsUnit (H.Gdet t.f t.f' t.T t.T')) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramCU H hF hF' hD1 hGd
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gdet_eq (f f' : Fin (r + 1) → V) (T T' : F) :
    H.Gdet f f' T T' = H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := rfl

/- English proof (translation)
Rewrite using `[gdet_eq, gdet_eq, dl_swap_full, dl_swap_r, M.L.cj_cj, M.L.cj_cj, mul_comm T' T]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gdet_swap (f f' : Fin (r + 1) → V) (T T' : F) : H.Gdet f' f T' T = H.Gdet f f' T T' := by
  rw [gdet_eq, gdet_eq, dl_swap_full, dl_swap_r, M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
  ring

/- English proof (translation)
Introduce and unpack `_ ⟨u₁, u₁', u₁'', hu₁, hu₁', -, rfl⟩ _ ⟨u₂, u₂', u₂'', hu₂, hu₂', -, rfl⟩ hc hc'`. Simplify using `only [PcG, PcG', coordW_mk, Prod.mk.injEq] at hc hc'`. Establish `hν` using `nu_eq H t₁.f t₁.f' f₂ f₂' t₁.T' hg₁.2.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 hrel`. Establish `hrel' : H.Dl t₁.f' t₁.f r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl t₁.f' t₁.f (r + 1)`. Rewrite using `[dl_swap_r H t₁.f t₁.f', dl_swap_full H f₂ f₂', dl_swap_r H f₂ f₂', dl_swap_full H t₁.f t₁.f', ← map_mul, ← map_mul, hrel]`.

Establish `hν'` using `nu_eq H t₁.f' t₁.f f₂' f₂ t₁.T hg₁.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1) (unit_swap H _ _ hg₂.2.2.2.1) hrel'`. Prove the components needed by the constructor for the conclusion. Conclude with `mkW_transport H hg₁.2.1 hg₁.2.2.1 hg₂.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 (by rw [← gdet_eq]; exact hG₁) (by rw [← gdet_eq]; exact hG₂) hν φ hz ho ⟨u₁, hu₁⟩ (mem_span_of_sharpG H hg₁ u₁) ⟨u₂, hu₂⟩ (mem_span_of_sharpG H hg₂ u₂) hc.1 hc.2`. Conclude with `mkW_transport H hg₁.2.2.1 hg₁.2.1 hg₂.2.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1) (unit_swap H _ _ hg₂.2.2.2.1) (by rw [← gdet_eq, gdet_swap]; exact hG₁) (by rw [← gdet_eq, gdet_swap]; exact hG₂) hν' φ' hz' ho' ⟨u₁', hu₁'⟩ (by rw [span_swap]; exact mem_span_of_sharpG H hg₁ u₁') ⟨ …`.
-/
theorem gamR_sepU {g : SplitG M.L} {t₁ : Term V M r} {f₂ f₂' : Fin (r + 1) → V}
    (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))
    (hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')) (hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T'))
    (hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1))
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW f₂ ⟨_, z_mem H f₂ t₁.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW f₂ ⟨_, omP_mem H f₂ f₂' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW f₂' ⟨_, z_mem H f₂' t₁.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW f₂' ⟨_, omP_mem H f₂' f₂ (unit_swap H f₂ f₂' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)),
      ∀ p₂ ∈ GamR H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  rintro _ ⟨u₁, u₁', u₁'', hu₁, hu₁', -, rfl⟩ _ ⟨u₂, u₂', u₂'', hu₂, hu₂', -, rfl⟩ hc hc'
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at hc hc'
  have hν := nu_eq H t₁.f t₁.f' f₂ f₂' t₁.T' hg₁.2.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 hrel
  have hrel' : H.Dl t₁.f' t₁.f r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl t₁.f' t₁.f (r + 1) := by
    rw [dl_swap_r H t₁.f t₁.f', dl_swap_full H f₂ f₂', dl_swap_r H f₂ f₂', dl_swap_full H t₁.f t₁.f',
      ← map_mul, ← map_mul, hrel]
  have hν' := nu_eq H t₁.f' t₁.f f₂' f₂ t₁.T hg₁.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
    (unit_swap H _ _ hg₂.2.2.2.1) hrel'
  constructor
  · exact mkW_transport H hg₁.2.1 hg₁.2.2.1 hg₂.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1
      (by rw [← gdet_eq]; exact hG₁) (by rw [← gdet_eq]; exact hG₂) hν φ hz ho ⟨u₁, hu₁⟩
      (mem_span_of_sharpG H hg₁ u₁) ⟨u₂, hu₂⟩ (mem_span_of_sharpG H hg₂ u₂) hc.1 hc.2
  · exact mkW_transport H hg₁.2.2.1 hg₁.2.1 hg₂.2.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
      (unit_swap H _ _ hg₂.2.2.2.1)
      (by rw [← gdet_eq, gdet_swap]; exact hG₁) (by rw [← gdet_eq, gdet_swap]; exact hG₂) hν' φ' hz' ho'
      ⟨u₁', hu₁'⟩ (by rw [span_swap]; exact mem_span_of_sharpG H hg₁ u₁') ⟨u₂', hu₂'⟩
      (by rw [span_swap]; exact mem_span_of_sharpG H hg₂ u₂') hc'.2 hc'.1

end Parts

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M g hs r n V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hR`. Establish `hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T` using `⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩`. Establish `hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T'` using `⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩`. Establish `hT : t₁.T ∈ 𝒪[F]` using `hyp.1.1.2.1.2.2.2.1`. Establish `hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1)` using `hyp.2.2.2.1.2.2.2.2.2`.

Establish `hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')`. Establish `hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0` using `hyp.1.1.2.2.2.2.1`. Apply `isUnit_of_cj_fixed g _ hG` to reduce the goal to its premises. Rewrite using `[gdet_eq]`. Simplify using `only [map_sub, map_mul, M.L.cj_cj, M.L.cj.commutes]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T')`. Establish `key` using `gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1)) (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel`. Establish `hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)))` using `hU2.mul (hU2.map M.L.cj)`. Establish `: IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))))`.

Rewrite using `[gdet_eq, key]; exact hB.mul (by rw [← gdet_eq]; exact hG₁)`. Conclude with `isUnit_of_mul_isUnit_left this`. Establish `hg₁ : GoodG H g t₁` using `⟨hs, hF₁, hF₁', dl_succ_unit hyp, unit_gramHU H hs hF₁ hF₁' (dl_succ_unit hyp) hG₁⟩`. Establish `hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)` using `⟨hs, hyp.2.1, hyp.2.2.1, hU2, unit_gramHU H hs hyp.2.1 hyp.2.2.1 hU2 hG₂⟩`. Establish `hTT` using `(hyp.1.1.2.2.2.2.2 g hs).2.1`.

Establish `hI` using `hyp.2.2.2.1`. Establish `hmm : MMInt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)` using `mmInt_G H hg₂ hT hTT hR`. Establish `eZ` using `sends_one H φ _ _ (z_mem H t₁.f t₁.T hF₁) (z_mem H f₂ t₁.T hyp.2.1) hyp.2.2.2.2.1`. Establish `eZ'` using `sends_one H φ' _ _ (z_mem H t₁.f' t₁.T' hF₁') (z_mem H f₂' t₁.T' hyp.2.2.1) hyp.2.2.2.2.2`. Establish `eO` using `sends_omP H φ hg₁.2.2.2.1 hU2 hI.2.2.2.1`.

Establish `eO'` using `sends_omP' H φ' hg₁.2.2.2.1 hU2 hI.2.2.2.2.1`. Establish `hGam` using `fun θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) => graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ' (PcG H hg₁) (PcG H hg₂) (PcG' H hg₁) (PcG' H hg₂) (GamR H t₁ (algebraMap F E (g.q : F))) (GamR H _ (algebraMap F E (g.q : F))) _ …`. Establish `key : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r), θ ∈ Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔ (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)) ∈ ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₁.f …`. Introduce `θ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, _, hD', _, hG⟩`. Conclude with `⟨(isomD_iffG H hg₁ hg₂ θ).1 hD', (hGam θ).1 (hG g hs)⟩`. Introduce and unpack `⟨hD', hG⟩`. Use `⟨hU2, hmm, (isomD_iffG H hg₁ hg₂ θ).2 hD', fun h => ?_, fun g' hg' => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hs]`.

Consider the cases of `h`. Rewrite `hg'` using `[hs]`. Consider the cases of `hg'`. Conclude with `(hGam θ).2 hG`. Use `Nat.card_congr { toFun := fun θ => ⟨(PsiG H hg₁).symm.trans (θ.1.trans (PsiG H hg₂)), (key θ.1).1 θ.2⟩ invFun := fun θc => ⟨(PsiG H hg₁).trans (θc.1.trans (PsiG H hg₂).symm), (key _).2 (by` and prove the remaining obligations.

Use `θc.2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Use the proof step `simp)⟩`. Use `left_inv := fun θ => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `LinearEquiv.ext` to reduce the goal to its premises. Introduce `x`. Simplify using the standard rewrite rules. Use `right_inv := fun θc => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `LinearEquiv.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `}`.
-/
theorem coordGU_holds : CoordGU := by
  intro F _ _ _ E _ _ _ _ M g hs r n V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hR
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hyp.1.1.2.2.2.2.1
    apply isUnit_of_cj_fixed g _ hG
    rw [gdet_eq]
    simp only [map_sub, map_mul, M.L.cj_cj, M.L.cj.commutes]
    ring
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map M.L.cj)
    have : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' *
        (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [gdet_eq, key]; exact hB.mul (by rw [← gdet_eq]; exact hG₁)
    exact isUnit_of_mul_isUnit_left this
  have hg₁ : GoodG H g t₁ := ⟨hs, hF₁, hF₁', dl_succ_unit hyp,
    unit_gramHU H hs hF₁ hF₁' (dl_succ_unit hyp) hG₁⟩
  have hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) :=
    ⟨hs, hyp.2.1, hyp.2.2.1, hU2, unit_gramHU H hs hyp.2.1 hyp.2.2.1 hU2 hG₂⟩
  have hTT := (hyp.1.1.2.2.2.2.2 g hs).2.1
  have hI := hyp.2.2.2.1
  have hmm : MMInt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) := mmInt_G H hg₂ hT hTT hR
  have eZ := sends_one H φ _ _ (z_mem H t₁.f t₁.T hF₁) (z_mem H f₂ t₁.T hyp.2.1) hyp.2.2.2.2.1
  have eZ' := sends_one H φ' _ _ (z_mem H t₁.f' t₁.T' hF₁') (z_mem H f₂' t₁.T' hyp.2.2.1)
    hyp.2.2.2.2.2
  have eO := sends_omP H φ hg₁.2.2.2.1 hU2 hI.2.2.2.1
  have eO' := sends_omP' H φ' hg₁.2.2.2.1 hU2 hI.2.2.2.2.1
  have hGam := fun θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =>
    graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ' (PcG H hg₁) (PcG H hg₂)
      (PcG' H hg₁) (PcG' H hg₂) (GamR H t₁ (algebraMap F E (g.q : F))) (GamR H _ (algebraMap F E (g.q : F)))
      _ _ (gamR_image H hg₁) (gamR_image H hg₂)
      (coordW_comp H φ hI.1 _ _ _ _ _ _ _ _ eZ eO)
      (coordW_comp H φ' hI.2.1 _ _ _ _ _ _ _ _ eO' eZ')
      (gamR_sepU H hg₁ hg₂ hG₁ hG₂ hrel φ φ' eZ eO eZ' eO')
  have key : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r),
      θ ∈ Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)) ∈
          ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
            (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T') := by
    intro θ
    constructor
    · rintro ⟨_, _, hD', _, hG⟩
      exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hD', (hGam θ).1 (hG g hs)⟩
    · rintro ⟨hD', hG⟩
      refine ⟨hU2, hmm, (isomD_iffG H hg₁ hg₂ θ).2 hD', fun h => ?_, fun g' hg' => ?_⟩
      · rw [hs] at h; cases h
      · rw [hs] at hg'
        cases hg'
        exact (hGam θ).2 hG
  refine Nat.card_congr
    { toFun := fun θ => ⟨(PsiG H hg₁).symm.trans (θ.1.trans (PsiG H hg₂)), (key θ.1).1 θ.2⟩
      invFun := fun θc => ⟨(PsiG H hg₁).trans (θc.1.trans (PsiG H hg₂).symm), (key _).2 (by
        convert θc.2 using 1
        ext x
        simp)⟩
      left_inv := fun θ => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp
      right_inv := fun θc => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp }

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
