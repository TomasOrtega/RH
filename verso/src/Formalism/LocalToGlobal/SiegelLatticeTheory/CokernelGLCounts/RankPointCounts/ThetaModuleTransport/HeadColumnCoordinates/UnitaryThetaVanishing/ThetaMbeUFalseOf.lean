import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Establish `hn : ∀ x : E, M.L.cj (H.normE x) = H.normE x`. Introduce `x`. Rewrite using `[HermSp.normE, map_mul, M.L.cj_cj, mul_comm]`. Simplify using `only [HermSp.Gdet, map_sub, map_mul, AlgEquiv.commutes, hn]`.
-/
theorem gdet_fix (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) :
    M.L.cj (H.Gdet f f' T T') = H.Gdet f f' T T' := by
  have hn : ∀ x : E, M.L.cj (H.normE x) = H.normE x := by
    intro x
    rw [HermSp.normE, map_mul, M.L.cj_cj, mul_comm]
  simp only [HermSp.Gdet, map_sub, map_mul, AlgEquiv.commutes, hn]

/- English proof (translation)
Take `⟨a, ha⟩` from `(M.L.cj_fix _).mp (gdet_fix H f f' T T')`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `hG` to reduce the goal to its premises. Rewrite using `[← ha, map_zero]`.

Rewrite using `[← ha]`. Conclude with `(IsUnit.mk0 a ha0).map (algebraMap F E)`.
-/
theorem gdet_unit (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hG : H.Gdet f f' T T' ≠ 0) : IsUnit (H.Gdet f f' T T') := by
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).mp (gdet_fix H f f' T T')
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hG
    rw [← ha, map_zero]
  rw [← ha]
  exact (IsUnit.mk0 a ha0).map (algebraMap F E)

/- English proof (translation)
Establish `hmul : ∀ x y : E, H.normE x * H.normE y = H.normE (x * y)`. Introduce `x y`. Simplify using `only [HermSp.normE, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `congrArg H.normE hrel`.

Rewrite `h` using `[← hmul, ← hmul]`. Simplify using `only [HermSp.Gdet]`. Take the linear combination `(algebraMap F E (T * T')) * h`.
-/
theorem gdet_rel (H : HermSp M V) {r : ℕ} (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  have hmul : ∀ x y : E, H.normE x * H.normE y = H.normE (x * y) := by
    intro x y
    simp only [HermSp.normE, map_mul]
    ring
  have h := congrArg H.normE hrel
  rw [← hmul, ← hmul] at h
  simp only [HermSp.Gdet]
  linear_combination (algebraMap F E (T * T')) * h

/- English proof (translation)
Rewrite using `[gramC_eq H f f' T T' hF hF', Matrix.det_transpose]`. Take `⟨s, hs, hdet⟩` from `gram_det H f f' T T' hF hF' hD1`. Establish `: (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s`. Rewrite using `[← hdet, mul_assoc, hs, mul_one]`. Rewrite using `[this]`.

Conclude with `hG.mul ⟨⟨s, s, hs, hs⟩, rfl⟩`.
-/
theorem unit_gramC_of (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hG.mul ⟨⟨s, s, hs, hs⟩, rfl⟩

/- English proof (translation)
Take `⟨L, sp, mu⟩` from `M`. Consider the cases of `sp with`. Consider the case `some g => intro hmode`. Simplify using `at hmode`. Consider the case `none`.

Introduce `_ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂`. Establish `hs : (⟨L, none, mu⟩ : Model F E).split = none` using `rfl`. Establish `z₁ : Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f'`. Rewrite using `[e₁]`. Conclude with `zzplusOf_none hs _ _ _`.

Establish `z₂ : Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂'`. Rewrite using `[e₂]`. Conclude with `zzplusOf_none hs _ _ _`. Establish `hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1))` using `dl_succ_unit hyp`. Establish `hU2 : IsUnit (H.Dl f₂ f₂' (r + 1))` using `by rw [dl_full, ← z₂]; exact Z₂.unit`.

Establish `hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1)` using `hyp.2.2.2.1.2.2.2.2.2`. Establish `hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O`. Introduce `a b`. Rewrite using `[← z₂]`. Conclude with `(Z₂.Z a b).2`.

Establish `hT : t₁.T ∈ 𝒪[F]` using `hyp.1.1.2.1.2.2.2.1`. Establish `hT' : t₁.T' ∈ 𝒪[F]` using `hyp.1.1.2.2.1.2.2.2.1`. Establish `hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T` using `⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩`. Establish `hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T'` using `⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩`. Establish `hGu₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')` using `gdet_unit H _ _ _ _ hyp.1.1.2.2.2.2.1`.

Establish `hGu₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T')`. Establish `hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1)))` using `hU2.mul (hU2.map L.cj)`. Use `gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel` as an intermediate fact. Establish `hp : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1)))`. Rewrite using `[this]`.

Conclude with `hN₂.mul hGu₁`. Conclude with `isUnit_of_mul_isUnit_left hp`. Establish `hG1` using `unit_gramC_of H _ _ _ _ hF₁ hF₁' hU1 hGu₁`. Establish `hG2` using `unit_gramC_of H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hGu₂`. Establish `hh : ((Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).det = ((Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).det`.

Rewrite using `[z₁, z₂, ← dl_eq_det, ← dl_eq_det, ← dl_full, ← dl_full]`. Conclude with `hrel`. Rewrite `hG1` using `[← z₁]`. Rewrite `hG2` using `[← z₂]`. Rewrite using `[h1 F E ⟨L, none, mu⟩ hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hint, ← z₁, ← z₂]`.

Conclude with `h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx) r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩) (AlgEquiv.commutes _ _) (AlgEquiv.commu …`.
-/
theorem thetaMbeU_false_of (h1 : CoordU) (h2 : AlgAll) (M : Model F E) (r n : ℕ) :
    Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.ThetaMbeU M r n false := by
  obtain ⟨L, sp, mu⟩ := M
  cases sp with
  | some g => intro hmode; simp at hmode
  | none =>
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : (⟨L, none, mu⟩ : Model F E).split = none := rfl
  have z₁ : Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f' := by
    rw [e₁]; exact zzplusOf_none hs _ _ _
  have z₂ : Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂' := by
    rw [e₂]; exact zzplusOf_none hs _ _ _
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hU2 : IsUnit (H.Dl f₂ f₂' (r + 1)) := by rw [dl_full, ← z₂]; exact Z₂.unit
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O := by
    intro a b
    rw [← z₂]
    exact (Z₂.Z a b).2
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hyp.1.1.2.2.1.2.2.2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hGu₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := gdet_unit H _ _ _ _ hyp.1.1.2.2.2.2.1
  have hGu₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map L.cj)
    have := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
    have hp : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [this]; exact hN₂.mul hGu₁
    exact isUnit_of_mul_isUnit_left hp
  have hG1 := unit_gramC_of H _ _ _ _ hF₁ hF₁' hU1 hGu₁
  have hG2 := unit_gramC_of H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hGu₂
  have hh : ((Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).det =
      ((Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).det := by
    rw [z₁, z₂, ← dl_eq_det, ← dl_eq_det, ← dl_full, ← dl_full]
    exact hrel
  rw [← z₁] at hG1
  rw [← z₂] at hG2
  rw [h1 F E ⟨L, none, mu⟩ hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hint, ← z₁, ← z₂]
  exact h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx)
    r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩)
    (AlgEquiv.commutes _ _) (AlgEquiv.commutes _ _) Z₁.Z Z₂.Z Z₁.unit Z₂.unit hh hG1 hG2

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
