import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.ThetaMbeU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.S.Loc.Model.R, hs]`.
-/
theorem R_eq_O' (hs : M.split = none) : M.R = M.L.O := by
  simp only [Formalism.MainNotions.S.Loc.Model.R, hs]

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos le_rfl]`. Simplify using `[Fin.castLE_rfl]`.
-/
theorem dl_full' (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  rw [Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos le_rfl]
  simp [Fin.castLE_rfl]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Y₁ Y₂ be₁ be₂ al₁ al₂ eY eb`. Establish `hs : M.split = none`. Consider the cases of `h : M.split with`. Consider the case `none => rfl`. Consider the case `some g => simp [h] at hmode`.

Establish `hR : M.R = M.L.O` using `R_eq_O' hs`. Establish `z₁ : H.ZZplus t₁ = H.Zhat t₁.f t₁.f'` using `zzplusOf_none hs _ _ _`. Establish `z₂ : HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' = H.Zhat f₂ f₂'` using `zzplusOf_none hs _ _ _`. Simplify using `only [z₁, z₂] at eY eb`. Establish `hg` using `hyp.1`.

Establish `hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1)` using `hyp.2.2.2.1.2.2.2.2.2`. Establish `hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1))` using `dl_succ_unit hyp`. Establish `hY₂ : Y₂.Z.map M.R.subtype = (H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `a b`. Conclude with `(eY a b).2`.

Establish `hU2r : IsUnit (H.Dl f₂ f₂' r)` using `by rw [dl_eq_det, ← hY₂]; exact Y₂.unit`. Establish `hU2 : IsUnit (H.Dl f₂ f₂' (r + 1))`. Establish `: IsUnit (H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1))` using `by rw [hrel]; exact hU2r.mul hU1`. Conclude with `isUnit_of_mul_isUnit_right this`. Establish `hint₁ : ∀ a b, H.Zhat t₁.f t₁.f' a b ∈ M.R`.

Introduce `a b`. Rewrite using `[hR]`. Conclude with `(hg.1.1.2.2 (t₁.f' b)).1 (hg.1.2.2.1.1.1 b) (t₁.f a) (hg.1.2.1.1.1 a)`. Set `Z₁ : M.Mat (r + 1)` to `⟨Matrix.of fun a b => ⟨H.Zhat t₁.f t₁.f' a b, hint₁ a b⟩, by`. Establish `: (Matrix.of fun a b => (⟨H.Zhat t₁.f t₁.f' a b, hint₁ a b⟩ : M.R)).map M.R.subtype = H.Zhat t₁.f t₁.f'` using `rfl`.

Rewrite using `[this, ← dl_full']`. Conclude with `hU1⟩`. Establish `hdet : headDet M Z₁.Z * (H.Zhat f₂ f₂').det = ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det * (Z₁.Z.map M.R.subtype).det` using `by show ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat f₂ f₂').det = ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat t₁.f t₁.f').det`. Rewrite using `[← dl_eq_det, ← dl_eq_det, ← dl_full', ← dl_full']`. Conclude with `hrel`.

Distinguish the cases in `hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ M.R`. Set `Z₂ : M.Mat (r + 1)` to `⟨Matrix.of fun a b => ⟨H.Zhat f₂ f₂' a b, hint a b⟩, by`. Establish `: (Matrix.of fun a b => (⟨H.Zhat f₂ f₂' a b, hint a b⟩ : M.R)).map M.R.subtype = H.Zhat f₂ f₂'` using `rfl`. Rewrite using `[this, ← dl_full']`. Conclude with `hU2⟩`.

Establish `e₁ : Z₁.Z.map M.R.subtype = H.ZZplus t₁` using `by rw [z₁]; rfl`. Establish `e₂ : Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'` using `by rw [z₂]; rfl`. Rewrite using `[h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂]`. Conclude with `h2 F E M hOK r Z₁ Z₂ Y₁ Y₂ be₁ be₂ al₁ al₂ (fun a b => ⟨Subtype.ext (eY a b).1, Subtype.ext (eY a b).2⟩) (fun a => ⟨Subtype.ext (eb a).1, Subtype.ext (eb a).2.1, Subtype.ext (eb a).2.2.1, Subtype.ext (eb a).2.2.2⟩) hdet`. Establish `hTh : Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' = ∅`.

Use extensionality with `θ`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hθ`. Apply `hint` to reduce the goal to its premises. Introduce `a b`.

Establish `hm : MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩` using `hθ.2.1`. Rewrite using `[hR]`. Establish `ha : f₂ a ∈ MMo H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩` using `Submodule.subset_span ⟨Sum.inl a, by simp only [HermSp.MMfam, hs, Sum.elim_inl]⟩`. Establish `hb : f₂' b ∈ MMo H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩` using `Submodule.subset_span ⟨Sum.inr b, by simp only [HermSp.MMfam, hs, Sum.elim_inr]⟩`. Conclude with `hm _ hb _ ha`.

Use `haveI hne : IsEmpty {ψ : M.Cok Y₁ ≃ₗ[M.R] M.Cok Y₂ // ψ (Submodule.Quotient.mk be₁) = Submodule.Quotient.mk be₂ ∧ ∀ v, M.linQ Y₂ al₂ (ψ v) = M.linQ Y₁ al₁ v} := by`. Use `⟨fun ψ => hint ?_⟩` and prove the remaining obligations. Establish `hc` using `h3 F E M hOK r Z₁ (H.Zhat f₂ f₂') Y₁ Y₂ be₁ be₂ al₁ al₂ (fun a b => ⟨Subtype.ext (eY a b).1, (eY a b).2⟩) (fun a => ⟨Subtype.ext (eb a).1, (eb a).2.1, Subtype.ext (eb a).2.2.1, (eb a).2.2.2⟩) hdet ⟨ψ⟩`. Introduce `a b`. Apply the tactic sequence `rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>`.

Break down `Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl` into its components or cases. Rewrite using `[← (eY a' b').2]`. Conclude with `(Y₂.Z a' b').2`. Rewrite using `[← (eb a').2.1]`. Conclude with `(be₂ a').2`.

Rewrite using `[← (eb b').2.2.2]`. Conclude with `(al₂ b').2`. Conclude with `hc`. Rewrite using `[hTh, Nat.card_of_isEmpty, Model.nIsoBA, Nat.card_of_isEmpty]`.
-/
theorem locCntUL_of
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbeU M r n false))
    (h2 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r, MbeU M r))
    (h3 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r, CornerU M r)) : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Y₁ Y₂ be₁ be₂ al₁ al₂ eY eb
  have hs : M.split = none := by
    cases h : M.split with
    | none => rfl
    | some g => simp [h] at hmode
  have hR : M.R = M.L.O := R_eq_O' hs
  have z₁ : H.ZZplus t₁ = H.Zhat t₁.f t₁.f' := zzplusOf_none hs _ _ _
  have z₂ : HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' = H.Zhat f₂ f₂' := zzplusOf_none hs _ _ _
  simp only [z₁, z₂] at eY eb
  have hg := hyp.1
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hY₂ : Y₂.Z.map M.R.subtype = (H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc := by
    ext a b; exact (eY a b).2
  have hU2r : IsUnit (H.Dl f₂ f₂' r) := by rw [dl_eq_det, ← hY₂]; exact Y₂.unit
  have hU2 : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    have : IsUnit (H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1)) := by rw [hrel]; exact hU2r.mul hU1
    exact isUnit_of_mul_isUnit_right this
  have hint₁ : ∀ a b, H.Zhat t₁.f t₁.f' a b ∈ M.R := by
    intro a b
    rw [hR]
    exact (hg.1.1.2.2 (t₁.f' b)).1 (hg.1.2.2.1.1.1 b) (t₁.f a) (hg.1.2.1.1.1 a)
  let Z₁ : M.Mat (r + 1) := ⟨Matrix.of fun a b => ⟨H.Zhat t₁.f t₁.f' a b, hint₁ a b⟩, by
    have : (Matrix.of fun a b => (⟨H.Zhat t₁.f t₁.f' a b, hint₁ a b⟩ : M.R)).map M.R.subtype =
      H.Zhat t₁.f t₁.f' := rfl
    rw [this, ← dl_full']; exact hU1⟩
  have hdet : headDet M Z₁.Z * (H.Zhat f₂ f₂').det =
      ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det * (Z₁.Z.map M.R.subtype).det := by
    show ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat f₂ f₂').det =
      ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat t₁.f t₁.f').det
    rw [← dl_eq_det, ← dl_eq_det, ← dl_full', ← dl_full']
    exact hrel
  by_cases hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ M.R
  · let Z₂ : M.Mat (r + 1) := ⟨Matrix.of fun a b => ⟨H.Zhat f₂ f₂' a b, hint a b⟩, by
      have : (Matrix.of fun a b => (⟨H.Zhat f₂ f₂' a b, hint a b⟩ : M.R)).map M.R.subtype =
        H.Zhat f₂ f₂' := rfl
      rw [this, ← dl_full']; exact hU2⟩
    have e₁ : Z₁.Z.map M.R.subtype = H.ZZplus t₁ := by rw [z₁]; rfl
    have e₂ : Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' := by rw [z₂]; rfl
    rw [h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂]
    exact h2 F E M hOK r Z₁ Z₂ Y₁ Y₂ be₁ be₂ al₁ al₂
      (fun a b => ⟨Subtype.ext (eY a b).1, Subtype.ext (eY a b).2⟩)
      (fun a => ⟨Subtype.ext (eb a).1, Subtype.ext (eb a).2.1, Subtype.ext (eb a).2.2.1,
        Subtype.ext (eb a).2.2.2⟩) hdet
  · have hTh : Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' = ∅ := by
      ext θ
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hθ
      apply hint
      intro a b
      have hm : MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ := hθ.2.1
      rw [hR]
      have ha : f₂ a ∈ MMo H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ :=
        Submodule.subset_span ⟨Sum.inl a, by simp only [HermSp.MMfam, hs, Sum.elim_inl]⟩
      have hb : f₂' b ∈ MMo H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ :=
        Submodule.subset_span ⟨Sum.inr b, by simp only [HermSp.MMfam, hs, Sum.elim_inr]⟩
      exact hm _ hb _ ha
    haveI hne : IsEmpty {ψ : M.Cok Y₁ ≃ₗ[M.R] M.Cok Y₂ //
        ψ (Submodule.Quotient.mk be₁) = Submodule.Quotient.mk be₂ ∧
          ∀ v, M.linQ Y₂ al₂ (ψ v) = M.linQ Y₁ al₁ v} := by
      refine ⟨fun ψ => hint ?_⟩
      have hc := h3 F E M hOK r Z₁ (H.Zhat f₂ f₂') Y₁ Y₂ be₁ be₂ al₁ al₂
        (fun a b => ⟨Subtype.ext (eY a b).1, (eY a b).2⟩)
        (fun a => ⟨Subtype.ext (eb a).1, (eb a).2.1, Subtype.ext (eb a).2.2.1, (eb a).2.2.2⟩) hdet ⟨ψ⟩
      intro a b
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · rw [← (eY a' b').2]; exact (Y₂.Z a' b').2
      · rw [← (eb a').2.1]; exact (be₂ a').2
      · rw [← (eb b').2.2.2]; exact (al₂ b').2
      · exact hc
    rw [hTh, Nat.card_of_isEmpty, Model.nIsoBA, Nat.card_of_isEmpty]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
