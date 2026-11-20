import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsPt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel

noncomputable section

namespace Formalism.L2.SG.WConst

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `| _, [] => rfl | b, (s, t) :: rest => by simp only [Formalism.L2.SG.DataInst.signAux, signFlip_involutive r (b + s) rest] congr 2 rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul] simp`.
-/
theorem signFlip_involutive {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K),
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [Formalism.L2.SG.DataInst.signAux, signFlip_involutive r (b + s) rest]
    congr 2
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

variable {D : D7}

def lst (w : Point D.host.E (D.R.rS + 1)) : Formalism.FourierDecayAlt.TB.Pt D.host.E :=
  Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)

/- English proof (translation)
Establish `h : Formalism.L2.SG.DataInst.signPt D.R.rS (lst w) = Formalism.L2.S.ptList w`. Unfold `lst Formalism.L2.SG.DataInst.signPt`. Conclude with `signFlip_involutive _ _ _`. Establish `hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS (lst w)) (D.R.rS + 1)`. Rewrite using `[h]`.

Conclude with `Formalism.L2.S.ptList_isPtL w`. Unfold `Formalism.L2.SG.DataInst.ptOfList`. Rewrite using `[dif_pos hL]`. Use `congr 1`. Apply `(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).injective` to reduce the goal to its premises.

Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `Subtype.ext h`.
-/
theorem ptOfList_lst (w : Point D.host.E (D.R.rS + 1)) :
    Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) (lst w) = some w := by
  have h : Formalism.L2.SG.DataInst.signPt D.R.rS (lst w) = Formalism.L2.S.ptList w := by
    unfold lst Formalism.L2.SG.DataInst.signPt
    exact signFlip_involutive _ _ _
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS (lst w)) (D.R.rS + 1) := by
    rw [h]; exact Formalism.L2.S.ptList_isPtL w
  unfold Formalism.L2.SG.DataInst.ptOfList
  rw [dif_pos hL]
  congr 1
  apply (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext h

/- English proof (translation)
Introduce `w w' h`. Use `(ptOfList_lst w).symm.trans ((congrArg _ h).trans (ptOfList_lst w'))` as an intermediate fact. Conclude with `Option.some_injective _ this`.
-/
theorem lst_injective : Function.Injective (lst (D := D)) := by
  intro w w' h
  have := (ptOfList_lst w).symm.trans ((congrArg _ h).trans (ptOfList_lst w'))
  exact Option.some_injective _ this

/- English proof (translation)
The claim follows from `Formalism.L2.SG.RowsAbsX.ptOfList_inj hp (ptOfList_lst w)`.
-/
theorem eq_lst_of {p : Formalism.FourierDecayAlt.TB.Pt D.host.E} {w : Point D.host.E (D.R.rS + 1)}
    (hp : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p = some w) : p = lst w :=
  Formalism.L2.SG.RowsAbsX.ptOfList_inj hp (ptOfList_lst w)

section Regroup

open Formalism.L2.SG.Pf.RowForm

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

/- English proof (translation)
Introduce `ρ`. Use `haveI := FiniteDimensional.complete ℂ (X.Vpi u)`. Use `set V : Point D.host.E (D.R.rS + 1) → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) := fun w => Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) with hV`. Establish `hsupp : Function.support (ptVal X Y u u' vR i0 i0' νq κ ρ) ⊆ Set.range lst`. Introduce `p hp`.

Break down `h : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p with _ | w` into its components or cases. Conclude with `absurd (by simp [ptVal, h]) hp`. Conclude with `⟨w, (eq_lst_of h).symm⟩`. Rewrite using `[← lst_injective.tsum_eq hsupp]`. Use `set f : ClassT X Y u u' κ ρ → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) := fun t => (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) • V (Formalism.L2.SG.PairVal.ptOf t.1) with hf`.

Set `e : (Σ w : Point D.host.E (D.R.rS + 1), {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) → ClassT X Y u u' κ ρ` to `fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.1⟩`. Establish `huniq : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w w', t.atPt w → t.atPt w' → w = w'` using `fun t w w' h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.cls w w' h h'`. Establish `he : Function.Injective e`. Introduce and unpack `⟨w, t, ht⟩ ⟨w', t', ht'⟩ h`. Establish `htt : t = t'` using `congrArg Subtype.val h`.

Substitute `htt` using the available equality. Establish `hw : w = w'` using `huniq t w w' ht.2.2 ht'.2.2`. Substitute `hw` using the available equality. Both sides reduce to the same expression. Establish `hpt : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w → Formalism.L2.SG.PairVal.ptOf t = w`.

Introduce `t w h`. Establish `hrel` using `Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t w h`. Conclude with `huniq t _ _ (Formalism.L2.SG.PairVal.ptOf_spec t ⟨w, h, hrel⟩) h`. Establish `hc : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w → Formalism.L2.SG.PairVal.cTerm vR t = Formalism.L2.SG.PairVal.cAt vR t w` using `fun t w h => Formalism.L2.SG.PairVal.cTerm_of_atPt vR t h (fun w' h' => huniq t w' w h' h)`. Establish `hFe : ∀ x : (Σ w : Point D.host.E (D.R.rS + 1), {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}), (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1 = f (e x …`.

Introduce and unpack `⟨w, t, ht⟩`. Simplify using `only [hf, e, hpt t w ht.2.2, hc t w ht.2.2]`. Establish `hfs : Summable f` using `Summable.of_norm (hA ρ)`. Establish `hsum : Summable (f ∘ e)` using `hfs.comp_injective he`. Establish `hsumF : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1), {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) => (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) …`.

Simplify `hsum` using `only [Function.comp_def, hFe]`. Establish `hnorm : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1), {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) => ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) …`. Establish `h0 : Summable (fun x => ‖f (e x)‖)` using `(hA ρ).comp_injective he`. Conclude with `h0.congr (fun x => by rw [← hFe x])`. Establish `h2 : ∀ w, ptVal X Y u u' vR i0 i0' νq κ ρ (lst w) = ∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}, (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w) • V w`.

Introduce `w`. Simplify using `only [ptVal, ptOfList_lst]`. Distinguish the cases in `hV : V w = 0`. Establish `hV' : Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) = 0` using `hV`. Rewrite using `[hV', smul_zero]`.

Simplify using `only [hV, smul_zero, tsum_zero]`. Establish `h3` using `hnorm.sigma_factor w`. Simplify using `only [norm_smul] at h3`. Establish `h4 : Summable (fun t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w} => ‖((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w‖)`. Establish `h5` using `h3.div_const ‖V w‖`.

Establish `hVn : ‖V w‖ ≠ 0` using `norm_ne_zero_iff.2 hV`. Simplify `h5` using `only [mul_div_assoc, div_self hVn, mul_one]`. Conclude with `((Summable.of_norm h4).tsum_smul_const (V w)).symm`. Rewrite using `[tsum_congr h2]`. Rewrite using `[← hsumF.tsum_sigma]`.

Rewrite using `[tsum_congr hFe]`. Establish `hsuppf : Function.support f ⊆ Set.range e`. Introduce `t ht`. Distinguish the cases in `h : ∃ w, t.1.atPt w`. Take `⟨w, hw⟩` from `h`.

Conclude with `⟨⟨w, t.1, t.2.1, t.2.2, hw⟩, rfl⟩`. It suffices to derive a contradiction. Apply `ht` to reduce the goal to its premises. Simplify using `only [hf, Formalism.L2.SG.PairVal.cTerm, dif_neg h, mul_zero, zero_smul]`. Conclude with `he.tsum_eq hsuppf`.
-/
theorem pointRegroupC_of (hA : ClassAbsC X Y u u' vR i0 i0' νq κ) : PointRegroupC X Y u u' vR i0 i0' νq κ := by
  intro ρ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set V : Point D.host.E (D.R.rS + 1) → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
    fun w => Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) with hV

  have hsupp : Function.support (ptVal X Y u u' vR i0 i0' νq κ ρ) ⊆ Set.range lst := by
    intro p hp
    rcases h : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p with _ | w
    · exact absurd (by simp [ptVal, h]) hp
    · exact ⟨w, (eq_lst_of h).symm⟩
  rw [← lst_injective.tsum_eq hsupp]

  set f : ClassT X Y u u' κ ρ → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) := fun t =>
    (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      V (Formalism.L2.SG.PairVal.ptOf t.1) with hf
  let e : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) →
      ClassT X Y u u' κ ρ := fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.1⟩
  have huniq : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w w', t.atPt w → t.atPt w' → w = w' :=
    fun t w w' h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.cls w w' h h'
  have he : Function.Injective e := by
    rintro ⟨w, t, ht⟩ ⟨w', t', ht'⟩ h
    have htt : t = t' := congrArg Subtype.val h
    subst htt
    have hw : w = w' := huniq t w w' ht.2.2 ht'.2.2
    subst hw
    rfl
  have hpt : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w → Formalism.L2.SG.PairVal.ptOf t = w := by
    intro t w h
    have hrel := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t w h
    exact huniq t _ _ (Formalism.L2.SG.PairVal.ptOf_spec t ⟨w, h, hrel⟩) h
  have hc : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) w, t.atPt w →
      Formalism.L2.SG.PairVal.cTerm vR t = Formalism.L2.SG.PairVal.cAt vR t w :=
    fun t w h => Formalism.L2.SG.PairVal.cTerm_of_atPt vR t h (fun w' h' => huniq t w' w h' h)
  have hFe : ∀ x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}),
      (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1 =
        f (e x) := by
    rintro ⟨w, t, ht⟩
    simp only [hf, e, hpt t w ht.2.2, hc t w ht.2.2]
  have hfs : Summable f := Summable.of_norm (hA ρ)
  have hsum : Summable (f ∘ e) := hfs.comp_injective he
  have hsumF : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) =>
      (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1) := by
    simpa only [Function.comp_def, hFe] using hsum
  have hnorm : Summable (fun x : (Σ w : Point D.host.E (D.R.rS + 1),
      {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}) =>
      ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) x.2.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR x.2.1 x.1) • V x.1‖) := by
    have h0 : Summable (fun x => ‖f (e x)‖) := (hA ρ).comp_injective he
    exact h0.congr (fun x => by rw [← hFe x])

  have h2 : ∀ w, ptVal X Y u u' vR i0 i0' νq κ ρ (lst w) =
      ∑' t : {t : Term D u u' (X.Fu u) (Y.what₂ u) // Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w},
        (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w) • V w := by
    intro w
    simp only [ptVal, ptOfList_lst]
    by_cases hV : V w = 0
    · have hV' : Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) = 0 := hV
      rw [hV', smul_zero]
      simp only [hV, smul_zero, tsum_zero]
    · have h3 := hnorm.sigma_factor w
      simp only [norm_smul] at h3
      have h4 : Summable (fun t : {t : Term D u u' (X.Fu u) (Y.what₂ u) //
          Formalism.L2.SG.DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w} =>
          ‖((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cAt vR t.1 w‖) := by
        have h5 := h3.div_const ‖V w‖
        have hVn : ‖V w‖ ≠ 0 := norm_ne_zero_iff.2 hV
        simpa only [mul_div_assoc, div_self hVn, mul_one] using h5
      exact ((Summable.of_norm h4).tsum_smul_const (V w)).symm
  rw [tsum_congr h2]
  rw [← hsumF.tsum_sigma]
  rw [tsum_congr hFe]
  have hsuppf : Function.support f ⊆ Set.range e := by
    intro t ht
    by_cases h : ∃ w, t.1.atPt w
    · obtain ⟨w, hw⟩ := h
      exact ⟨⟨w, t.1, t.2.1, t.2.2, hw⟩, rfl⟩
    · exfalso
      apply ht
      simp only [hf, Formalism.L2.SG.PairVal.cTerm, dif_neg h, mul_zero, zero_smul]
  exact he.tsum_eq hsuppf

end Regroup

end Formalism.L2.SG.WConst
