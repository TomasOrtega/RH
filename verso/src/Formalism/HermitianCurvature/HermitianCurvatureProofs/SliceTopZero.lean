import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Substitute `hρ` using the available equality. Use `⟨hγ, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Establish `hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2))` using `Fin.ext (by simp only; omega)`. Substitute `hl0` using the available equality. Unfold `Dmin`.

Rewrite using `[Matrix.det_fin_zero]`. Conclude with `one_ne_zero`. Establish `e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ`. Unfold `Gf Q.GGl Dmin`. Rewrite using `[Matrix.det_fin_zero, Matrix.det_fin_one]`.

Simplify using `only [Complex.normSq_one, mul_one]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hG`.
-/
theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

/- English proof (translation)
Establish `hOm` using `om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG`. Break down `P with ⟨k, r, T, T', u, u'⟩` into its components or cases. Simplify using `only at hr`. Substitute `hr` using the available equality. Establish `hnil : h = []`.

Consider the cases of `h with`. Consider the case `nil => rfl`. Consider the case `cons b t`. It suffices to derive a contradiction. Establish `h1` using `(hh.1 b (List.mem_cons.2 (Or.inl rfl))).1`.

Establish `h2` using `hh.2`. Simplify using `only [D.ptSize, List.map_cons, List.sum_cons] at h2`. Use linear arithmetic over natural numbers and integers. Substitute `hnil` using the available equality. Establish `hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt)))` using `⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩`.

Use `set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀`. Establish `hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀`. Rewrite using `[volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]`. Establish `hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀` using `fun v => funext fun q => (hE.false q).elim`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hvol]`. Use `(integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [hxe v]`. Establish `hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) = CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ`. Rewrite using `[hvol, integral_dirac]`.

Unfold `PBQ.ellH`. Establish `hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt)))` using `⟨fun i => Fin.elim0 (i : Fin 0)⟩`. Establish `hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0`. Unfold `U.subS`. Conclude with `Finset.sum_of_isEmpty _`.

Rewrite using `[hs]`. Simplify using `[Formalism.FourierDecayAlt.G.psi]`. Rewrite using `[hone]`. Establish `e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G`. Use function extensionality and compare the values at `y`.

Simplify using `only [D.castF]`. Use `(Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_` and prove the remaining obligations. Conclude with `congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)`. Establish `hCpt : KB.CptCoef (p.T.bs 0) G` using `hG.1`. Establish `hL` using `SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)`.

Establish `hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ`. Unfold `CutEX.xT U.mMap`. Rewrite using `[SliceIntegralLemmas.block_three_zero_size_eq]`. Conclude with `Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ`. Rewrite using `[e3, hL]`.

Unfold `CutEX.pbTop PBQ.pbT`. Rewrite using `[hx, SliceIntegralLemmas.pbF_zero]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]`.

Both sides reduce to the same expression.
-/
theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
