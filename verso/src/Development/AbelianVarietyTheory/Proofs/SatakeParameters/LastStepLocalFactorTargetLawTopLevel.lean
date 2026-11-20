import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTop

open GlobalTheory.DatumLaw GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

/- English proof (translation)
Unfold `rowLevTop at hg`. Rewrite `hg` using `[if_pos hP]`. Establish `h : g ∈ stabL X.E ((n - 1) + 0) (LocE.lamY P (qOf P) (n - 1) 0 fun i => i + 1)` using `by split_ifs at hg`. Conclude with `hg.1`. Conclude with `hg.1`.

Rewrite `h` using `[GlobalTheory.TopLawSym.lamY_eq]`. Conclude with `h`.
-/
theorem rowLevTop_glint {sharp : Bool} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((n - 1) + 0) ≃ₗ[X.E] Sp X.E ((n - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp n P) : g ∈ GLint X.E (n - 1) P := by
  unfold rowLevTop at hg
  rw [if_pos hP] at hg
  have h : g ∈ stabL X.E ((n - 1) + 0) (LocE.lamY P (qOf P) (n - 1) 0 fun i => i + 1) := by
    split_ifs at hg
    · exact hg.1
    · exact hg.1
  rw [GlobalTheory.TopLawSym.lamY_eq] at h
  exact h

/- English proof (translation)
Take `⟨-, -, -, a4⟩` from `ranks R (j := 0) (by omega)`. Establish `a5` using `r_le_X' R`. Establish `b1 : R.N R.m - 1 + 0 = R.r + (m2 + 1) * R.t + R.t`. Rewrite using `[add_zero, rank_X'_eq R, hm]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `rowLevTop at hg`. Unfold `PhiTop rowChrTop`. Rewrite `hg` using `[if_pos hP]`. Rewrite using `[if_pos hP, if_pos hP]`. Generalize the expression as in `R.N R.m - 1 = n at *`.

Generalize the expression as in `psi0P Ch P = ψ`. Generalize the expression as in `chiP Ch P = χ`. Rewrite using `[hm]`. Use `split_ifs at hg ⊢`. Rewrite using `[DatumLaw.phiGS_eq]`.

Conclude with `phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x`. Rewrite using `[phiG_eq, LocE.lamGB, lamGv_eq]`. Conclude with `phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x`.
-/
theorem phiTop_rowLevTop (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp (R.N R.m) P)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P (g.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rowChrTop Ch mu sharp R.m (R.N R.m) P g.toLinearMap * PhiTop Ch mu sharp m2 P x := by
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  have a5 := r_le_X' R
  have b1 : R.N R.m - 1 + 0 = R.r + (m2 + 1) * R.t + R.t := by
    rw [add_zero, rank_X'_eq R, hm]; ring
  unfold rowLevTop at hg
  unfold PhiTop rowChrTop
  rw [if_pos hP] at hg
  rw [if_pos hP, if_pos hP]
  generalize R.N R.m - 1 = n at *
  generalize psi0P Ch P = ψ
  generalize chiP Ch P = χ
  rw [hm]
  split_ifs at hg ⊢
  · rw [DatumLaw.phiGS_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, LocE.lamGB, lamGv_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x

/- English proof (translation)
Take `⟨g', hg', h1, h2, rfl⟩` from `hg`. Set `j : GLint X.E (R.N R.m - 1) P.1` to `⟨g', rowLevTop_glint hP hg'⟩`. Establish `eg : (extI (N_m_succ R) P.1 j).1 = g`. Use `LinearEquiv.ext fun v => ext_prH (N_m_succ R) ?_ ?_` and prove the remaining obligations. Conclude with `(prH_sumE (N_m_succ R) _ _ _).trans (LinearMap.congr_fun h1 v).symm`.

Use `(sumE_last (N_m_succ R) _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_one, one_mul]`. Conclude with `(atNL_last v).symm.trans ((LinearMap.congr_fun h2 v).symm.trans (atNL_last _))`. Use `⟨extI (N_m_succ R) P.1 j, eg, fun k hk y y' hy' => ?_⟩` and prove the remaining obligations. Establish `e3 : (k⁻¹).1.toLinearMap ∘ₗ y = (k⁻¹ * extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ ((extI (N_m_succ R) P.1 j⁻¹).1.toLinearMap ∘ₗ y)`.

Rewrite using `[map_inv]`. Conclude with `LinearMap.ext fun v => congrArg (k⁻¹).1 (LinearEquiv.apply_symm_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm`. Rewrite using `[e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, hk, inv_mul_cancel]) _ hy', locTop_extI, ← eg]`. Unfold `rhoT`. Rewrite using `[if_pos hP, unitV_det_ext _ (N_m_succ R) j _ rfl]`.

Establish `h3` using `phiTop_rowLevTop (Ch := Ch) (mu := mu) hm cst.sharp hP hg' ((j⁻¹).1.toLinearMap ∘ₗ (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))`. Establish `e4 : g'.toLinearMap ∘ₗ ((j⁻¹).1.toLinearMap ∘ₗ (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) = prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))` using `LinearMap.ext fun v => g'.apply_symm_apply _`. Rewrite `h3` using `[e4]`. Establish `hu : IsUnit (redP P.1 ((LinearEquiv.det j.1 : X.Eˣ) : X.E))`. Rewrite using `[(det_glint j).2, ← redGL_val, ← Matrix.isUnit_iff_isUnit_det]`.

Conclude with `Units.isUnit _`. Establish `h4 : LocE.unitV (chiP Ch P.1 (m2 + 1)) ((LinearEquiv.det g' : X.Eˣ) : X.E) * LocE.unitV (chiP Ch P.1 (m2 + 1))⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = 1`. Rewrite using `[DatumLaw.unitV_eq, DatumLaw.unitV_eq, extendByZeroOffSubset_mul_left_of_mem_lattice]`. Conclude with `mul_inv_cancel₀ (unitCharacterExtendByZero_ne_zero_of_isUnit _ hu)`. Unfold `locTop`.

Rewrite using `[← mul_assoc, mul_right_comm]`. Use `congr 1`. Use `(congrArg (· * _) h3.symm).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, h4, mul_one]`.
-/
theorem locTop_topLev (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hP : P.1 ∈ Pr.vGs) (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (z : X.K) (hg : TopLev Ch sel mu cst R.m P g z) :
    ∃ Gg : GLint X.E (R.N R.m) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N R.m) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
      ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
        z * locTop Ch sel mu cst m2 P ((k⁻¹).1.toLinearMap ∘ₗ y) y' * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
          locTop Ch sel mu cst m2 P y y' := by
  classical
  obtain ⟨g', hg', h1, h2, rfl⟩ := hg
  let j : GLint X.E (R.N R.m - 1) P.1 := ⟨g', rowLevTop_glint hP hg'⟩
  have eg : (extI (N_m_succ R) P.1 j).1 = g := by
    refine LinearEquiv.ext fun v => ext_prH (N_m_succ R) ?_ ?_
    · exact (prH_sumE (N_m_succ R) _ _ _).trans (LinearMap.congr_fun h1 v).symm
    · refine (sumE_last (N_m_succ R) _ _ _).trans ?_
      rw [Units.val_one, one_mul]
      exact (atNL_last v).symm.trans ((LinearMap.congr_fun h2 v).symm.trans (atNL_last _))
  refine ⟨extI (N_m_succ R) P.1 j, eg, fun k hk y y' hy' => ?_⟩
  have e3 : (k⁻¹).1.toLinearMap ∘ₗ y = (k⁻¹ * extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ
      ((extI (N_m_succ R) P.1 j⁻¹).1.toLinearMap ∘ₗ y) := by
    rw [map_inv]
    exact LinearMap.ext fun v => congrArg (k⁻¹).1 (LinearEquiv.apply_symm_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm
  rw [e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, hk, inv_mul_cancel]) _ hy', locTop_extI, ← eg]
  unfold rhoT
  rw [if_pos hP, unitV_det_ext _ (N_m_succ R) j _ rfl]
  have h3 := phiTop_rowLevTop (Ch := Ch) (mu := mu) hm cst.sharp hP hg' ((j⁻¹).1.toLinearMap ∘ₗ
    (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
  have e4 : g'.toLinearMap ∘ₗ ((j⁻¹).1.toLinearMap ∘ₗ
      (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) =
      prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) :=
    LinearMap.ext fun v => g'.apply_symm_apply _
  rw [e4] at h3
  have hu : IsUnit (redP P.1 ((LinearEquiv.det j.1 : X.Eˣ) : X.E)) := by
    rw [(det_glint j).2, ← redGL_val, ← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit _
  have h4 : LocE.unitV (chiP Ch P.1 (m2 + 1)) ((LinearEquiv.det g' : X.Eˣ) : X.E) *
      LocE.unitV (chiP Ch P.1 (m2 + 1))⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = 1 := by
    rw [DatumLaw.unitV_eq, DatumLaw.unitV_eq, extendByZeroOffSubset_mul_left_of_mem_lattice]
    exact mul_inv_cancel₀ (unitCharacterExtendByZero_ne_zero_of_isUnit _ hu)
  unfold locTop
  rw [← mul_assoc, mul_right_comm]
  congr 1
  refine (congrArg (· * _) h3.symm).trans ?_
  rw [mul_assoc, h4, mul_one]

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL P hP`. Establish `hm : R.m = m2 + 1 + 1` using `hL.hm`. Generalize the expression as in `m2 + 1 + 1 = j at hm ⊢`. Substitute `hm` using the available equality. Introduce `g z hg`.

Conclude with `locTop_topLev hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 hP g z hg`.
-/
theorem topF_target_vG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL P hP
  have hm : R.m = m2 + 1 + 1 := hL.hm
  generalize m2 + 1 + 1 = j at hm ⊢
  subst hm
  intro g z hg
  exact locTop_topLev hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 hP g z hg

end GlobalTheory.TwTop

end
