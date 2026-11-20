import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `hinf : cInf g = 1` using `MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1`. Use `ga_ext (hinf.trans (pInf_finGL k).symm) ?_` and prove the remaining obligations. Rewrite using `[pFin_finGL]`. Use `Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)` and prove the remaining obligations. Conclude with `congrArg Units.val (hk u)`.
-/
private theorem eq_finGL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (k : GL (Fin n) (Af E))
    (hk : ∀ u, cLoc u g = Matrix.GeneralLinearGroup.map (pLoc E u) k) : (g : GA E n) = finGL E n k := by
  have hinf : cInf g = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1
  refine ga_ext (hinf.trans (pInf_finGL k).symm) ?_
  rw [pFin_finGL]
  refine Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)
  exact congrArg Units.val (hk u)

/- English proof (translation)
The claim follows from `MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)`.
-/
private theorem cLoc_off {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w u : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (hu : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    cLoc u g = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)

/- English proof (translation)
Introduce `E _ _ _ n ν hν w g hg`. Use `⟨fun hw => ?_, fun hw => ?_⟩` and prove the remaining obligations. Take `⟨hne, hun, hover⟩` from `GlobalTheory.SplitPts.over_split hw set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'`. Establish `e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g))`. Use `eq_finGL hg _ fun u => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `h1 : u = w`. Rewrite using `[h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]`. Distinguish the cases in `h2 : u = w'`. Rewrite using `[h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]`.

Rewrite using `[pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]`. Conclude with `cLoc_off hg fun h => (hover u h).elim h1 h2`. Establish `hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) = (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹`. Use `eq_inv_of_mul_eq_one_left (Units.ext ?_)` and prove the remaining obligations. Establish `h` using `congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)`.

Rewrite `h` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]`. Use `Eq.trans ?_ h` and prove the remaining obligations. Conclude with `congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)`. Establish `h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g)`. Express the relevant statement in the definitionally equal form `ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) = ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))`.

Establish `h3` using `GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))`. Rewrite `h3` using `[hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv]`. Conclude with `h3`. Rewrite using `[e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]`. Both sides reduce to the same expression.

Establish `e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g))`. Use `eq_finGL hg _ fun u => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : u = w`. Rewrite using `[h1, pLoc_locGL]`. Rewrite using `[pLoc_locGL_of_ne h1]`.

Conclude with `cLoc_off hg fun h => hw ⟨u, h1, h⟩`. Rewrite using `[e, CuspSub.chiDet_locGL]`.
-/
theorem UpperTheory.detCharacter_eq_localDet_split_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E), GlobalTheory.ThetaPull.thetaChar ν = ν → ∀ (w : Plc E), ∀ g ∈ locU n w, (IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n (ν * ν) w (cLoc w g)) ∧ (¬ IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n ν w (cLoc w g)) := by
  intro E _ _ _ n ν hν w g hg
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨hne, hun, hover⟩ := GlobalTheory.SplitPts.over_split hw
    set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'
    have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g)) := by
      refine eq_finGL hg _ fun u => ?_
      rw [map_mul]
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]
      · by_cases h2 : u = w'
        · rw [h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]
        · rw [pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]
          exact cLoc_off hg fun h => (hover u h).elim h1 h2
    have hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) =
        (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      have h := congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      refine Eq.trans ?_ h
      exact congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)
    have h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g) := by
      change ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) =
        ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))
      have h3 := GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))
      rw [hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv] at h3
      exact h3
    rw [e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]
    rfl
  · have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g)) := by
      refine eq_finGL hg _ fun u => ?_
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL]
      · rw [pLoc_locGL_of_ne h1]
        exact cLoc_off hg fun h => hw ⟨u, h1, h⟩
    rw [e, CuspSub.chiDet_locGL]
