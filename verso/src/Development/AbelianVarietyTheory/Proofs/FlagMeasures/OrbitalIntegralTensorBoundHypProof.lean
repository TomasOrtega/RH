import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PackageTie

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions

namespace GlobalTheory.TensHS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`.
-/
theorem hsNormSq_eq_sum_std {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/- English proof (translation)
Take `⟨hon, hsp⟩` from `Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'`. Set `B` to `OrthonormalBasis.mk hon hsp`. Establish `hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v))` using `fun i => by simp [B]`. Rewrite using `[hsNormSq_eq_sum_std]`. Simplify using `only [hsNormSq_eq_sum_std]`.

Unfold `Formalism.L2.SG.RealObj.hs2`. Rewrite using `[Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]`. Simplify using `only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]`. Rewrite using `[Fintype.prod_sum]`.
-/
theorem hsNormSq_of_tens {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (A : X.Vpi u' →L[ℂ] X.Vpi u) (J : ∀ v, X.Vloc u' v →L[ℂ] X.Vloc u v)
    (hA : ∀ y, A (X.tensU u' y) = X.tensU u (fun v => J v (y v))) :
    Formalism.MainNotions.S.hsNormSq A = ∏ v, Formalism.MainNotions.S.hsNormSq (J v) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  rw [hsNormSq_eq_sum_std]
  simp only [hsNormSq_eq_sum_std]
  unfold Formalism.L2.SG.RealObj.hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

/- English proof (translation)
Rewrite using `[hsNormSq_eq_sum_std]`. Conclude with `Finset.sum_nonneg fun i _ => sq_nonneg _`.
-/
theorem hsNormSq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ Formalism.MainNotions.S.hsNormSq A := by
  rw [hsNormSq_eq_sum_std]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/- English proof (translation)
Introduce `D X u γ νl hσ`. Use `haveI := FiniteDimensional.complete ℂ (X.Vpi u)`. Use `haveI : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ (X.Vloc u v)`. Use `haveI := hσ`. Establish `hWc : Continuous (X.Wu u)` using `(X.Wu_spec u).2.2.1`.

Establish `hfac : ∀ y, (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ) (X.tensU u y) = X.tensU u (fun v => (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) (y v))`. Introduce `y`. Establish `h` using `Formalism.L2.SG.RealObj.RankOneTensors.oo_factor νl (X.tensU u) (X.tensU u) (X.tensU_inner u) (X.tensU_inner u) (X.tensU_span u) (X.Wloc u) (X.Wloc u) (X.Wloc_cont u) (X.Wloc_cont u) (X.Wu u) (X.Wu u) hWc hWc (X.Wu_tens u) (X.Wu_tens u) γ y`. Simplify `h` using `only [Formalism.L2.SG.RealObj.Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ]`. Establish `hhs` using `hsNormSq_of_tens X u u _ _ hfac`.

Establish `hn` using `Formalism.L2.SG.PackageTie.norm_hsEmb_sq (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ)`. Use `le_of_eq ?_` and prove the remaining obligations. Rewrite using `[← Real.sqrt_sq (norm_nonneg _), hn, hhs]`. Establish `hprod : ∏ v, Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) = (∏ v, Real.sqrt (Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)))) ^ 2`. Rewrite using `[← Finset.prod_pow]`.

Conclude with `Finset.prod_congr rfl fun v _ => (Real.sq_sqrt (hsNormSq_nonneg _)).symm`. Rewrite using `[hprod, Real.sqrt_sq (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)]`.
-/
theorem tensC_holds : GlobalTheory.TypeAsm.TensC := by
  intro D X u γ νl hσ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := hσ
  have hWc : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hfac : ∀ y, (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ) (X.tensU u y) =
      X.tensU u (fun v => (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) (y v)) := by
    intro y
    have h := Formalism.L2.SG.RealObj.RankOneTensors.oo_factor νl (X.tensU u) (X.tensU u) (X.tensU_inner u)
      (X.tensU_inner u) (X.tensU_span u) (X.Wloc u) (X.Wloc u) (X.Wloc_cont u) (X.Wloc_cont u)
      (X.Wu u) (X.Wu u) hWc hWc (X.Wu_tens u) (X.Wu_tens u) γ y
    simpa only [Formalism.L2.SG.RealObj.Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ] using h
  have hhs := hsNormSq_of_tens X u u _ _ hfac
  have hn := Formalism.L2.SG.PackageTie.norm_hsEmb_sq
    (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ)
  refine le_of_eq ?_
  rw [← Real.sqrt_sq (norm_nonneg _), hn, hhs]
  have hprod : ∏ v, Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) =
      (∏ v, Real.sqrt (Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)))) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => (Real.sq_sqrt (hsNormSq_nonneg _)).symm
  rw [hprod, Real.sqrt_sq (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)]

end GlobalTheory.TensHS
