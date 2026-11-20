import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im`. Use function extensionality and compare the values at `w`. Conclude with `Complex.normSq_apply w`. Rewrite using `[h]`. Conclude with `(Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)`.
-/
theorem mulG_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im := by
    funext w; exact Complex.normSq_apply w
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))`. Rewrite using `[iteratedDeriv_eq_iterate]`. Conclude with `ContDiff.iterate_deriv q hφ`. Conclude with `h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))`.
-/
theorem mulG_ld_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiffOn ℝ ∞ (LE.ld q φ) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv q hφ
  exact h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `gR Q.GGl`. Use `ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)` and prove the remaining obligations. Conclude with `contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a`. Conclude with `(Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd`.
-/
theorem mulG_gR_contDiff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    ContDiff ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => gR P Bs x.1 x.2) := by
  unfold gR Q.GGl
  refine ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)
  · exact contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a
  · exact (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd

/- English proof (translation)
The claim follows from `mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2`.
-/
theorem mulG_gR_pos (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Formalism.FourierDecayAlt.P.Qx5.OpR P.k P.r Bs.z Bs.z') : 0 < gR P Bs x.1 x.2 :=
  mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ` and prove the remaining obligations. Use `Complex.ofRealCLM.contDiff.comp_contDiffOn ?_` and prove the remaining obligations. Conclude with `(mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx`. Introduce `x _ h hh h' hh'`. Simplify using `only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']`.
-/
theorem mulG_mem (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ)
    {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ) • Φ c g) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
  refine Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ
  · refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx
  · intro x _ h hh h' hh'
    simp only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']

/- English proof (translation)
Use `⟨fun q => { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩ map_add' := fun Φ Ψ => ?_ map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Simplify using `only [Submodule.coe_add, Pi.add_apply, smul_add]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `c g`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]`. Conclude with `smul_comm _ _ _`.
-/
theorem exists_isMulG_of_smoothLog (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W := by
  refine ⟨fun q =>
    { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩
      map_add' := fun Φ Ψ => ?_
      map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ` and use `exists_isMulG_of_smoothLog P Bs hφ`.
-/
theorem mulG_exists : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W :=
  fun _ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ => exists_isMulG_of_smoothLog P Bs hφ

end GlobalTheory.HatNF
