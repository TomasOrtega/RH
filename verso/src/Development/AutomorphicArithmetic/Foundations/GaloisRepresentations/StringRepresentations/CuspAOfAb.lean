import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.WeilDeligne UpperTheory.Lit.Car

namespace UpperTheory.GalN

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Aw.dim {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) :
    x.lpDim = y.lpDim := by rw [← WD.charPol_natDegree x 1, k.pol, WD.charPol_natDegree]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem spl_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (c : G H.E N.Om → ℂ) (t : ℕ) (y : A.LP w) :
    Spl N A c t y ↔ SplW c t (T.e w y) := by
  constructor
  · rintro ⟨a, b, e, d, m, p⟩
    exact ⟨T.e w a, T.e w b, by rw [e, T.sum], by rw [T.dim, d], (T.mono0 w b).1 m,
      fun σ hσ => by rw [← T.inePol w b σ hσ, p σ hσ]⟩
  · rintro ⟨a, b, e, d, m, p⟩
    obtain ⟨a, rfl⟩ := (T.e w).surjective a
    obtain ⟨b, rfl⟩ := (T.e w).surjective b
    exact ⟨a, b, (T.e w).injective (by rw [e, T.sum]), by rw [← T.dim, d], (T.mono0 w b).2 m,
      fun σ hσ => by rw [T.inePol w b σ hσ, p σ hσ]⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem relW_of_aw (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Aw (T.e w x) (T.e w y)) : RelW N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], fun σ hσ => ?_, fun m => (T.e w).injective (h.n0 ((T.mono0 w y).1 m)),
    fun u c t γ hγ hm hs => ?_⟩
  · rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, h.pol]
  · rw [spl_iff T, T.sum] at hs ⊢
    rw [T.inePol _ _ γ hγ, T.sum] at hm
    exact h.spl _ c t γ hγ hm hs

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem relA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Ab (T.e w x) (T.e w y)) : RelA N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], by rw [T.mono0, T.mono0]; exact h.mono, fun hy σ hσ => ?_⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ]
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  refine h.ine ((T.mono0 _ _).1 hy.1) (fun g hg => ?_) _ (deg_ineIncl _)
  have e := hy.2 g hg
  rw [T.inePol _ _ _ (comm_le_ine w hg), WD.inePol_of_mem _ g.2, ← T.dim] at e
  exact e

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : Ab (T.e w x) (T.e w y)) : CuspA N A x y := ⟨relA_of_ab T h, fun e => absurd e h1⟩

end UpperTheory.GalN
