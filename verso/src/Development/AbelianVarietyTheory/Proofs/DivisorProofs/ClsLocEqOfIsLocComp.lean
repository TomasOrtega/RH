import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

/- English proof (translation)
Establish `h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ)` using `hσ`. Rewrite using `[locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]`. Both sides reduce to the same expression.
-/
theorem locParT_eq_of_isLocComp (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

/- English proof (translation)
Establish `h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ)` using `hσ`. Rewrite using `[CG.IsLoc.unique E a _ w _ _ h1.loc h1]`. Both sides reduce to the same expression.
-/
theorem cls_loc_eq_of_isLocComp {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    (⟨a, ParLaws.toCl ((CG.mk π).loc w)⟩ : IrrGL (w.adicCompletion E)) = cls (ParLaws.toRep σ) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

/- English proof (translation)
The claim follows from `locParT_eq_of_isLocComp hT (CG.isLoc_ofChar χ w) h`.
-/
theorem locParT_ofChar_eq (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    locParT hT (CG.ofChar χ) h = locRecT hT h (.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w)) :=
  locParT_eq_of_isLocComp hT (CG.isLoc_ofChar χ w) h

end GlobalTheory.CuspRep.ParLawsT

/- English proof (translation)
Introduce `hF hT E Ω _ _ _ _ _ _ A w a π χ h hg`. Proceed by induction on `π using Quotient.inductionOn with | _ π =>`. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Take `⟨_, _, H⟩` from `isRecT_locRecT hT h`. Establish `hg' : UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ))` using `cls_loc_eq_of_isLocComp hσ ▸ hg`.

Use `(locParT_eq_of_isLocComp hT (hσ.twist χ) h).trans ?_` and prove the remaining obligations. Rewrite using `[locParT_ofChar_eq, show locParT hT (Quotient.mk _ π) h = _ from locParT_eq_of_isLocComp hT hσ h, ← H.twist _ _ _ hg']`. Conclude with `congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm`.
-/
theorem GlobalTheory.CuspRep.ParLawsT.locParT_twist : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w), UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E)) → locParT hT (π.twist χ) h = (locParT hT π h).lpChar (locParT hT (CG.ofChar χ) h) := by
  intro hF hT E Ω _ _ _ _ _ _ A w a π χ h hg
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  have hg' : UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ)) := cls_loc_eq_of_isLocComp hσ ▸ hg
  refine (locParT_eq_of_isLocComp hT (hσ.twist χ) h).trans ?_
  rw [locParT_ofChar_eq, show locParT hT (Quotient.mk _ π) h = _ from locParT_eq_of_isLocComp hT hσ h, ← H.twist _ _ _ hg']
  exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end
