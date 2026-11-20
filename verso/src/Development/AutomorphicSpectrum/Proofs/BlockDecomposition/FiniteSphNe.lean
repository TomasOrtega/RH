import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Function
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitaryWord

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.U

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev unitFn (n : ℕ) (w : Pl E) : UL n w → ℂ := (KL n w : Set (UL n w)).indicator 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩`.
-/
theorem isHecke_zero {w : Pl E} (K' : Subgroup (UL n w)) : IsHecke K' (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

/- English proof (translation)
The claim follows from `(hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1`.
-/
theorem isHecke_lone (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    IsHecke K' (lone K') :=
  (hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1

/- English proof (translation)
The claim follows from `(hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1`.
-/
theorem isHecke_lconv (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {f₁ f₂ : UL n w → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) : IsHecke K' (lconv f₁ f₂) :=
  (hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1

/- English proof (translation)
Simplify using `[lone, unitFn, Subgroup.relIndex_self]`. Both sides reduce to the same expression.
-/
theorem lone_KL (w : Pl E) : lone (KL n w) = unitFn n w := by
  simp [lone, unitFn, Subgroup.relIndex_self]
  rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact isHecke_lone hL hK`. Consider the case `succ k ih => exact isHecke_lconv hL hK hg ih`.
-/
theorem isHecke_lpow (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (lpow K' g k) := by
  induction k with
  | zero => exact isHecke_lone hL hK
  | succ k ih => exact isHecke_lconv hL hK hg ih

section Fam

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  (F : UFam S lam K') {B : Finset (Pl E)}

end Fam

end GlobalTheory.CompanionTheory.UnitaryWord

end
