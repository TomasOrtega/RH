import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOverFinExtOfFiniteInertiaImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePeriodUnramifiedRepStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ P AI T n _ _ K r ρ hρ hfin`. Take `⟨K', hK, hI, hc⟩` from `GlobalTheory.T.unramified_over_finExt_of_finite_inertia_image l n K r ρ hρ hfin`. Set `ι : ↥(GK K') →* ↥(GK K)` to `Subgroup.inclusion (GK_le hK)`. Set `ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)` to `ρ.comp ι`. Establish `hι : Continuous ι` using `continuous_subtype_val.subtype_mk _`.

Establish `hρ' : IsRat r ρ'` using `{ pos := hρ.pos le := fun c hc => hK (hρ.le c hc) rat := fun g i j => hρ.rat (ι g) i j cont := fun i j => (hρ.cont i j).comp hι }`. Take `⟨Q, hQ⟩` from `GlobalTheory.T.exists_crystalline_period_unramified_rep l P AI T n K' r ρ' hρ' (fun g hg => hI g hg) (fun g i j => hc g i j)`. Use `⟨K', hK, Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q, fun g => ?_⟩` and prove the remaining obligations. Establish `h1 : ((Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q : GL n (Bst P)) : Matrix n n (Bst P)) = (Q : Matrix n n P.R.B).map Polynomial.C` using `rfl`. Establish `h2 : ((Q : Matrix n n P.R.B).map Polynomial.C).map (actSt P (g : GQ l)) = ((Q : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P)`.

Rewrite using `[Matrix.map_map, Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Conclude with `actSt_C P _ b`. Establish `h3 : (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) = ((ρ' g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (Polynomial.C : P.R.B →+* Bst P)`.

Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, h3, ← Matrix.map_mul, hQ g]`.
-/
theorem unrStep_holds : UnrStep := by
  intro l _ P AI T n _ _ K r ρ hρ hfin
  obtain ⟨K', hK, hI, hc⟩ := GlobalTheory.T.unramified_over_finExt_of_finite_inertia_image l n K r ρ hρ hfin
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  let ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) := ρ.comp ι
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hρ' : IsRat r ρ' :=
    { pos := hρ.pos
      le := fun c hc => hK (hρ.le c hc)
      rat := fun g i j => hρ.rat (ι g) i j
      cont := fun i j => (hρ.cont i j).comp hι }
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_crystalline_period_unramified_rep l P AI T n K' r ρ' hρ' (fun g hg => hI g hg) (fun g i j => hc g i j)
  refine ⟨K', hK, Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q, fun g => ?_⟩
  have h1 : ((Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q : GL n (Bst P)) :
      Matrix n n (Bst P)) = (Q : Matrix n n P.R.B).map Polynomial.C := rfl
  have h2 : ((Q : Matrix n n P.R.B).map Polynomial.C).map (actSt P (g : GQ l)) =
      ((Q : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext b
    exact actSt_C P _ b
  have h3 : (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) =
      ((ρ' g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map]
    rfl
  rw [h1, h2, h3, ← Matrix.map_mul, hQ g]

end GlobalTheory.PMon

end
