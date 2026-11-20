import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.BCT.LocVal

/- English proof (translation)
Establish `key : ∀ u : Pl E, u = w → ∀ f : u.adicCompletion E →+* w.adicCompletion E, Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) → ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧ ∀ k : E, s (algebraMap E _ k) = algebraMap E _ …`. Introduce `u hu f hf hk`. Substitute `hu` using the available equality. Conclude with `⟨f, hf, hk⟩`. Establish `hex` using `key _ ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw) (GlobalTheory.CuspRep.conjLoc (GlobalTheory.SplitPts.conjE E) w) (GlobalTheory.CuspRep.conjLoc_spec _ w).1 (GlobalTheory.CuspRep.conjLoc_spec _ w).2.1`.

Unfold `cj`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec.2 x`.
-/
theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (x : E) :
    cj w (algebraMap E (w.adicCompletion E) x) = algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := by
  have key : ∀ u : Pl E, u = w → ∀ f : u.adicCompletion E →+* w.adicCompletion E, Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ k : E, s (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k) := by
    intro u hu f hf hk
    subst hu
    exact ⟨f, hf, hk⟩
  have hex := key _ ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw) (GlobalTheory.CuspRep.conjLoc (GlobalTheory.SplitPts.conjE E) w)
    (GlobalTheory.CuspRep.conjLoc_spec _ w).1 (GlobalTheory.CuspRep.conjLoc_spec _ w).2.1
  unfold cj
  rw [dif_pos hex]
  exact hex.choose_spec.2 x

/- English proof (translation)
Unfold `UL`. Use `split_ifs with hw`. Conclude with `Subgroup.mem_top _`. Establish `hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val * 1 * (γ : GL (Fin n) E).val = 1` using `γ.2`. Express the relevant statement in the definitionally equal form `cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) * 1 * (algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val = 1`.

Establish `e : cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) = (algebraMap E (w.adicCompletion E)).mapMatrix (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val)`. Use extensionality with `i j`. Simplify using `[cT, Matrix.map_apply, cj_algebraMap w hw]`. Rewrite using `[e, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT _ _), hγ, map_one]`.
-/
theorem map_mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val * 1 * (γ : GL (Fin n) E).val = 1 :=
      γ.2
    change cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) * 1 *
      (algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val = 1
    have e : cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) =
        (algebraMap E (w.adicCompletion E)).mapMatrix
          (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val) := by
      ext i j
      simp [cT, Matrix.map_apply, cj_algebraMap w hw]
    rw [e, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT _ _), hγ, map_one]

/- English proof (translation)
Introduce `E _ _ _ _ n γ w`. Unfold `locPt toSub`. Rewrite using `[dif_pos (map_mem_UL γ w)]`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  intro E _ _ _ _ n γ w
  unfold locPt toSub
  rw [dif_pos (map_mem_UL γ w)]

end GlobalTheory.BCT.LocVal
