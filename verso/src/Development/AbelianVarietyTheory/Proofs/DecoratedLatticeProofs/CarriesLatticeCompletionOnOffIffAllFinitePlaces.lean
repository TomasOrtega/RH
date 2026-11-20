import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesSplit

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem idem_eq_algebraMap (R : Pl D → Prop) :
    idem D R = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ePl D R)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idem_smul_mem (S : HSp D) (L : Lat S) {P : Pl D → Prop} (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : idem D R • y ∈ latV S L (fun p => P p ∧ R p) := by
  classical
  rw [idem_eq_algebraMap]
  exact smul_mem_latV S L (ePl D R) (ePl_int R) (fun v hv => by rw [evalV_ePl, if_neg hv]) hy

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idem_smul_eq (S : HSp D) (R : Pl D → Prop) {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D R) :
    idem D R • y = y :=
  funext fun i => (mem_idAt_iff R (y i)).1 (hy i)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_latV_iff_all (S : HSp D) (L : Lat S) (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D R) : y ∈ latV S L R ↔ y ∈ latV S L (fun _ => True) := by
  refine ⟨fun h => latV_mono S L (fun _ _ => trivial) h, fun h => ?_⟩
  have h1 := idem_smul_mem S L R h
  rw [idem_smul_eq S R hy] at h1
  exact latV_mono S L (fun _ h => h.2) h1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem idem_add_idem (P : Pl D → Prop) {a : AE D} (ha : a ∈ idAt D (fun _ => True)) :
    idem D P * a + idem D (fun p => ¬ P p) * a = a := by
  classical
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, infPart_of_idAt ha, mul_zero, mul_zero, add_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, compAt_idem, compAt_idem]
    by_cases h : P w
    · simp [h]
    · simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_latV_iff_parts (S : HSp D) (L : Lat S) (P : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (fun _ => True)) :
    y ∈ latV S L (fun _ => True) ↔
      idem D (fun p => ¬ P p) • y ∈ latV S L (fun p => ¬ P p) ∧ idem D P • y ∈ latV S L P := by
  constructor
  · intro h
    exact ⟨latV_mono S L (fun _ h => h.2) (idem_smul_mem S L _ h), latV_mono S L (fun _ h => h.2) (idem_smul_mem S L P h)⟩
  · rintro ⟨h1, h2⟩
    have e : y = idem D P • y + idem D (fun p => ¬ P p) • y :=
      funext fun i => (idem_add_idem P (hy i)).symm
    rw [e]
    exact add_mem (latV_mono S L (fun _ _ => trivial) h2) (latV_mono S L (fun _ _ => trivial) h1)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idem_smul_supp (S : HSp D) (R : Pl D → Prop) (y : Fin S.rank → AE D) (i : Fin S.rank) :
    (idem D R • y) i ∈ idAt D R :=
  Ideal.mul_mem_right _ _ (idem_mem_idAt R)

end GlobalTheory.FinPl.MovesSplit

open GlobalTheory.FinPl.MovesSplit GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GlobalTheory.FinPl.moves_iff_moves_on_off : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S)
    (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔
      GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  intro D S g L P
  constructor
  · rintro ⟨hn, hp⟩ y hy
    rw [mem_latV_iff_parts S L P hy, mem_latV_iff_parts S L P (mulVec_mem S _ hy), ← Matrix.mulVec_smul,
      ← Matrix.mulVec_smul]
    exact and_congr (hn _ (idem_smul_supp S _ y)) (hp _ (idem_smul_supp S P y))
  · intro h
    have key : ∀ R : GlobalTheory.FinPl.Pl D → Prop, GlobalTheory.FinPl.Moves S g L L R := by
      intro R y hy
      rw [mem_latV_iff_all S L R hy, mem_latV_iff_all S L R (mulVec_mem S _ hy)]
      exact h y fun i => idAt_mono (fun _ _ => trivial) (hy i)
    exact ⟨key _, key _⟩

end
