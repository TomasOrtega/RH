import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmulTopOfEntries
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue`. Consider the case `exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue`. Consider the case `(apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)`.
-/
theorem span_matrix_eq_top_of_residue_span {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (f i).map (IsLocalRing.residue A))) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | (apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)

/- English proof (translation)
The claim follows from `span_matrix_eq_top_of_residue_span (mat ρ) h`.
-/
theorem span_mat_eq_top_of_residue {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  span_matrix_eq_top_of_residue_span (mat ρ) h

end GlobalTheory
