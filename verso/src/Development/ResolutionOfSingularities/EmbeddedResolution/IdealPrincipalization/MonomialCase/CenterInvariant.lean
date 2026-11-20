import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def sortedIndices {n : ℕ} (J : Finset (Fin n)) : List ℕ :=
  (J.sort (· ≤ ·)).map Fin.val

/- English proof (authored)
By definition, the list of indices is obtained by sorting the finite set in increasing order and then taking the natural-number value of each index.
-/
theorem sortedIndices_eq_map_sort {n : ℕ} (J : Finset (Fin n)) :
    sortedIndices J = (J.sort (· ≤ ·)).map Fin.val := rfl

/- English proof (authored)
An entry of the sorted list is the natural-number value of a member of the original finite set. Sorting retains every member, so any such value also occurs in the list.
-/
theorem mem_sortedIndices {n : ℕ} (J : Finset (Fin n)) (a : ℕ) :
    a ∈ sortedIndices J ↔ ∃ j ∈ J, (j : ℕ) = a := by
  simp [sortedIndices, List.mem_map, Finset.mem_sort]

structure CenterInvariant (n : ℕ) : Type where
  positions : Finset (Fin n)
  rank : ℕ
  value : ℕ∞

def CenterInvariant.sortedIndices {n : ℕ} (K : CenterInvariant n) : List ℕ :=
  _root_.FunctorialResolution.EmbeddedResolution.MonomialCenter.sortedIndices K.positions

def CenterInvariant.Lt {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.rank < K'.rank ∨
    (K.rank = K'.rank ∧
      (K'.value < K.value ∨
        (K.value = K'.value ∧
          List.Lex (· < ·) K.sortedIndices K'.sortedIndices)))

def CenterInvariant.Le {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.Lt K' ∨
    (K.rank = K'.rank ∧ K.value = K'.value ∧ K.sortedIndices = K'.sortedIndices)

def centerInvariant {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    CenterInvariant L.length where
  positions := lexMaxIndices I m L
  rank := minIndexCard I m L
  value := maxCandidateOrder I m L

/- English proof (authored)
The selected position set is defined to be the index set obtained by maximizing the binary code among the candidates of the chosen size and order.
-/
@[simp] theorem centerInvariant_indices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).positions = lexMaxIndices I m L := rfl

/- English proof (authored)
The rank field is filled with the smallest positive size of an index set supporting a candidate component, as given by the minimum-size function.
-/
@[simp] theorem centerInvariant_depth {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).rank = minIndexCard I m L := rfl

/- English proof (authored)
The order field is filled with the supremum of the orders of candidate components among index sets of the chosen minimum size.
-/
@[simp] theorem centerInvariant_order {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).value = maxCandidateOrder I m L := rfl

/- English proof (authored)
The sorted list of an invariant is the sorted list of its position set. For this invariant that position set is the selected set of indices.
-/
@[simp] theorem centerInvariant_sortedIndices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    (centerInvariant I m L).sortedIndices = sortedIndices (lexMaxIndices I m L) := rfl

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
