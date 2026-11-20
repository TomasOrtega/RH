import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

/- English proof (translation)
Introduce and unpack `⟨ha, hma⟩ ⟨hb, hmb⟩`. Use `⟨(grpAt S P).mul_mem ha hb, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P`. Introduce `i`.

Establish `: (mt S b *ᵥ y) i = ∑ j, mt S b i j * y j` using `rfl`. Rewrite using `[this]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)`. Establish `hmul : mt S (a * b) = mt S a * mt S b` using `rfl`. Rewrite using `[hmul, ← Matrix.mulVec_mulVec]`.

Conclude with `(hmb y hy).trans (hma _ hy')`.
-/
theorem inK_mul {D : D7} (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S) :
    InK S L P a → InK S L P b → InK S L P (a * b) := by
  rintro ⟨ha, hma⟩ ⟨hb, hmb⟩
  refine ⟨(grpAt S P).mul_mem ha hb, ?_⟩
  intro y hy
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := by
    intro i
    have : (mt S b *ᵥ y) i = ∑ j, mt S b i j * y j := rfl
    rw [this]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hmul : mt S (a * b) = mt S a * mt S b := rfl
  rw [hmul, ← Matrix.mulVec_mulVec]
  exact (hmb y hy).trans (hma _ hy')

end GlobalTheory.FinPl
