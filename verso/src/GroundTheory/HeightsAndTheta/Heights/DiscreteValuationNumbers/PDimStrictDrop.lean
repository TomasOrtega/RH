import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Introduce `A _ Q Q' _ _ hlt`. Set `q : PrimeSpectrum.zeroLocus (R` to `A) (Q : Set A) := ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩`. Establish `: Nonempty (PrimeSpectrum.zeroLocus (R` using `A) (Q' : Set A)) := ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩`. Establish `: Nonempty (PrimeSpectrum.zeroLocus (R` using `A) (Q : Set A)) := ⟨q⟩`. Set `f : PrimeSpectrum.zeroLocus (R` to `A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) := fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩`.

Establish `hf : StrictMono f` using `fun a b h => h`. Rewrite using `[ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]`. Introduce `l`. Establish `hq : q < f l.head` using `by show Q < (l.head.1.asIdeal)`. Conclude with `lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)`.

Use `le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))` and prove the remaining obligations. Establish `hlen : ((l.map f hf).cons q hq).length = l.length + 1`. Simplify using `[RelSeries.cons_length, LTSeries.map]`. Rewrite using `[hlen]`. Simplify using the standard rewrite rules.
-/
theorem DimStrictDrop.proof : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp

end GroundTheory.Heights₂.Heights.NumbersDVR
