import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem base_ainf_φ (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  BaseC.ainf_φ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem base_ainf_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  BaseC.ainf_σ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem base_ainf_plus (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, ι l x ∈ Plus l :=
  BaseC.ainf_plus

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem base_ainf_eig (l : ℕ) [Fact l.Prime] :
    ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0 :=
  fun h m hm x hx he => BaseC.ainf_eig h m hm x hx he

end period_ring_base
