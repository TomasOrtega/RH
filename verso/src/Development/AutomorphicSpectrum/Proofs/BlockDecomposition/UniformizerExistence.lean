import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalUnif

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F)` using `⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩`. Conclude with `hv.isUnit_iff_valuation_eq_one`.
-/
theorem isUnit_iff_valued_eq_one (x : v.adicCompletionIntegers F) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
    ⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  exact hv.isUnit_iff_valuation_eq_one

/- English proof (translation)
Rewrite using `[isUnit_iff_valued_eq_one, Valued.toNormedField.norm_lt_one_iff]`. Establish `h` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2`. Conclude with `⟨ne_of_lt, fun h' => lt_of_le_of_ne h h'⟩`.
-/
theorem norm_lt_one_iff_not_isUnit (x : v.adicCompletionIntegers F) :
    ‖(x : v.adicCompletion F)‖ < 1 ↔ ¬ IsUnit x := by
  rw [isUnit_iff_valued_eq_one, Valued.toNormedField.norm_lt_one_iff]
  have h := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  exact ⟨ne_of_lt, fun h' => lt_of_le_of_ne h h'⟩

/- English proof (translation)
Rewrite using `[← hϖ.maximalIdeal_eq]`. Conclude with `GroundTheory.Global.natCard_residueField_adicCompletionIntegers v`.
-/
theorem natCard_quotient_span_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  rw [← hϖ.maximalIdeal_eq]
  exact GroundTheory.Global.natCard_residueField_adicCompletionIntegers v

/- English proof (translation)
Unfold `PositivityTheory.SiegelWeilFormula.Gunr.UnifEx`. Introduce `F _ _ v`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)`. Use `⟨ϖ, ?_, ?_, ?_, natCard_quotient_span_irreducible v hϖ⟩` and prove the remaining obligations. Introduce `h`.

Conclude with `hϖ.ne_zero (Subtype.ext h)`. Conclude with `(norm_lt_one_iff_not_isUnit v ϖ).2 hϖ.not_isUnit`. Introduce `x hx`. Establish `hm : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)` using `(IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 ((norm_lt_one_iff_not_isUnit v x).1 hx))`. Rewrite `hm` using `[hϖ.maximalIdeal_eq]`.

Conclude with `Ideal.mem_span_singleton.1 hm`.
-/
theorem unifEx : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.UnifEx
  intro F _ _ v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  refine ⟨ϖ, ?_, ?_, ?_, natCard_quotient_span_irreducible v hϖ⟩
  · intro h
    exact hϖ.ne_zero (Subtype.ext h)
  · exact (norm_lt_one_iff_not_isUnit v ϖ).2 hϖ.not_isUnit
  · intro x hx
    have hm : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 ((norm_lt_one_iff_not_isUnit v x).1 hx))
    rw [hϖ.maximalIdeal_eq] at hm
    exact Ideal.mem_span_singleton.1 hm

end GlobalTheory.CompanionTheory.LocalUnif

end
