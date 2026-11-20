import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSectionsStatement

set_option autoImplicit false

namespace GlobalTheory.HSShort

/- English proof (translation)
Introduce `F _ _ T hg hb δ f hf`. Take `⟨hδ, Q, hQ, hs⟩` from `h F T hg hb δ f hf`. Conclude with `⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩`.
-/
theorem bertiniNF_of_bertini (h : Bertini) : BertiniNF := by
  intro F _ _ T hg hb δ f hf
  obtain ⟨hδ, Q, hQ, hs⟩ := h F T hg hb δ f hf
  exact ⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩

/- English proof (translation)
Introduce `hq` and use `bertiniNF_of_bertini (GlobalTheory.T.bertini_simple_zeros_generic_sections hq)`.
-/
theorem bertiniNumberField_of_hilbertSamuel : GlobalTheory.HSCore.Quoted → BertiniNF :=
  fun hq => bertiniNF_of_bertini (GlobalTheory.T.bertini_simple_zeros_generic_sections hq)

end GlobalTheory.HSShort
