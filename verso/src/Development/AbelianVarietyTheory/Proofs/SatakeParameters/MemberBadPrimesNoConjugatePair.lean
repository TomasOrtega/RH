import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

namespace GlobalTheory.BadNoConj

/- English proof (translation)
Introduce `X Pr sel S mu hX hPr hsel u hT hg`. Establish `hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K)`. Introduce `P`. Unfold `Sall rowSG uSG`. Simplify using `only [Finset.mem_union]`.

The claim follows by propositional logic. Establish `hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K)`. Introduce `P hP hQ`. Take `⟨π, p, hπ, -, hn, hp, hk⟩` from `bad_gen hPr u hP`. Establish `hpS : p ∈ S`.

Break down `hk with ⟨e, -⟩ | ⟨j, e, -⟩` into its components or cases. Rewrite using `[e]`. Conclude with `hT`. Rewrite using `[e]`. Conclude with `hg j`.

Use `qe_nat_notMem mu hsel hp hpS hQ ?_` and prove the remaining obligations. Rewrite using `[mem_conjP, map_natCast]`. Conclude with `hn ▸ P.asIdeal.mul_mem_right _ hπ`. Introduce `P hP hP'`. Apply the tactic sequence `rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'`.

Conclude with `tg_noConj hPr u P h h'`. Conclude with `hmix P h h'`. Conclude with `hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)`. Conclude with `GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'`.
-/
theorem sall_noConj_ok : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr sel S mu hX hPr hsel u hT hg
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto
  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'

end GlobalTheory.BadNoConj
