import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n hC π`. Proceed by induction on `π using Quotient.inductionOn with | _ π => ?_`. Introduce `hπ σ`. Take `⟨π', τ, τ', h1, h2, h3, -⟩` from `hC π hπ σ`. Take `⟨hs, hs'⟩` from `sep_of_conj h1 h2 h3`.

Conclude with `⟨CG.mk π', fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩`.
-/
theorem UpperTheory.V.Cj.satConj :
    UpperTheory.V.Cj.SatConj := by
  intro E _ _ _ n hC π
  induction π using Quotient.inductionOn with | _ π => ?_
  intro hπ σ
  obtain ⟨π', τ, τ', h1, h2, h3, -⟩ := hC π hπ σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  exact ⟨CG.mk π', fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
