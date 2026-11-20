import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.CobLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.SigCob
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Use `UpperTheory.V.Cj.cobLin Γ M ρ q (-1) c' c h' h` as an intermediate fact. Rewrite `this` using `[neg_smul, one_smul, neg_add_eq_sub]`. Then use the resulting hypothesis.
-/
private theorem cob_sub {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c - c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q (-1) c' c h' h
  rwa [neg_smul, one_smul, neg_add_eq_sub] at this

/- English proof (translation)
Use `UpperTheory.V.Cj.cobLin Γ M ρ q 1 c c' h h'` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis.
-/
private theorem cob_add {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c + c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q 1 c c' h h'
  rwa [one_smul] at this

/- English proof (translation)
Introduce `E _ _ _ a ha U hU σ Ξ Ξ' h hσ q α β`. Establish `hs` using `UpperTheory.V.Cj.sigCob E a U σ Ξ Ξ' h hσ q`. Use `⟨?_, fun a1 b1 a2 b2 a3 b3 => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a1, b1, c, c', p, p', hc⟩`. Rewrite using `[← perKer E a ha U hU Ξ q α c a1 p, ← perKer E a ha U hU Ξ' q β c' b1 p', ← hs c]`.

Prove the components needed by the constructor for the conclusion. Introduce `k`. Use `cob_add hc k` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `k`.

Use `cob_sub k hc` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Take `⟨c, p⟩` from `(perEx E a U Ξ q).1 α a1 a2`. Take `⟨c', p'⟩` from `(perEx E a U Ξ' q).1 β b1 b2`. Conclude with `⟨a1, b1, c, c', p, p', cob_sub ((perKer E a ha U hU Ξ' q β c' b1 p').2 b3) ((hs c).2 ((perKer E a ha U hU Ξ q α c a1 p).2 a3))⟩`.
-/
theorem UpperTheory.V.Cj.relKer :
    UpperTheory.V.Cj.RelKer := by
  intro E _ _ _ a ha U hU σ Ξ Ξ' h hσ q α β
  have hs := UpperTheory.V.Cj.sigCob E a U σ Ξ Ξ' h hσ q
  refine ⟨?_, fun a1 b1 a2 b2 a3 b3 => ?_⟩
  · rintro ⟨a1, b1, c, c', p, p', hc⟩
    rw [← perKer E a ha U hU Ξ q α c a1 p, ← perKer E a ha U hU Ξ' q β c' b1 p', ← hs c]
    constructor
    · intro k
      have := cob_add hc k
      rwa [sub_add_cancel] at this
    · intro k
      have := cob_sub k hc
      rwa [sub_sub_cancel] at this
  · obtain ⟨c, p⟩ := (perEx E a U Ξ q).1 α a1 a2
    obtain ⟨c', p'⟩ := (perEx E a U Ξ' q).1 β b1 b2
    exact ⟨a1, b1, c, c', p, p', cob_sub ((perKer E a ha U hU Ξ' q β c' b1 p').2 b3)
      ((hs c).2 ((perKer E a ha U hU Ξ q α c a1 p).2 a3))⟩
