import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement

open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Introduce `l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb`. Establish `hNl : Nat.Coprime N l` using `((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm`. Take `⟨φ, h1, h2⟩` from `X.j_hol`. Use `⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1`.

Express the relevant statement in the definitionally equal form `X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h`. Rewrite using `[← h, hb.2 d hd, map_smul]`.
-/
theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
