import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `: IsGalois E Ω` using `{}`. Establish `: CompactSpace (G E Ω)` using `inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))`. Take `⟨K', _, _, _, X, hX, hroots⟩` from `hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)`.

Set `T : G E Ω → (Qbar l)[X] → Prop` to `fun g Q => Q.Monic ∧ Q.natDegree = a ∧ aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧ ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0`. Set `P : G E Ω → (Qbar l)[X]` to `fun g => if h : ∃ Q, T g Q then h.choose else 1`. Establish `hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s)`. Introduce `s hs`. Establish `e : P s = (show ∃ Q, T s Q from hs).choose` using `dif_pos hs`.

Rewrite using `[e]`. Conclude with `(show ∃ Q, T s Q from hs).choose_spec`. Establish `hss' : IsSSMat ρ`. Introduce `W hW`. Take `⟨W', h1, h2⟩` from `hss W hW`.

Conclude with `⟨W', h2, h1⟩`. Take `⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩` from `hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss' {g : G E Ω | ∃ Q, T g Q} hD P (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1) X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)`. Use `⟨r, ?_, ?_, hin, hco, hopen, hdense⟩` and prove the remaining obligations. Use `Units.continuous_iff.mpr ⟨hrc, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`.

Conclude with `hrc.comp continuous_inv`. Introduce `W hW`. Take `⟨W', h1, h2⟩` from `hrss W hW`. Conclude with `⟨W', h2, h1⟩`.
-/
theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
