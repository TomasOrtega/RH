import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem primeProd_conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (I : Ideal (𝓞 E)) :
    conjI I = I.map (RingOfIntegers.mapRingHom ((IsCMField.complexConj E).toRingEquiv.toRingHom)) := by
  unfold conjI
  show _ = Ideal.span _
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem primeProd_squarefree_le_conj : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), Squarefree (∏ PP ∈ P, PP.asIdeal) ∧ (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (∏ PP ∈ P, PP.asIdeal) ≤ PP'.asIdeal ↔ PP' ∈ P) ∧ conjI (∏ PP ∈ P, PP.asIdeal) = ∏ PP ∈ P, conjI PP.asIdeal := by
  intro D P
  refine ⟨?_, ?_, ?_⟩
  · have hprod : (∏ PP ∈ P, PP.asIdeal) = (P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal)).prod := by
      rw [Finset.prod_eq_multiset_prod]
    have hprime : ∀ p ∈ P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal), Prime p := by
      intro p hp
      obtain ⟨PP, -, rfl⟩ := Multiset.mem_map.1 hp
      exact PP.prime
    have hne : (∏ PP ∈ P, PP.asIdeal) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro PP _
      exact PP.ne_bot
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne, hprod,
      UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime]
    exact (Multiset.nodup_map_iff_of_injective (fun a b h => HeightOneSpectrum.ext h)).2 P.nodup
  · intro PP'
    constructor
    · intro hle
      obtain ⟨PP, hPP, hle'⟩ := (Ideal.IsPrime.prod_le PP'.isPrime).1 hle
      have : PP.asIdeal = PP'.asIdeal := PP.isMaximal.eq_of_le PP'.isPrime.ne_top hle'
      have h2 : PP = PP' := HeightOneSpectrum.ext this
      exact h2 ▸ hPP
    · intro h
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ h)
  · simp only [primeProd_conjI_eq_map]
    exact map_prod (Ideal.mapHom _) _ _

end GlobalTheory
