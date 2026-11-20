import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.HalfUnit

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_int_inv_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) →
    ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  intro D P e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hP : P = ∅
  · subst hP
    refine ⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩
    simp
  obtain ⟨tableDegreeThreeBase, hPP0⟩ := Finset.nonempty_iff_ne_empty.2 hP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs tableDegreeThreeBase hPP0 (zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by
    intro h; apply hs0; exact RingOfIntegers.ext (by simpa using h)
  refine ⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩
  · rw [map_sum, Finset.sum_mul, map_sum]
    refine sum_mem fun PP hPP => ?_
    have hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0 := by
      intro h0; apply hs0
      rw [← Formalism.L2.Col.cO_cO s, h0, map_zero]
    have hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal := fun hm => hs PP hPP (mem_conjI_of D _ s hm)
    have hint := not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)
    have := GlobalTheory.MovedIdem.finPart_conj_mem hint
    have hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_star (s : D.host.E)
    rwa [hst] at this
  · have h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hsE, map_one]
    calc cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) * cA D (∑ PP ∈ P, es PP)
        = cA D ((∑ PP ∈ P, es PP) * (∑ PP ∈ P, es PP)) := by
          rw [mul_assoc (cA D _), h1, mul_one, map_mul]
      _ = cA D (∑ PP ∈ P, es PP) := by rw [hee]

end GlobalTheory.HalfUnit
