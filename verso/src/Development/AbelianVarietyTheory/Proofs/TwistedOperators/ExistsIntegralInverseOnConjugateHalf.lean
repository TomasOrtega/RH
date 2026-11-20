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
Use `first`. Consider the case `exact star_star x`. Consider the case `rfl`. Consider the case `simp [cc]`.
-/
theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩`.
-/
theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

/- English proof (translation)
Introduce `D P e he s hs`. Establish `hee : e * e = e` using `GlobalTheory.PlaceVec.idemSum_mul_self he`. Take `⟨⟨es, hes, rfl⟩, -⟩` from `he`. Distinguish the cases in `hP : P = ∅`. Substitute `hP` using the available equality.

Use `⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Take `⟨tableDegreeThreeBase, hPP0⟩` from `Finset.nonempty_iff_ne_empty.2 hP`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hs tableDegreeThreeBase hPP0 (zero_mem _)`. Establish `hsE : (s : D.host.E) ≠ 0`. Introduce `h; apply hs0; exact RingOfIntegers.ext (by simpa using h)`. Use `⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_mul, map_sum]`.

Use `sum_mem fun PP hPP => ?_` and prove the remaining obligations. Establish `hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0`. Introduce `h0`. Apply `hs0` to reduce the goal to its premises. Rewrite using `[← Formalism.L2.Col.cO_cO s, h0, map_zero]`.

Establish `hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal` using `fun hm => hs PP hPP (mem_conjI_of D _ s hm)`. Establish `hint` using `not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)`. Use `GlobalTheory.MovedIdem.finPart_conj_mem hint` as an intermediate fact. Establish `hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹`. Rewrite using `[star_inv₀]`.

Use `congr 1`. Conclude with `star_star (s : D.host.E)`. Rewrite `this` using `[hst]`. Then use the resulting hypothesis. Establish `h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hsE, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc (cA D _), h1, mul_one, map_mul]`. Use `_ = cA D (∑ PP ∈ P, es PP) := by rw [hee]`.
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
