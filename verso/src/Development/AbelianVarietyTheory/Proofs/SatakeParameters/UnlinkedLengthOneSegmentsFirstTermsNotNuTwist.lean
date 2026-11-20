import Mathlib
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedFirst

/- English proof (translation)
Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem single_linked_single_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ρ ρ' : IrrGL k} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (he : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst he
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unlinked_first_of_len_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc c Δ hlen hun
  obtain ⟨a, ha, L⟩ := hrc
  intro y hy z hz hyz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  have hne : (Δ j).first ≠ (Δ j).first.nu 1 := by
    intro e0
    refine GlobalTheory.UnlinkedMono.lpTw_one_ne (rc (Δ j).first) (by rw [L.dim]; exact (Δ j).isCusp_first.1) ?_
    calc (rc (Δ j).first).lpTw 1 = rc ((Δ j).first.nu ((1 : ℝ) : ℂ)) := (L.nu _ 1).symm
      _ = rc (Δ j).first := by rw [Complex.ofReal_one, ← e0]
  have eΔ : ∀ k, Δ k = Segment.single (Δ k).first (Δ k).isCusp_first := fun k =>
    Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, hlen k])
  by_cases hij : j = i
  · subst hij; exact hne hyz
  exact hun j i hij (by
    rw [eΔ j, eΔ i]
    exact single_linked_single_nu (Δ j).isCusp_first (Δ i).isCusp_first hne hyz)

end GlobalTheory.UnlinkedFirst
