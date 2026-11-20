import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRingsStatement

open scoped Pointwise
open GlobalTheory.Published GlobalTheory.Published.AbVarRed

namespace GlobalTheory.ValConj

/- English proof (translation)
Set `: TopologicalSpace Ω` to `⊥`. Establish `: DiscreteTopology Ω` using `⟨rfl⟩`. Establish `: ContinuousSMul (Ω ≃ₐ[K] Ω) Ω` using `continuousSMul_iff_stabilizer_isOpen.mpr fun y => stabilizer_isOpen_of_isIntegral y`. Rewrite using `[IsLocallyConstant.iff_continuous]`. Conclude with `(continuous_id.smul continuous_const : Continuous fun g : Ω ≃ₐ[K] Ω => g • x)`.
-/
theorem isLocallyConstant_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (x : Ω) :
    IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g x) := by
  let : TopologicalSpace Ω := ⊥
  have : DiscreteTopology Ω := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) Ω :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun y => stabilizer_isOpen_of_isIntegral y
  rw [IsLocallyConstant.iff_continuous]
  exact (continuous_id.smul continuous_const : Continuous fun g : Ω ≃ₐ[K] Ω => g • x)

/- English proof (translation)
Establish `key` using `(isCompact_univ (X := Ω ≃ₐ[K] Ω)).inter_iInter_nonempty (fun x : Ω => {g : Ω ≃ₐ[K] Ω | g x ∈ V' ↔ x ∈ V}) (fun x => ((isLocallyConstant_apply (K := K) x).comp (fun y => y ∈ V' ↔ x ∈ V)).isClosed_fiber True |> fun h => by simpa using h) (fun u => by`. Set `L : IntermediateField K Ω` to `(FiniteGaloisIntermediateField.adjoin K (u : Set Ω)).toIntermediateField`. Establish `hL : ∀ x ∈ u, x ∈ L` using `fun x hx => FiniteGaloisIntermediateField.subset_adjoin K (u : Set Ω) hx`. Establish `hc : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring → IsAbove R K (W.comap (algebraMap L Ω)).toSubring` using `fun W hW => by`. Unfold `IsAbove at hW ⊢`.

Rewrite using `[← hW]`. Use extensionality with `y`. Both sides reduce to the same expression. Take `⟨τ, hτ⟩` from `GlobalTheory.T.galois_transitive_on_valuation_rings R K L _ _ (hc V hV) (hc V' hV')`. Use `⟨τ.liftNormal Ω, trivial, Set.mem_iInter₂.2 fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h1 : τ.liftNormal Ω x = algebraMap L Ω (τ ⟨x, hL x hx⟩)` using `τ.liftNormal_commutes Ω ⟨x, hL x hx⟩`. Express the relevant statement in the definitionally equal form `τ.liftNormal Ω x ∈ V' ↔ x ∈ V`. Rewrite using `[h1, ← ValuationSubring.mem_comap, ← hτ]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff (g := τ) (x := (⟨x, hL x hx⟩ : L)) (S := V.comap (algebraMap L Ω)))`. Take `⟨g, -, hg⟩` from `key`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Take `⟨x, rfl⟩` from `g.surjective y`. Use `Set.mem_iInter.1 hg x` as an intermediate fact. Conclude with `(ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := x)).trans (Iff.symm this)`.
-/
theorem exists_smul_eq_of_isAbove (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (V V' : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (hV' : IsAbove R K V'.toSubring) :
    ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  classical
  have key := (isCompact_univ (X := Ω ≃ₐ[K] Ω)).inter_iInter_nonempty
    (fun x : Ω => {g : Ω ≃ₐ[K] Ω | g x ∈ V' ↔ x ∈ V})
    (fun x => ((isLocallyConstant_apply (K := K) x).comp (fun y => y ∈ V' ↔ x ∈ V)).isClosed_fiber True
      |> fun h => by simpa using h)
    (fun u => by
      let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K (u : Set Ω)).toIntermediateField
      have hL : ∀ x ∈ u, x ∈ L := fun x hx => FiniteGaloisIntermediateField.subset_adjoin K (u : Set Ω) hx
      have hc : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring →
          IsAbove R K (W.comap (algebraMap L Ω)).toSubring := fun W hW => by
        unfold IsAbove at hW ⊢
        rw [← hW]
        ext y
        rfl
      obtain ⟨τ, hτ⟩ := GlobalTheory.T.galois_transitive_on_valuation_rings R K L _ _ (hc V hV) (hc V' hV')
      refine ⟨τ.liftNormal Ω, trivial, Set.mem_iInter₂.2 fun x hx => ?_⟩
      have h1 : τ.liftNormal Ω x = algebraMap L Ω (τ ⟨x, hL x hx⟩) := τ.liftNormal_commutes Ω ⟨x, hL x hx⟩
      change τ.liftNormal Ω x ∈ V' ↔ x ∈ V
      rw [h1, ← ValuationSubring.mem_comap, ← hτ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := τ) (x := (⟨x, hL x hx⟩ : L))
        (S := V.comap (algebraMap L Ω)))
  obtain ⟨g, -, hg⟩ := key
  refine ⟨g, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  have := Set.mem_iInter.1 hg x
  exact (ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := x)).trans (Iff.symm this)

end GlobalTheory.ValConj
