import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellCompare

/- English proof (translation)
Introduce `k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x`. Unfold `relParab`. Rewrite using `[Subgroup.mem_pi]`. Express the relevant statement in the definitionally equal form `_ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ`. Prove the components needed by the constructor for the conclusion.

Introduce `hx p q hpq`. Take `⟨⟨a, u⟩, rfl⟩` from `e.surjective p`. Take `⟨⟨b, v⟩, rfl⟩` from `e.surjective q`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Take `⟨⟨j, t⟩, rfl⟩` from `(f a).surjective u`. Take `⟨⟨j', t'⟩, rfl⟩` from `(f a).surjective v`. Rewrite using `[leviEmb_apply_same]`. Conclude with `mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)`. Conclude with `leviEmb_apply_ne k e x hab u v`.

Introduce `hx i _`. Rewrite using `[mem_parab_iff]`. Introduce `j j' t t' hjj`. Establish `h` using `hx ((hδ i j' j t' t).2 hjj)`. Rewrite `h` using `[leviEmb_apply_same]`. Then use the resulting hypothesis.
-/
theorem mem_relParab_iff_leviEmb_mem_blockUpper :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
      {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type}
      [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N)
      (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ)
      (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
        δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m),
      x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  unfold relParab
  rw [Subgroup.mem_pi]
  change _ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ
  constructor
  · intro hx p q hpq
    obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨b, v⟩, rfl⟩ := e.surjective q
    by_cases hab : a = b
    · subst hab
      obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective u
      obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective v
      rw [leviEmb_apply_same]
      exact mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)
    · exact leviEmb_apply_ne k e x hab u v
  · intro hx i _
    rw [mem_parab_iff]
    intro j j' t t' hjj
    have h := hx ((hδ i j' j t' t).2 hjj)
    rwa [leviEmb_apply_same] at h

end GlobalTheory.CompanionTheory.CellCompare
