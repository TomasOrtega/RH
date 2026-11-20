import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm

noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
