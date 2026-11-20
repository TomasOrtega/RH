import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Treat this case separately. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem pt_pt_eq_reflect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  intro F E _ _ _ _ _ A ψ x ν hsd Φ hΦ

  haveI : T2Space A.K := by
    let e := (Module.finBasis F A.K).equivFun
    have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    first
      | exact T2Space.of_continuous_injective e.injective he
      | exact T2Space.of_injective_continuous e.injective he
      | exact e.injective.t2Space he
  funext p
  have hemb : Topology.IsClosedEmbedding (Prod.mk p.1 : A.K → A.K × A.K) := by
    refine ⟨isEmbedding_prodMkRight p.1, ?_⟩
    have : Set.range (Prod.mk p.1 : A.K → A.K × A.K) = ({p.1} : Set A.K) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      simp only [Set.mem_range, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      constructor
      · rintro ⟨y, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨b, rfl, rfl⟩
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  have hf : IsTest (fun b => Φ (p.1, b)) :=
    ⟨hΦ.1.comp_continuous hemb.continuous, hΦ.2.comp_isClosedEmbedding hemb⟩
  exact hsd.2 _ hf p.2

end GlobalTheory.JR.Hyp
