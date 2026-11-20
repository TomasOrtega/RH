import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ x ν hsd Φ hΦ`. Use `haveI : T2Space A.K := by`. Set `e` to `(Module.finBasis F A.K).equivFun`. Establish `he : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Use `first`.

Consider the case `exact T2Space.of_continuous_injective e.injective he`. Consider the case `exact T2Space.of_injective_continuous e.injective he`. Consider the case `exact e.injective.t2Space he`. Use function extensionality and compare the values at `p`. Establish `hemb : Topology.IsClosedEmbedding (Prod.mk p.1 : A.K → A.K × A.K)`.

Use `⟨isEmbedding_prodMkRight p.1, ?_⟩` and prove the remaining obligations. Establish `: Set.range (Prod.mk p.1 : A.K → A.K × A.K) = ({p.1} : Set A.K) ×ˢ Set.univ`. Use extensionality with `⟨a, b⟩`. Simplify using `only [Set.mem_range, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl, rfl⟩`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨b, rfl, rfl⟩`. Rewrite using `[this]`.

Conclude with `isClosed_singleton.prod isClosed_univ`. Establish `hf : IsTest (fun b => Φ (p.1, b))` using `⟨hΦ.1.comp_continuous hemb.continuous, hΦ.2.comp_isClosedEmbedding hemb⟩`. Conclude with `hsd.2 _ hf p.2`.
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
