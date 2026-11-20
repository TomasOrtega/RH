import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMassAdapted

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hB hY hH`. Establish `hx0 : H.x ≠ 0` using `fun h0 => by`. Establish `h1` using `hH.xy`. Rewrite `h1` using `[h0]`. Simplify using `[form] at h1`.

Establish `hcl` using `GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ Y H hx0`. Use `⟨hcl, fun μN hμ => ?_⟩` and prove the remaining obligations. Establish `hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E))`.

Rewrite using `[hY.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, hz⟩` from `hH.split z hz`.

Conclude with `⟨s, t, u, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨s, t, u, rfl⟩` from `hy`. Take `⟨s', t', u', rfl⟩` from `hz`.

Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul a y _ hy`. Take `⟨s, t, u, rfl⟩` from `hy`. Conclude with `⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩`. Take `⟨K, hK, hcov⟩` from `GlobalTheory.UnipHermCover.cocompact_herm F E σ hB.cm n n₁ Y H hY.herm hH.xx hH.yy hH.xy hH.orth hspan`.

Take `⟨hTG, hLC, hSC, hT2⟩` from `GlobalTheory.UnipMass.topUA σ Y.J`. Use `haveI := hTG`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`.

Use `haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (unip σ Y H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (unip σ Y H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Use `haveI := GlobalTheory.UnipMass.countable_ratU' σ Y.J (unip σ Y H)`. Use `haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ Y.J (unip σ Y H)`.

Use `haveI := hμ`. Conclude with `GlobalTheory.UnipMassHerm.exists_fundDom_pos_finite _ K hK hcov μN`.
-/
theorem closed_and_fundDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → IsClosed (unip σ Y H : Set (UA σ Y.J)) ∧ ∀ μN : Measure (unip σ Y H), μN.IsHaarMeasure → ∃ 𝓕 : Set (unip σ Y H), IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hB hY hH
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ Y H hx0
  refine ⟨hcl, fun μN hμ => ?_⟩
  have hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [hY.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UnipHermCover.cocompact_herm F E σ hB.cm n n₁ Y H hY.herm hH.xx hH.yy hH.xy hH.orth hspan
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ Y.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ Y H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ Y H) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := GlobalTheory.UnipMass.countable_ratU' σ Y.J (unip σ Y H)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ Y.J (unip σ Y H)
  haveI := hμ
  exact GlobalTheory.UnipMassHerm.exists_fundDom_pos_finite _ K hK hcov μN

end GlobalTheory.UnipMassAdapted
