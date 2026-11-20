import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStableStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnitStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Introduce `D H Dw l Xo c σ V r C hC dict hd Kf hK`. Establish `last : ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩`. Introduce `g k γ hm`. Take `⟨γ₀, hm₀, hf⟩` from `hd.1 g`. Establish `hu` using `GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC g`.

Establish `hk : (dict g).1 = k` using `hu.1 _ _ _ _ hm₀ hm`. Substitute `hk` using the available equality. Take `⟨δ, hδ, he⟩` from `hu.2 _ γ γ₀ hm hm₀`. Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, ← hf]`.

Use `⟨?_, ?_, ?_, ?_, last⟩` and prove the remaining obligations. Introduce `γ hγ g`. Take `⟨γ₀, hm₀, hf⟩` from `hd.1 g`. Establish `hm` using `(GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).1 γ hγ`. Take `⟨δ, hδ, he⟩` from `last _ _ _ hm`.

Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations. Rewrite using `[he, hf, mul_assoc, inv_mul_cancel_left]`. Introduce `k hk g`. Take `⟨γ₀, hm₀, hf⟩` from `hd.1 g`. Establish `hk'` using `(hK k).1 hk`.

Establish `hm` using `(GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).2.1 k hk'.2`. Take `⟨δ, hδ, he⟩` from `last _ _ _ hm`. Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations. Rewrite using `[he, hf, ← mul_assoc, (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.2.2.1 k hk'.1]`. Introduce `g`.

Take `⟨γ₀, -, hf⟩` from `hd.1 g`. Rewrite using `[hf]`. Conclude with `(GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.1`. Introduce `g τ i`. Take `⟨γ₀, -, hf⟩` from `hd.1 g`.

Rewrite using `[hf]`. Conclude with `(GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.1 τ i`.
-/
theorem dict_invariant : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  have last : ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
    intro g k γ hm
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hu := GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC g
    have hk : (dict g).1 = k := hu.1 _ _ _ _ hm₀ hm
    subst hk
    obtain ⟨δ, hδ, he⟩ := hu.2 _ γ γ₀ hm hm₀
    refine ⟨δ, hδ, ?_⟩
    rw [← he, ← hf]
  refine ⟨?_, ?_, ?_, ?_, last⟩
  · intro γ hγ g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hm := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).1 γ hγ
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, mul_assoc, inv_mul_cancel_left]
  · intro k hk g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hk' := (hK k).1 hk
    have hm := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).2.1 k hk'.2
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, ← mul_assoc,
      (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.2.2.1 k hk'.1]
  · intro g
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.1
  · intro g τ i
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.1 τ i

end GlobalTheory.Member
