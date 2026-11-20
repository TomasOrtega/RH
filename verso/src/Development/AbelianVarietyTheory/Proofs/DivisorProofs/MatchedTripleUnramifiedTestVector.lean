import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalActionStatement

namespace GlobalTheory.ThK.SoKInf

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk Φ hΦ`. Establish `h1 : At (evI F) (mat (1 : UA σ G.V'.J) - 1)`. Introduce `u _`. Simplify using `[mat]`. Establish `hloc` using `GlobalTheory.T.archimedean_theta_local_action hK.base F E σ B a a' G X om om' hM.triple 1 k h1 hk.1`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, φ, hSB, hvac, hv₁, rfl⟩` from `hx`. Take `⟨f₂, e⟩` from `hloc f φ hSB hvac`. Rewrite using `[e]`.

Conclude with `Submodule.subset_span ⟨f₂, φ, hSB, hvac, hv₁, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem so_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ k ∈ KInf σ G.W B.emb, ∀ Φ ∈ G.M'.So B.ψ B.τ₁,
      om' (1, k) Φ ∈ G.M'.So B.ψ B.τ₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk Φ hΦ
  have h1 : At (evI F) (mat (1 : UA σ G.V'.J) - 1) := by
    intro u _
    simp [mat]
  have hloc := GlobalTheory.T.archimedean_theta_local_action hK.base F E σ B a a' G X om om' hM.triple 1 k h1 hk.1
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    obtain ⟨f₂, e⟩ := hloc f φ hSB hvac
    rw [e]
    exact Submodule.subset_span ⟨f₂, φ, hSB, hvac, hv₁, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ThK.SoKInf
