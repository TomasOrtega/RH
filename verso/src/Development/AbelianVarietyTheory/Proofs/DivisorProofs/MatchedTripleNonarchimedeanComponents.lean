import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.SoFinite

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm v h hh Φ hΦ`. Establish `hT` using `hm.triple`. Establish `hP` using `GlobalTheory.ThK.Inhab.pairV' hT`. Establish `hAE` using `GlobalTheory.T.theta_action_exists hK.base`. Establish `h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)`.

Introduce `u _`. Use `show u • (mat (1 : UA σ G.V'.J) - 1) = 0`. Establish `: mat (1 : UA σ G.V'.J) = 1` using `rfl`. Rewrite using `[this, sub_self, smul_zero]`. Proceed by induction on `hΦ using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨f, φ, hSB, hev, hloc, rfl⟩` from `hx`. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `by filter_upwards [hev, hT.geo.hM'.std] with w h1 h2`. Rewrite using `[h1, h2]`. Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `(hAE F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v).1 1 h1 h hh (φ v) (hSB v)`.

Establish `e` using `GlobalTheory.ThK.LocalOps.acts_pure v (om' (1, h)) f φ φ₁ (GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd) (GlobalTheory.PureFactor.mulSupport_finite φ hstd) hact`. Rewrite using `[e]`. Use `Submodule.subset_span ⟨f, Function.update φ v φ₁, fun w => ?_, ?_, ?_, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hφ₁`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`. Use `filter_upwards [hev, Filter.eventually_cofinite_ne v] with w h1 h2`.

Rewrite using `[Function.update_of_ne h2, h1]`. Distinguish the cases in `hv : v = B.v₁`. Substitute `hv` using the available equality. Rewrite using `[Function.update_self]`. Take `⟨-, ι, hι, hsupp⟩` from `hloc`.

Use `⟨hφ₁, ι, hι, fun Y hY => ?_⟩` and prove the remaining obligations. Take `⟨c, P, Q, hPQ⟩` from `GlobalTheory.T.linear_bar_local_theta_factor hK.base F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι 1 h1 h hh (φ B.v₁) (hSB B.v₁) φ₁ hφ₁ hact`. Rewrite using `[hPQ Y, hsupp, mul_zero]`. Establish `hPd : IsUnit (P.1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 P.isUnit`. Establish `hQd : IsUnit (Q.1).det` using `(Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit`.

Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQd, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPd]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne (Ne.symm hv)]`. Conclude with `hloc`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mem_so_of_fin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (v : Pl F), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, om' (1, h) Φ ∈ G.M'.So B.ψ B.τ₁ := by
  classical
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm v h hh Φ hΦ
  have hT := hm.triple
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := GlobalTheory.T.theta_action_exists hK.base
  have h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V'.J) - 1) = 0
    have : mat (1 : UA σ G.V'.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hev, hloc, rfl⟩ := hx
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hev, hT.geo.hM'.std] with w h1 h2
      rw [h1, h2]
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := (hAE F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v).1
      1 h1 h hh (φ v) (hSB v)
    have e := GlobalTheory.ThK.LocalOps.acts_pure v (om' (1, h)) f φ φ₁ (GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd)
      (GlobalTheory.PureFactor.mulSupport_finite φ hstd) hact
    rw [e]
    refine Submodule.subset_span ⟨f, Function.update φ v φ₁, fun w => ?_, ?_, ?_, rfl⟩
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    · by_cases hv : v = B.v₁
      · subst hv
        rw [Function.update_self]
        obtain ⟨-, ι, hι, hsupp⟩ := hloc
        refine ⟨hφ₁, ι, hι, fun Y hY => ?_⟩
        obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hK.base F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι 1 h1 h hh
          (φ B.v₁) (hSB B.v₁) φ₁ hφ₁ hact
        rw [hPQ Y, hsupp, mul_zero]
        have hPd : IsUnit (P.1).det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
        have hQd : IsUnit (Q.1).det := (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
        rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQd, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPd]
      · rw [Function.update_of_ne (Ne.symm hv)]; exact hloc
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ThK.SoFinite

end
