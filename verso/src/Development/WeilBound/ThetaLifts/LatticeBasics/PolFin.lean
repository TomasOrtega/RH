import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

/- English proof (translation)
Introduce `f hf`. Establish `hψ` using `h.base.std`. Establish `hs` using `h.weil.isUSplitting.toIsSplitting`. Set `S : Submodule ℂ (SInf F (Fin n × Fin d))` to `{ carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U} zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩ add_mem' := by`. Introduce and unpack `f g ⟨N, _, h1⟩ ⟨N', _, h2⟩`.

Conclude with `⟨N ⊔ N', inferInstance, fun k hk A hA => by`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩`. Use the proof step `smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }`. Choose the witnesses or unpack the hypotheses as in `⟨U, h0, h1⟩ : f ∈ S := by`.

Use `(sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf` and prove the remaining obligations. Use `haveI := Dense.vacSp_fin h.base.cm M B.emb`. Use `⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `PositivityTheory.ThKOwn.KPol.gauss_impl hψ hs hk hA h₀`. Conclude with `Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _) (Dense.actsD_dop M hψ hu' _)`.

Take `⟨N', h3, h4⟩` from `Dense.exists_dop_fin N`. Use `⟨N', h3, fun k hk A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]`. Conclude with `h4 _ _ _ (h1 k hk A hA)`. Use `⟨U, h0, fun k hk f₁ h₁ => ?_⟩` and prove the remaining obligations.

Take `⟨A, hA⟩` from `PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f`. Rewrite using `[PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]`. Conclude with `h1 k hk A hA`.
-/
theorem polFin {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : IsPair B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  obtain ⟨U, h0, h1⟩ : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      obtain ⟨ε, hε⟩ := PositivityTheory.ThKOwn.KPol.gauss_impl hψ hs hk hA h₀
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA

end GlobalTheory.ThK.Dbl

end
