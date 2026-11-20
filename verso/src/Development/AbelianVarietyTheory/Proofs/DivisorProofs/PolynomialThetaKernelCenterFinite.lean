import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToGAdInfPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothModuleFiniteRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaImaginaryScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaImaginaryVanishStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKZFinSmall

open GlobalTheory.WeakHolFamily in

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [dop, Pi.add_apply, Finsupp.sum]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[foldr_add (J := J) hf hh l (hz l hl), Pi.add_apply, mul_add]`.
-/
theorem dop_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ)
    {f h : GAd σ J → ℂ} (hf : IsSm σ J f) (hh : IsSm σ J h) : dop z (f + h) = dop z f + dop z h := by
  funext g
  simp only [dop, Pi.add_apply, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_add (J := J) hf hh l (hz l hl), Pi.add_apply, mul_add]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use function extensionality and compare the values at `g`. Simplify using `only [Finset.sum_empty, dop, Pi.zero_apply, Finsupp.sum]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.WeakHolFamily.foldr_zero (J := J) l]`. Simplify using the standard rewrite rules. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Establish `hs : IsSm σ J (∑ j ∈ s, ψ j)`.

Establish `: ∀ t : Finset ι, (∀ j ∈ t, IsSm σ J (ψ j)) → IsSm σ J (∑ j ∈ t, ψ j)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro _`. Conclude with `GlobalTheory.WeakHolFamily.smoothLines_zero (J := J)`.

Consider the case `insert j t hj iht`. Introduce `h`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `GlobalTheory.WeakHolFamily.smoothLines_add (J := J) (h j (Finset.mem_insert_self _ _)) (iht fun k hk => h k (Finset.mem_insert_of_mem hk))`. Conclude with `this s fun j hj => hψ j (Finset.mem_insert_of_mem hj)`.

Rewrite using `[dop_add hz (hψ i (Finset.mem_insert_self _ _)) hs, ih fun j hj => hψ j (Finset.mem_insert_of_mem hj)]`.
-/
theorem dop_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ)
    {ι : Type} (s : Finset ι) (ψ : ι → GAd σ J → ℂ) (hψ : ∀ i ∈ s, IsSm σ J (ψ i)) :
    dop z (∑ i ∈ s, ψ i) = ∑ i ∈ s, dop z (ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext g
    simp only [Finset.sum_empty, dop, Pi.zero_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [GlobalTheory.WeakHolFamily.foldr_zero (J := J) l]
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : IsSm σ J (∑ j ∈ s, ψ j) := by
      have : ∀ t : Finset ι, (∀ j ∈ t, IsSm σ J (ψ j)) → IsSm σ J (∑ j ∈ t, ψ j) := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro _; exact GlobalTheory.WeakHolFamily.smoothLines_zero (J := J)
        | insert j t hj iht =>
          intro h
          rw [Finset.sum_insert hj]
          exact GlobalTheory.WeakHolFamily.smoothLines_add (J := J) (h j (Finset.mem_insert_self _ _))
            (iht fun k hk => h k (Finset.mem_insert_of_mem hk))
      exact this s fun j hj => hψ j (Finset.mem_insert_of_mem hj)
    rw [dop_add hz (hψ i (Finset.mem_insert_self _ _)) hs, ih fun j hj => hψ j (Finset.mem_insert_of_mem hj)]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ`. Take `⟨m, f, φ, hgood, rfl⟩` from `GlobalTheory.T.polarized_data_tensor_decomposition F E σ B a a' G X om om' hT Φ hΦ`. Establish `hD : ∀ i, pure (f i) (φ i) ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁` using `fun i => ⟨Submodule.subset_span ⟨f i, (hgood i).1, φ i, (hgood i).2.1, (hgood i).2.2.1, rfl⟩, Submodule.subset_span ⟨f i, φ i, (hgood i).2.1, (hgood i).2.2.1, (hgood i).2.2.2, rfl⟩⟩`. Take `⟨Lin, hLin⟩` from `GlobalTheory.ThKLinT.thetaIntegral_linear_of_triple F E σ B a a' G X om om' hK hT`. Set `θi : Fin m → GAd σ (c • G.W.J.map σ) → ℂ` to `fun i x => G.M'.I om' (pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)`.

Establish `hI : G.M'.I om' (∑ i, pure (f i) (φ i)) = ∑ i, G.M'.I om' (pure (f i) (φ i))`. Establish `h1` using `hLin ⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩`. Establish `h2 : (⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) = ∑ i, ⟨pure (f i) (φ i), hD i⟩` using `by ext1; simp`. Rewrite using `[← h1, h2, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hLin _`.

Establish `hsum : (fun x => G.M'.I om' (∑ i, pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)) = ∑ i, θi i`. Use function extensionality and compare the values at `x`. Rewrite using `[hI]`. Simplify using `[θi, Finset.sum_apply]`. Establish `hfd : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {g | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ g = dop z (θi i)})`.

Introduce `i`. Take `⟨hsm, hline, hk, hrank⟩` from `GlobalTheory.T.weil_theta_imaginary_scalar F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1 (hgood i).2.2.1 (hgood i).2.2.2`. Take `⟨L, hL⟩` from `GlobalTheory.T.weil_theta_imaginary_vanish F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1 (hgood i).2.2.1 (hgood i).2.2.2`. Conclude with `GlobalTheory.T.smooth_module_finite_rank F E σ _ (c • G.W.J.map σ) _ ((toGAd hσ G.W.J hc) '' KInf σ G.W B.emb) (by rintro _ ⟨k, hk, rfl⟩; exact GlobalTheory.T.unitary_to_GAd_inf_points F E σ hσ _ G.W c hc k hk.1) hsm hline (by rintro _ ⟨k, hk', rfl⟩ ψ hψ; exact hk k hk' ψ hψ) hra …`. Establish `hsm : ∀ i, IsSm σ (c • G.W.J.map σ) (θi i)` using `fun i => (GlobalTheory.T.weil_theta_imaginary_scalar F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1 (hgood i).2.2.1 (hgood i).2.2.2).1 _ (Submodule.subset_span ⟨f i, (hgood i).1, rfl⟩)`.

Use `haveI := hfd`. Use `Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Submodule.span ℂ {g | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ g = dop z (θi i)}) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[hsum, dop_sum hz.1 Finset.univ θi fun i _ => hsm i]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨z, hz, rfl⟩)`.
-/
theorem zfin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ f = dop z (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x))}) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ
  obtain ⟨m, f, φ, hgood, rfl⟩ := GlobalTheory.T.polarized_data_tensor_decomposition F E σ B a a' G X om om' hT Φ hΦ
  have hD : ∀ i, pure (f i) (φ i) ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun i =>
    ⟨Submodule.subset_span ⟨f i, (hgood i).1, φ i, (hgood i).2.1, (hgood i).2.2.1, rfl⟩,
      Submodule.subset_span ⟨f i, φ i, (hgood i).2.1, (hgood i).2.2.1, (hgood i).2.2.2, rfl⟩⟩
  obtain ⟨Lin, hLin⟩ := GlobalTheory.ThKLinT.thetaIntegral_linear_of_triple F E σ B a a' G X om om' hK hT
  let θi : Fin m → GAd σ (c • G.W.J.map σ) → ℂ := fun i x =>
    G.M'.I om' (pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)
  have hI : G.M'.I om' (∑ i, pure (f i) (φ i)) = ∑ i, G.M'.I om' (pure (f i) (φ i)) := by
    have h1 := hLin ⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩
    have h2 : (⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩ :
        ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) = ∑ i, ⟨pure (f i) (φ i), hD i⟩ := by
      ext1; simp
    rw [← h1, h2, map_sum]
    exact Finset.sum_congr rfl fun i _ => hLin _
  have hsum : (fun x => G.M'.I om' (∑ i, pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)) = ∑ i, θi i := by
    funext x; rw [hI]; simp [θi, Finset.sum_apply]
  have hfd : ∀ i, FiniteDimensional ℂ
      (Submodule.span ℂ {g | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ g = dop z (θi i)}) := by
    intro i
    obtain ⟨hsm, hline, hk, hrank⟩ := GlobalTheory.T.weil_theta_imaginary_scalar F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1
      (hgood i).2.2.1 (hgood i).2.2.2
    obtain ⟨L, hL⟩ := GlobalTheory.T.weil_theta_imaginary_vanish F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1
      (hgood i).2.2.1 (hgood i).2.2.2
    exact GlobalTheory.T.smooth_module_finite_rank F E σ _ (c • G.W.J.map σ) _ ((toGAd hσ G.W.J hc) '' KInf σ G.W B.emb)
      (by rintro _ ⟨k, hk, rfl⟩; exact GlobalTheory.T.unitary_to_GAd_inf_points F E σ hσ _ G.W c hc k hk.1) hsm hline
      (by rintro _ ⟨k, hk', rfl⟩ ψ hψ; exact hk k hk' ψ hψ) hrank
      ⟨L, fun m N h1 h2 h3 h4 => hL m N h1 h2 h3 fun i k hk => h4 i _ ⟨k, hk, rfl⟩⟩ (θi i)
      (Submodule.subset_span ⟨f i, (hgood i).1, rfl⟩)
  have hsm : ∀ i, IsSm σ (c • G.W.J.map σ) (θi i) := fun i =>
    (GlobalTheory.T.weil_theta_imaginary_scalar F E σ hσ B a a' G X om om' hK hT c hc hcs (φ i) (hgood i).2.1 (hgood i).2.2.1 (hgood i).2.2.2).1 _
      (Submodule.subset_span ⟨f i, (hgood i).1, rfl⟩)
  haveI := hfd
  refine Submodule.finiteDimensional_of_le
    (S₂ := ⨆ i, Submodule.span ℂ {g | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ g = dop z (θi i)}) ?_
  rw [Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  rw [hsum, dop_sum hz.1 Finset.univ θi fun i _ => hsm i]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨z, hz, rfl⟩)

end GlobalTheory.ThKZFinSmall
