import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRationalFrameExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesIrreducibleStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThK.ExponentNeZero

/- English proof (translation)
Use `push Not at h`. Take `⟨k, hk, i, hik, hi⟩` from `h`. Establish `hne : (S.filter (i ≤ ·)).Nonempty` using `⟨k, Finset.mem_filter.2 ⟨hk, hik⟩⟩`. Establish `h0` using `Finset.mem_filter.1 (Finset.min'_mem _ hne)`. Use `⟨_, h0.1, i, lt_of_le_of_ne h0.2 fun e => hi (e ▸ h0.1), fun j hij hjk hj => ?_⟩` and prove the remaining obligations.

Conclude with `absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨hj, hij⟩)) (not_le.2 hjk)`.
-/
theorem exists_block {r : ℕ} {S : Finset (Fin r)} (h : ¬ ∀ k ∈ S, ∀ i ≤ k, i ∈ S) :
    ∃ k ∈ S, ∃ i : Fin r, i < k ∧ ∀ j : Fin r, i ≤ j → j < k → j ∉ S := by
  classical
  push Not at h
  obtain ⟨k, hk, i, hik, hi⟩ := h
  have hne : (S.filter (i ≤ ·)).Nonempty := ⟨k, Finset.mem_filter.2 ⟨hk, hik⟩⟩
  have h0 := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  refine ⟨_, h0.1, i, lt_of_le_of_ne h0.2 fun e => hi (e ▸ h0.1), fun j hij hjk hj => ?_⟩
  exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨hj, hij⟩)) (not_le.2 hjk)

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨f', hf', hne, -⟩` from `h`. Use `hne ((Submodule.mem_bot ℂ).1 ((Submodule.span_le.2 ?_) hf'))` and prove the remaining obligations. Introduce and unpack `_ ⟨u, a, -, rfl⟩`. Conclude with `(Submodule.mem_bot ℂ).2 rfl`.
-/
theorem ne_zero_of_isExponent {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {S : Finset (Fin r)} {φ : GAd σ J → ℂ} {s : Fin r → ℂ} (h : GlobalTheory.StdPar.IsExponent σ J X Y S φ s) : φ ≠ 0 := by
  rintro rfl
  obtain ⟨f', hf', hne, -⟩ := h
  refine hne ((Submodule.mem_bot ℂ).1 ((Submodule.span_le.2 ?_) hf'))
  rintro _ ⟨u, a, -, rfl⟩
  exact (Submodule.mem_bot ℂ).2 rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hS`. Use `haveI : IsTotallyComplex E := hT.base.cm.2.1`. Assume the negation of the conclusion as `hno`. Take `⟨k, hk, i, hik, hgap⟩` from `exists_block hno`. Take `⟨φc, hφc, hexp⟩` from `hS`.

Take `⟨w, x, x', τ, χ₁, χ₂, s₁, s₂, h2, hu₁, hu₂, hn₁, hn₂, hs, V, _, _, Q, hQ, f, hf⟩` from `GlobalTheory.T.theta_integral_rational_frame_expansion F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S φc hφc (ne_zero_of_isExponent hexp) k hk i hik hgap`. Establish `unr : ∀ {χ : (w.adicCompletion E)ˣ →* ℂˣ} (t : ℝ), GlobalTheory.SplitWeil.IsUnram χ → GlobalTheory.SmGL.IsSmoothChar (χ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (t : ℂ))` using `fun t h => GlobalTheory.SmGL.isSmoothChar_of_isUnram fun u hu => by`. Rewrite using `[MonoidHom.mul_apply, h u hu, GlobalTheory.SmGL.isUnram_absPow _ _ u hu, mul_one]`. Take `⟨hx, hx'⟩` from `GlobalTheory.T.generic_subquotient_principal_series E x x' τ w _ _ hKP.genericityGL (unr s₁ hu₁) (unr s₂ hu₂) V Q hQ f hf`. Take `rfl : x = 1` from `by omega`.

Take `rfl : x' = 1` from `by omega`. Conclude with `GlobalTheory.T.unramified_principal_series_irreducible E τ w χ₁ χ₂ s₁ s₂ hKP.jacquetShalika.2 hu₁ hu₂ hn₁ hn₂ (hs rfl rfl) V Q hQ f hf`.
-/
theorem blocks_initial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ k ∈ S, ∀ i ≤ k, i ∈ S := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hS
  haveI : IsTotallyComplex E := hT.base.cm.2.1
  by_contra hno
  obtain ⟨k, hk, i, hik, hgap⟩ := exists_block hno
  obtain ⟨φc, hφc, hexp⟩ := hS
  obtain ⟨w, x, x', τ, χ₁, χ₂, s₁, s₂, h2, hu₁, hu₂, hn₁, hn₂, hs, V, _, _, Q, hQ, f, hf⟩ :=
    GlobalTheory.T.theta_integral_rational_frame_expansion F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S φc hφc
      (ne_zero_of_isExponent hexp) k hk i hik hgap
  have unr : ∀ {χ : (w.adicCompletion E)ˣ →* ℂˣ} (t : ℝ), GlobalTheory.SplitWeil.IsUnram χ →
      GlobalTheory.SmGL.IsSmoothChar (χ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (t : ℂ)) := fun t h =>
    GlobalTheory.SmGL.isSmoothChar_of_isUnram fun u hu => by
      rw [MonoidHom.mul_apply, h u hu, GlobalTheory.SmGL.isUnram_absPow _ _ u hu, mul_one]
  obtain ⟨hx, hx'⟩ := GlobalTheory.T.generic_subquotient_principal_series E x x' τ w _ _ hKP.genericityGL (unr s₁ hu₁) (unr s₂ hu₂) V Q hQ f hf
  obtain rfl : x = 1 := by omega
  obtain rfl : x' = 1 := by omega
  exact GlobalTheory.T.unramified_principal_series_irreducible E τ w χ₁ χ₂ s₁ s₂ hKP.jacquetShalika.2 hu₁ hu₂ hn₁ hn₂ (hs rfl rfl) V Q hQ f hf

end GlobalTheory.ThK.ExponentNeZero
