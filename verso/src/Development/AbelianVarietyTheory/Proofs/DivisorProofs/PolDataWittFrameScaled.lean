import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameThetaIntegralBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.CuspCompV

open GlobalTheory.StdPar

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨f', hf', hne, -⟩` from `h`. Use `hne ((Submodule.mem_bot ℂ).1 ((Submodule.span_le.2 ?_) hf'))` and prove the remaining obligations. Introduce and unpack `_ ⟨u, a, -, rfl⟩`. Conclude with `(Submodule.mem_bot ℂ).2 rfl`.
-/
theorem isExponent_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {S : Finset (Fin r)} {φ : GAd σ J → ℂ} {s : Fin r → ℂ} (h : IsExponent σ J X Y S φ s) : φ ≠ 0 := by
  rintro rfl
  obtain ⟨f', hf', hne, -⟩ := h
  refine hne ((Submodule.mem_bot ℂ).1 ((Submodule.span_le.2 ?_) hf'))
  rintro _ ⟨u, a, -, rfl⟩
  exact (Submodule.mem_bot ℂ).2 rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨isAutOn_const σ J X Y S K 0, fun _ _ _ _ _ _ _ _ => by simp⟩`.
-/
theorem isCuspOn_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (S : Finset (Fin r)) (K : Subgroup (GAd σ J)) : IsCuspOn σ J X Y S K 0 :=
  ⟨isAutOn_const σ J X Y S K 0, fun _ _ _ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨isCuspOn_zero S' K, 0, hφ.2 S' h, fun _ _ _ _ _ _ _ _ => by simp⟩`.
-/
theorem isCuspComp_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {S S' : Finset (Fin r)} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (hφ : IsCuspOn σ J X Y S K φ) (h : S ⊂ S') :
    IsCuspComp σ J X Y S' K φ 0 :=
  ⟨isCuspOn_zero S' K, 0, hφ.2 S' h, fun _ _ _ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Take `⟨h1, _, _, hint⟩` from `h`. Conclude with `⟨h1, φc, h1.1.isConstAlong_self, fun ψ hψ μ 𝓕 a b g g' => ⟨(hint ψ hψ μ 𝓕 a b g g').2.1, (hint ψ hψ μ 𝓕 a b g g').2.1, rfl⟩⟩`.
-/
theorem isCuspComp_self_of_isCuspComp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {S : Finset (Fin r)} {K : Subgroup (GAd σ J)} {φ φc : GAd σ J → ℂ} (h : IsCuspComp σ J X Y S K φ φc) :
    IsCuspComp σ J X Y S K φc φc := by
  obtain ⟨h1, _, _, hint⟩ := h
  exact ⟨h1, φc, h1.1.isConstAlong_self, fun ψ hψ μ 𝓕 a b g g' =>
    ⟨(hint ψ hψ μ 𝓕 a b g g').2.1, (hint ψ hψ μ 𝓕 a b g g').2.1, rfl⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S hS`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`. Establish `hJ : IsHermND σ (c • G.W.J.map σ)` using `GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcσ`. Establish `HL` using `hKP.automorphicFormsUnitary.2`. Take `⟨φc, hφc, -⟩` from `(HL F E σ hcm _ _ hJ r Xf Yf hW K hK ∅ _ (isAutOn_empty.2 hA)).1 S (Finset.empty_subset S)`.

Distinguish the cases in `h0 : φc = 0`. Conclude with `h0 ▸ hφc`. It suffices to derive a contradiction. Establish `hL` using `HL F E σ hcm _ _ hJ r Xf Yf hW K hK S φc hφc.1.1`. Take `⟨S', hSS', s, ψ, hψ, hexp⟩` from `hL.2.2 h0`.

Break down `eq_or_ssubset_of_subset hSS' with e | hss` into its components or cases. Substitute `e` using the available equality. Take `rfl : ψ = φc` from `(hL.1 S le_rfl).unique hψ (isCuspComp_self_of_isCuspComp hφc)`. Conclude with `hS (GlobalTheory.T.witt_frame_theta_integral_bound F E σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S s ⟨ψ, hφc, hexp⟩)`. Conclude with `isExponent_ne_zero hexp ((hL.1 S' hSS').unique hψ (isCuspComp_zero hφc.1 hss))`.
-/
theorem cuspComp_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ i ≤ k, i ∈ S) →
            GlobalTheory.StdPar.IsCuspComp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S hS
  have hcm : IsCMExt F E σ := hT.base.cm
  have hJ : IsHermND σ (c • G.W.J.map σ) :=
    GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcσ
  have HL := hKP.automorphicFormsUnitary.2
  obtain ⟨φc, hφc, -⟩ := (HL F E σ hcm _ _ hJ r Xf Yf hW K hK ∅ _ (isAutOn_empty.2 hA)).1 S (Finset.empty_subset S)
  by_cases h0 : φc = 0
  · exact h0 ▸ hφc
  exfalso
  have hL := HL F E σ hcm _ _ hJ r Xf Yf hW K hK S φc hφc.1.1
  obtain ⟨S', hSS', s, ψ, hψ, hexp⟩ := hL.2.2 h0
  rcases eq_or_ssubset_of_subset hSS' with e | hss
  · subst e
    obtain rfl : ψ = φc := (hL.1 S le_rfl).unique hψ (isCuspComp_self_of_isCuspComp hφc)
    exact hS (GlobalTheory.T.witt_frame_theta_integral_bound F E σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S s ⟨ψ, hφc, hexp⟩)
  · exact isExponent_ne_zero hexp ((hL.1 S' hSS').unique hψ (isCuspComp_zero hφc.1 hss))

end GlobalTheory.ThK.CuspCompV
