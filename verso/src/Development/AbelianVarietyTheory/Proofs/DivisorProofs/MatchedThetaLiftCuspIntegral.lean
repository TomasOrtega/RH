import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivOpSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureMemPureSpanG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalActionAtSpecialPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPolynomialLinesInvarianceStatement

noncomputable section

namespace GlobalTheory.ThetaFibMaxSo

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThetaFibMax GlobalTheory.ThetaFibMaxG
open scoped TensorProduct

def GdSo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ φ B.v₁ ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)

/- English proof (translation)
Establish `hV'` using `GlobalTheory.ThK.Inhab.pairV' hT`. Establish `hstd` using `hT.geo.hM'.std`. Establish `h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)`. Introduce `u _`. Use `show u • (mat (1 : UA σ G.V'.J) - 1) = 0`.

Establish `: mat (1 : UA σ G.V'.J) = 1` using `rfl`. Rewrite using `[this, sub_self, smul_zero]`. Establish `key : ∀ f ∈ P, ∀ φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ → om' (1, h) (pure f φ) ∈ pureSpanG G.M' (GdSo B G.M') P`. Introduce `f hf φ hSB hev hv1`. Establish `hs : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hstd).mono fun w hw => hw.1.trans hw.2`.

Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `((GlobalTheory.T.theta_action_exists hKP.base) F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hV' v).1 1 h1 h hh (φ v) (hSB v)`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φ hs`. Establish `hpure : tens (evFin F v) (φ v) ρ = pure f φ` using `by rw [hρt, Function.update_eq_self]`. Establish `hRest : Rest (evFin F v) (φ v) ρ` using `⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hs⟩`. Establish `hmap : om' (1, h) (pure f φ) = pure f (Function.update φ v φ₁)`.

Rewrite using `[← hpure, hact ρ hRest, hρt]`. Rewrite using `[hmap]`. Use `Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, ⟨fun w => ?_, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hφ₁`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`. Use `filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne`.

Rewrite using `[Function.update_of_ne hne]`. Conclude with `hw`. Apply `Submodule.subset_span` to reduce the goal to its premises. Distinguish the cases in `hw : B.v₁ = v`. Substitute `hw` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `GlobalTheory.T.triple_local_action_at_special_place hKP F E σ B a a' G X om om' hT h hh (φ B.v₁) hv1 φ₁ hφ₁ hact`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hv1`. Introduce `Φ hΦ`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, hf, φ, ⟨hSB, hev, hv1⟩, rfl⟩` from `hΨ`. Conclude with `GlobalTheory.SoPure.pure_mem_of_span G.M' B.ψ B.τ₁ hstd f ((pureSpanG G.M' (GdSo B G.M') P).comap (om' (1, h))) (fun φ' h1' h2' h3' => key f hf φ' h1' h2' h3') φ hSB hev hv1`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem fin_so (hKP : KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (P : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))))
    (v : Pl F) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v)) :
    ∀ Φ ∈ pureSpanG G.M' (GdSo B G.M') P, om' (1, h) Φ ∈ pureSpanG G.M' (GdSo B G.M') P := by
  classical
  have hV' := GlobalTheory.ThK.Inhab.pairV' hT
  have hstd := hT.geo.hM'.std
  have h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V'.J) - 1) = 0
    have : mat (1 : UA σ G.V'.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have key : ∀ f ∈ P, ∀ φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) →
      (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      om' (1, h) (pure f φ) ∈ pureSpanG G.M' (GdSo B G.M') P := by
    intro f hf φ hSB hev hv1
    have hs : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hstd).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ :=
      ((GlobalTheory.T.theta_action_exists hKP.base) F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hV' v).1 1 h1 h hh (φ v) (hSB v)
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
    have hpure : tens (evFin F v) (φ v) ρ = pure f φ := by rw [hρt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hs⟩
    have hmap : om' (1, h) (pure f φ) = pure f (Function.update φ v φ₁) := by
      rw [← hpure, hact ρ hRest, hρt]
    rw [hmap]
    refine Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, ⟨fun w => ?_, ?_, ?_⟩, rfl⟩
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
    · apply Submodule.subset_span
      by_cases hw : B.v₁ = v
      · subst hw
        rw [Function.update_self]
        exact GlobalTheory.T.triple_local_action_at_special_place hKP F E σ B a a' G X om om' hT h hh (φ B.v₁) hv1 φ₁ hφ₁ hact
      · rw [Function.update_of_ne hw]; exact hv1
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, ⟨hSB, hev, hv1⟩, rfl⟩ := hΨ
    exact GlobalTheory.SoPure.pure_mem_of_span G.M' B.ψ B.τ₁ hstd f ((pureSpanG G.M' (GdSo B G.M') P).comap (om' (1, h)))
      (fun φ' h1' h2' h3' => key f hf φ' h1' h2' h3') φ hSB hev hv1
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Rewrite using `[GlobalTheory.SoPure.polSo_eq_span B M hstd]`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, φ, h1, h2, h3, rfl⟩`. Conclude with `Submodule.subset_span ⟨f, hf, φ, ⟨h1, h2, Submodule.subset_span h3⟩, rfl⟩`.

Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, φ, ⟨h1, h2, h3⟩, rfl⟩`. Use `GlobalTheory.SoPure.pure_mem_polSo B M hstd f hf φ h1 h2 h3` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SoPure.polSo_eq_span B M hstd]`. Then use the resulting hypothesis.
-/
theorem polSo_eq_DG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W)
    (hstd : ∀ᶠ w in Filter.cofinite, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) :
    PolData B M ⊓ M.So B.ψ B.τ₁ = DG B M (GdSo B M) := by
  rw [GlobalTheory.SoPure.polSo_eq_span B M hstd]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨f, hf, φ, h1, h2, h3, rfl⟩
    exact Submodule.subset_span ⟨f, hf, φ, ⟨h1, h2, Submodule.subset_span h3⟩, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨f, hf, φ, ⟨h1, h2, h3⟩, rfl⟩
    have := GlobalTheory.SoPure.pure_mem_polSo B M hstd f hf φ h1 h2 h3
    rwa [GlobalTheory.SoPure.polSo_eq_span B M hstd] at this

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN φ hSB hev hv1 P hP _ hne`. Establish `hT` using `hM.triple`. Establish `hstd` using `hT.geo.hM'.std`. Take `⟨hP1, hP2, hP3, hP4⟩` from `GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hT`. Take `⟨hchain, hsum⟩` from `howe_pair hKP (GlobalTheory.ThK.Inhab.pairV' hT)`.

Rewrite `hN` using `[polSo_eq_DG B G.M' hstd]`. Conclude with `core hstd (fun φ h => ⟨h.1, h.2.1⟩) hP1 hP2 hP3 hP4 (fun P' v h hh => fin_so hKP hT P' v h hh) hchain hsum hN (φ := φ) ⟨hSB, hev, hv1⟩ P hP hne`.
-/
theorem fibMax : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → ∀ P : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' P → G.M'.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) ≤ P → P ≠ G.M'.Pol B.ψ B.emb → P ≤ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN φ hSB hev hv1 P hP _ hne
  have hT := hM.triple
  have hstd := hT.geo.hM'.std
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hT
  obtain ⟨hchain, hsum⟩ := howe_pair hKP (GlobalTheory.ThK.Inhab.pairV' hT)
  rw [polSo_eq_DG B G.M' hstd] at hN
  exact core hstd (fun φ h => ⟨h.1, h.2.1⟩) hP1 hP2 hP3 hP4 (fun P' v h hh => fin_so hKP hT P' v h hh) hchain hsum hN
    (φ := φ) ⟨hSB, hev, hv1⟩ P hP hne

end GlobalTheory.ThetaFibMaxSo

end
