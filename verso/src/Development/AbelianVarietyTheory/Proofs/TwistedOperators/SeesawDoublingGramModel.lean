import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingFrameModelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineSumV'

/- English proof (translation)
Take `⟨γ, hγ, hγt⟩` from `GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hJ`. Take `⟨Dop, hDP, hD⟩` from `(GlobalTheory.T.polynomial_datum_action_of_pair hP _ _ D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' Xc.α (Xc.α / Xc.β) om' _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V' hT)).2.2.1 γ hγ`. Establish `hfun : ∀ Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ, ∀ x, (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om' (1, γ (Multiplicative.ofAdd t)) Φ x`. Introduce `Φ x`. Use function extensionality and compare the values at `t`.

Rewrite using `[hγt t]`. Introduce `ΦD hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `zero`. Use `⟨0, zero_mem _, fun x => ?_⟩` and prove the remaining obligations.

Simplify using `using hasDerivAt_const (0 : ℝ) (0 : ℂ)`. Consider the case `add p q _ _ hp hq`. Take `⟨p', hp', hdp⟩` from `hp`. Take `⟨q', hq', hdq⟩` from `hq`. Use `⟨p' + q', add_mem hp' hq', fun x => ?_⟩` and prove the remaining obligations.

Establish `e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) = fun t => om' (1, kapX X e hJ (oneP θ X τ Y t)) p x + om' (1, kapX X e hJ (oneP θ X τ Y t)) q x`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Conclude with `(hdp x).add (hdq x)`.

Consider the case `smul c p _ hp`. Take `⟨p', hp', hdp⟩` from `hp`. Use `⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩` and prove the remaining obligations. Establish `e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) = fun t => c * om' (1, kapX X e hJ (oneP θ X τ Y t)) p x`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Simplify using `using (hdp x).const_mul c`. Consider the case `mem Φ hΦ`. Take `⟨f, φ, hf, hSB, hev, rfl⟩` from `hΦ`.

Establish `hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1` using `(hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2`. Use `⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Conclude with `((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x`.
-/
theorem exists_deriv_factor (hP : GlobalTheory.FunPr.Hypotheses₂) (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hJ
  obtain ⟨Dop, hDP, hD⟩ := (GlobalTheory.T.polynomial_datum_action_of_pair hP _ _ D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' Xc.α (Xc.α / Xc.β) om' _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V' hT)).2.2.1 γ hγ
  have hfun : ∀ Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ, ∀ x,
      (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om' (1, γ (Multiplicative.ofAdd t)) Φ x := by
    intro Φ x; funext t; rw [hγt t]
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q _ _ hp hq =>
    obtain ⟨p', hp', hdp⟩ := hp
    obtain ⟨q', hq', hdq⟩ := hq
    refine ⟨p' + q', add_mem hp' hq', fun x => ?_⟩
    have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) =
        fun t => om' (1, kapX X e hJ (oneP θ X τ Y t)) p x + om' (1, kapX X e hJ (oneP θ X τ Y t)) q x := by
      funext t; simp
    rw [e1]
    exact (hdp x).add (hdq x)
  | smul c p _ hp =>
    obtain ⟨p', hp', hdp⟩ := hp
    refine ⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩
    have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) =
        fun t => c * om' (1, kapX X e hJ (oneP θ X τ Y t)) p x := by
      funext t; simp
    rw [e1]
    simpa using (hdp x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩
    rw [hfun]
    exact ((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x

/- English proof (translation)
Introduce `hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD`. Establish `hex : ∀ (Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD Γ.M' Bs.ψ Bs.emb → ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0` using `fun Φ hΦ i => exists_deriv_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ`. Proceed by induction on `hΦD using Submodule.span_induction with`. Consider the case `zero`. Introduce `Ψ hΨ x`.

Establish `h0 : ∀ i, Ψ i x = 0`. Introduce `i`. Use `((hΨ i).2 x).unique ?_` and prove the remaining obligations. Simplify using `using hasDerivAt_const (0 : ℝ) (0 : ℂ)`. Simplify using `only [h0, Finset.sum_const_zero]`.

Simplify using `using hasDerivAt_const (0 : ℝ) (0 : ℂ)`. Consider the case `add p q hp hq ihp ihq`. Introduce `Ψ hΨ x`. Use `choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)`. Use `choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)`.

Establish `hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x`. Introduce `i`. Use `((hΨ i).2 x).unique ?_` and prove the remaining obligations. Establish `e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) = fun t => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x + om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Conclude with `(hdp i x).add (hdq i x)`. Establish `e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) = fun t => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x + om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Rewrite using `[e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]`. Conclude with `(ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)`. Consider the case `smul c p hp ihp`. Introduce `Ψ hΨ x`.

Use `choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)`. Establish `hsplit : ∀ i, Ψ i x = c * Ψp i x`. Introduce `i`. Use `((hΨ i).2 x).unique ?_` and prove the remaining obligations. Establish `e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) = fun t => c * om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x`.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Conclude with `(hdp i x).const_mul c`. Establish `e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) = fun t => c * om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x`.

Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite using `[e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]`. Conclude with `(ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c`. Consider the case `mem Φ hΦ`.

Take `⟨f, φ, hf, hSB, hev, rfl⟩` from `hΦ`. Conclude with `hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl f hf φ hSB hev`.
-/
theorem prodRule (hpure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a' × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
    ∀ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0) : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD
  have hex : ∀ (Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD Γ.M' Bs.ψ Bs.emb → ∀ i : Fin l.length,
      ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0 :=
    fun Φ hΦ i => exists_deriv_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ
  induction hΦD using Submodule.span_induction with
  | zero =>
    intro Ψ hΨ x
    have h0 : ∀ i, Ψ i x = 0 := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simp only [h0, Finset.sum_const_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q hp hq ihp ihq =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)
    have hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) =
          fun t => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x +
            om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).add (hdq i x)
    have e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) =
        fun t => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x +
          om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)
  | smul c p hp ihp =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    have hsplit : ∀ i, Ψ i x = c * Ψp i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) =
          fun t => c * om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).const_mul c
    have e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) =
        fun t => c * om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    exact hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl f hf φ hSB hev

/- English proof (translation)
Introduce `hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Φ₁D hΦ₁`. Establish `hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0` using `fun i => exists_deriv_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD`. Use `choose Ψ hΨ hder using hex`. Use `⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Rewrite using `[Finset.sum_apply]`. Conclude with `(hΦ₁ x).unique (prodRule GlobalTheory.T.seesaw_doubling_frame_model hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Ψ (fun i => ⟨hΨ i, hder i⟩) x)`.
-/
theorem derSum : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Φ₁D hΦ₁
  have hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0 :=
    fun i => exists_deriv_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD
  choose Ψ hΨ hder using hex
  refine ⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩
  funext x
  rw [Finset.sum_apply]
  exact (hΦ₁ x).unique (prodRule GlobalTheory.T.seesaw_doubling_frame_model hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Ψ (fun i => ⟨hΨ i, hder i⟩) x)

end GlobalTheory.LineSumV'
