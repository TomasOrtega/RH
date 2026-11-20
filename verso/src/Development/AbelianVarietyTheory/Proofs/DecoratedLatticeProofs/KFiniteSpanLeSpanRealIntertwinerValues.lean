import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleStaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ItOnto
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt)
open GlobalTheory.Chain.IoLift

/- English proof (translation)
The claim follows from `Submodule.span_eq (kFin M τ)`.
-/
theorem kfin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ = kFin M τ := Submodule.span_eq (kFin M τ)

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[inclK_tprod]`.
-/
theorem span_le_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) :
    Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} ≤ LinearMap.range (inclK h) := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩
  rw [inclK_tprod]

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r u`. Rewrite using `[map_smul, inclK_tprod]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`.
-/
theorem range_le_span {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) (y : KT M) :
    inclK h y ∈ Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, inclK_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Introduce `hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt`. Use `choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ`. Establish `h : KSm M` using `hs`. Establish `h' : KSm M'` using `fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1`. Establish `hval` using `GlobalTheory.T.real_intertwiner_values_kFinite D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt`.

Establish `inj` using `inclK_injective h`. Choose the witnesses or unpack the hypotheses as in `⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M, ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)`. Use `⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `span_le_range M h (hval φ (inclK h' y))`.

Express the relevant statement in the definitionally equal form `inclK h (g (It φ (inclK h' y))) = _`. Rewrite using `[← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]`. Take `⟨χS, χT, hω, hexp⟩` from `hW`. Establish `hL` using `fun τ => GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)`. Establish `hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y`.

Introduce `τ X hX φ`. Take `⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v)` from `⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩`. Use `⟨φ', fun y => inj ?_⟩` and prove the remaining obligations. Establish `e` using `hd (inclK h' y)`. Rewrite `e` using `[← hI]`.

Rewrite using `[hI]`. Conclude with `derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e`. Take `⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x}` from `⟨_, rfl⟩`. Establish `hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N`. Introduce `τ X x hx`.

Rewrite `hx`, the goal using `[hNd]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, y, rfl⟩` from `hx`. Take `⟨φ', hφ'⟩` from `hstep τ X X.2 φ`.

Conclude with `Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `h0 : N ≠ ⊥`. Take `⟨φ, y, hne⟩` from `GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor hH D V W S S' M M' θ ω _ It hIt h'`. Introduce `e`.

Use `hne ?_` and prove the remaining obligations. Establish `: I φ y ∈ N` using `hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩`. Rewrite `this` using `[e, Submodule.mem_bot]`. Rewrite using `[← hI, this, map_zero]`. Establish `htop` using `GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0`.

Introduce `w hw`. Take `⟨z, rfl⟩` from `span_le_range M h hw`. Establish `hz : z ∈ N` using `htop ▸ Submodule.mem_top`. Rewrite `hz` using `[hNd]`. Use `clear hw`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, y, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem kfinSpan_le_span_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  intro hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ
  have h : KSm M := hs
  have h' : KSm M' := fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1
  have hval := GlobalTheory.T.real_intertwiner_values_kFinite D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  have inj := inclK_injective h
  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
    refine ⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩
    obtain ⟨z, hz⟩ := span_le_range M h (hval φ (inclK h' y))
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  obtain ⟨χS, χT, hω, hexp⟩ := hW
  have hL := fun τ => GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω
    (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)
  have hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y := by
    intro τ X hX φ
    obtain ⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v) := ⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩
    refine ⟨φ', fun y => inj ?_⟩
    have e := hd (inclK h' y)
    rw [← hI] at e
    rw [hI]
    exact derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e
  obtain ⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x} := ⟨_, rfl⟩
  have hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N := by
    intro τ X x hx
    rw [hNd] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, y, rfl⟩ := hx
      obtain ⟨φ', hφ'⟩ := hstep τ X X.2 φ
      exact Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h0 : N ≠ ⊥ := by
    obtain ⟨φ, y, hne⟩ := GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor hH D V W S S' M M' θ ω _ It hIt h'
    intro e
    refine hne ?_
    have : I φ y ∈ N := hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩
    rw [e, Submodule.mem_bot] at this
    rw [← hI, this, map_zero]
  have htop := GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0
  intro w hw
  obtain ⟨z, rfl⟩ := span_le_range M h hw
  have hz : z ∈ N := htop ▸ Submodule.mem_top
  rw [hNd] at hz
  clear hw
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, y, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ItOnto
