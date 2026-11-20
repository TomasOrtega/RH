import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ItKFin

/- English proof (translation)
Rewrite using `[inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Use `congr 2`. Use function extensionality and compare the values at `ρ`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Use extensionality with `w`. Simplify using `[hg]`. Use extensionality with `w`. Simplify using `[e]`.
-/
theorem inclT_mapFactor {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Module.End ℂ (M.sm τ)) (A : M.H τ →ₗ[ℂ] M.H τ) (hg : ∀ w, ((g w : M.sm τ) : M.H τ) = A w) (y : SmT M) :
    inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ g y) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ A) (inclT M y) := by
  rw [inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 2
  funext ρ
  by_cases e : ρ = τ
  · subst e
    ext w
    simp [hg]
  · ext w
    simp [e]

/- English proof (translation)
Introduce `D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v`. Take `⟨χS, χT, hWD, hexp⟩` from `hW`. Establish `hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)` using `rfl`. Establish `hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧ inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v))`. Introduce `τ h hh`.

Take `⟨a, b, -, -, hc⟩` from `GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne`. Establish `h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ)` using `⟨one_mem _, by simp⟩`. Use `hc h hh 1 h1 P` as an intermediate fact. Establish `e1 : (Fr.ofModel M').elt θ τ 1 = 1`. Establish `hd'` using `(Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)`.

Use `show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1`. Rewrite using `[Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']`. Conclude with `GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ`. Rewrite `this` using `[e1, ptF_ofModel, hp, ← map_smul, ← hp]`. Use `⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩` and prove the remaining obligations.

Conclude with `(MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)`. Establish `hJ` using `fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1`. Establish `hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ` using `fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))`. Set `fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ)` to `fun τ h hh => (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)`. Establish `hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h` using `fun τ h => by`.

Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]`. Establish `hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M), inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y)`. Introduce `τ h hh y`. Rewrite using `[inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]`.

Simplify using `only [actT, DSModel.rep, hconj]`. Establish `hx` using `GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ) (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)`. Set `E : Submodule ℂ (SmT M)` to `(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)`. Establish `hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤ (E.map L).map (M.sm τ).subtype`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Take `⟨P', hP', e⟩` from `hA τ k hk`. Establish `e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v)` using `(tensorLaw D V S M).inj (by rw [e, hact τ k hk])`. Establish `e3` using `LinearMap.congr_fun (hL (fK τ k hk)) (It P v)`. Simplify using `only [LinearMap.comp_apply] at e3`.

Use `⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[e2, e3]`. Both sides reduce to the same expression. Establish `hσ` using `(M.ds τ).2.2.1`. Use `⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩, fun g hg w hw => ?_⟩` and prove the remaining obligations.

Simplify using `only [hσ.1.1]`. Both sides reduce to the same expression. Use `Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk', rfl⟩`. Use `Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩` and prove the remaining obligations.

Simplify using `only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `hx`. Rewrite using `[← hz]`. Use `clear hz`.

Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r n`. Rewrite using `[map_smul, PiTensorProduct.map_tprod]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`.
-/
theorem itKFin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v
  obtain ⟨χS, χT, hWD, hexp⟩ := hW
  have hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) := rfl
  have hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧
      inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v)) := by
    intro τ h hh
    obtain ⟨a, b, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ
      (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) := ⟨one_mem _, by simp⟩
    have := hc h hh 1 h1 P
    have e1 : (Fr.ofModel M').elt θ τ 1 = 1 := by
      have hd' := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
      show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ
    rw [e1, ptF_ofModel, hp, ← map_smul, ← hp] at this
    refine ⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)
  have hJ := fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
  have hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ :=
    fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
      ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))
  let fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ) := fun τ h hh =>
    (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)
  have hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h :=
    fun τ h => by
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M),
      inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y) := by
    intro τ h hh y
    rw [inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]
    simp only [actT, DSModel.rep, hconj]
  have hx := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ)
    (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by
      show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)
      let E : Submodule ℂ (SmT M) := (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)
      have hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤
          (E.map L).map (M.sm τ).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨P', hP', e⟩ := hA τ k hk
        have e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v) :=
          (tensorLaw D V S M).inj (by rw [e, hact τ k hk])
        have e3 := LinearMap.congr_fun (hL (fK τ k hk)) (It P v)
        simp only [LinearMap.comp_apply] at e3
        refine ⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩
        rw [e2, e3]
        rfl
      have hσ := (M.ds τ).2.2.1
      refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
        fun g hg w hw => ?_⟩
      · simp only [hσ.1.1]; rfl
      · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)
        rintro _ ⟨k, hk', rfl⟩
        refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
        simp only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]; rfl
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  clear hz
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r n =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end GlobalTheory.ItKFin
