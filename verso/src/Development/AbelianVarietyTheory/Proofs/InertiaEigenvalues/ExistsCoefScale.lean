import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.SeriesTie.Scale in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κw v₀ O hC _ hio i hO c hc u hu B hB hBo`. Establish `hcV : (R.cV i).Is` using `hC.models.cV i`. Establish `hinf : IsInfFam R.θ` using `hBo.θ ▸ hB.frame.vac.2.inf`. Take `⟨gramR, c0R, c0L, hft, hbc⟩` from `hO.2.lift.c0`. Establish `hfield : (inC (O i).c').comp (O i).jL = D.what₂.embLL` using `hO.2.lift.field`.

Take `⟨e, he0, he⟩` from `GlobalTheory.CoefReal.exists_real_model (Vc D i) R.θ (R.cV i) (lamV D i) (c0L i) hinf hcV (hft.mapL i)`. Establish `hce : c = e.toLinearMap`. Use `LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)) fun k => ?_` and prove the remaining obligations. Take `⟨v', hv', hv0⟩` from `hbc (bVV D.what₂.LL (lamV D i) k)`. Use `(hc v' _ ?_).trans (hv0.trans (he0 _).symm)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `MvPolynomial.map D.what₂.embLL _ = _`. Rewrite using `[hv', MvPolynomial.map_map, hfield]`. Take `⟨u', w₀, hu', -, hw⟩` from `FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio`. Establish `huu : u' = u` using `funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)`. Rewrite `hw` using `[huu]`.

Establish `hT` using `io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)`. Establish `hlam : B.w.lam = lamV D i` using `hBo.lam`. Establish `hΔ : B.w.delta (Wc D i).rank = RealDat.Delta i` using `hBo.delta`. Establish `hpq` using `GlobalTheory.CoefLatConj.pq_le hB`. Establish `hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ h : GinfC (Vc D i), U.map ((R.cV i).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤` using `fun U hU => hcV.2.2.2.2 U fun h => by`.

Take `⟨a, ha, k, hk, rfl⟩` from `(GlobalTheory.UnitarySplit.real_finite_split D _).1 h`. Rewrite using `[map_mul, hcV.1 k hk, mul_one]`. Conclude with `hU ⟨a, ha⟩`. Establish `hΔ0` using `GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i`. Use `set x := PiTensorProduct.tprod ℂ u`.

Establish `hharm : ∀ w, R.ioP i x w ∈ harm (Wc D i).rank B.w B.F.BS`. Break down `hirr ((harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)) (fun h => by` into its components or cases. Introduce and unpack `_ ⟨w, hw', rfl⟩`. Rewrite using `[Submodule.mem_comap, hT h h.2]`. Conclude with `fockGL_mem_harm _ _ _ hw') with h | h`.

Establish `h0 : w₀ ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)`. Rewrite using `[Submodule.mem_comap, hw, ← hΔ]`. Conclude with `delta_mem_harm _ _`. Rewrite `h0` using `[h, Submodule.mem_bot]`. Rewrite `hw` using `[h0, map_zero]`.

Conclude with `absurd hw.symm hΔ0`. Conclude with `fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x))`. Use `haveI := hcV.2.2.2.1`. Take `⟨κ, hcc⟩` from `GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D i)) (R.cV i).W (GLR D (Vc D i).rank → ℂ) (fun h => (R.cV i).ρ h) (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D i) h)⁻¹ * y) (harmFn (Wc D i).rank B.w B.F.BS ∘ₗ R.ioP i x) (coefLin (lamV D i) ∘ₗ e.symm.to …`. Introduce and unpack `_ ⟨w, rfl⟩`.

Establish `h1 : harmFn (Wc D i).rank B.w B.F.BS (R.ioP i x w) ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS)` using `Submodule.mem_map_of_mem (hharm w)`. Rewrite `h1` using `[GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam]`. Use `Submodule.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨G', rfl⟩`. Conclude with `⟨e G', congrArg (coefLin _) (e.symm_apply_apply G')⟩)`.

Use the proof step `(fun h w => funext fun y => by`. Express the relevant statement in the definitionally equal form `harmFn _ B.w B.F.BS (R.ioP i x ((R.cV i).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP i x w) _`. Rewrite using `[hT h h.2, ← hBo.θ]`. Conclude with `harmFn_fockGL _ _ _ _ _)`. Use the proof step `(fun h w => funext fun y => by`.

Take `⟨v, rfl⟩` from `e.surjective w`. Express the relevant statement in the definitionally equal form `coefLin _ (e.symm ((R.cV i).ρ h (e v))) y = coefLin _ (e.symm (e v)) _`. Rewrite using `[he h h.2, e.symm_apply_apply, e.symm_apply_apply]`. Conclude with `coefFn_translate _ _ _ _)`. Substitute `hce` using the available equality.

Use `⟨κ, fun h0 => hΔ0 ?_, fun y => hharm _, fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hcc w₀`. Rewrite `h1` using `[h0, zero_smul, LinearMap.comp_apply, hw]`. Conclude with `GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1`. Establish `h1` using `LinearMap.congr_fun hcc (e y)`.

Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1`. Conclude with `h1`.
-/
theorem exists_coef_scale : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.valSpace) ∧ ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC _ hio i hO c hc u hu B hB hBo
  have hcV : (R.cV i).Is := hC.models.cV i
  have hinf : IsInfFam R.θ := hBo.θ ▸ hB.frame.vac.2.inf

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hfield : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hO.2.lift.field
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D i) R.θ (R.cV i) (lamV D i) (c0L i) hinf hcV (hft.mapL i)
  have hce : c = e.toLinearMap := by
    refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)) fun k => ?_
    obtain ⟨v', hv', hv0⟩ := hbc (bVV D.what₂.LL (lamV D i) k)
    refine (hc v' _ ?_).trans (hv0.trans (he0 _).symm)
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]

  obtain ⟨u', w₀, hu', -, hw⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw

  have hT := io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hlam : B.w.lam = lamV D i := hBo.lam
  have hΔ : B.w.delta (Wc D i).rank = RealDat.Delta i := hBo.delta
  have hpq := GlobalTheory.CoefLatConj.pq_le hB
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ h : GinfC (Vc D i), U.map ((R.cV i).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hcV.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
  set x := PiTensorProduct.tprod ℂ u
  have hharm : ∀ w, R.ioP i x w ∈ harm (Wc D i).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x))

  haveI := hcV.2.2.2.1
  obtain ⟨κ, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D i)) (R.cV i).W (GLR D (Vc D i).rank → ℂ) (fun h => (R.cV i).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D i) h)⁻¹ * y)
    (harmFn (Wc D i).rank B.w B.F.BS ∘ₗ R.ioP i x) (coefLin (lamV D i) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D i).rank B.w B.F.BS (R.ioP i x w) ∈
          (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨G', rfl⟩
      exact ⟨e G', congrArg (coefLin _) (e.symm_apply_apply G')⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP i x ((R.cV i).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP i x w) _
      rw [hT h h.2, ← hBo.θ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV i).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  subst hce
  refine ⟨κ, fun h0 => hΔ0 ?_, fun y => hharm _, fun y => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · have h1 := LinearMap.congr_fun hcc (e y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    exact h1

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo`. Take `⟨κ, hκ0, hval, hκ⟩` from `exists_coef_scale D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo`. Set `Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank` to `R.ioP i (PiTensorProduct.tprod ℂ u) ∘ₗ c`. Establish `hlam` using `hBo.lam`. Use `⟨κ, hκ0, hκ, existsUnique_eq Φ hB hlam hκ0 hval hκ, fun K _ _ σ emb Oc hcoef => ⟨fun h => coefLat_eq_span Φ hB hlam hκ0 hval hκ σ emb Oc h, fun τ hτ => ⟨fun h x x' hx => conj_mem_iff Φ hlam hκ0 hval hκ σ emb Oc τ hτ h hx, ?_⟩⟩⟩` and prove the remaining obligations.

Introduce `ψ1 ψ1' h1 h1' hcc hfd f f' hff`. Prove the components needed by the constructor for the conclusion. Conclude with `GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb Oc hcoef τ hτ ψ1 ψ1' h1 h1' hcc hfd f f' hff`. Introduce `hf'`. Establish `hτ' : ∀ a : K, τ.symm (σ a) = σ a` using `fun a => by rw [τ.symm_apply_eq, hτ]`.

Establish `hcoef' : IsCoefRing σ emb (Oc.map (τ : ℂ →+* ℂ))` using `⟨hcoef.emb, fun a => Subring.mem_map.2 ⟨_, hcoef.int a, hτ _⟩⟩`. Establish `hOO : (Oc.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = Oc`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Take `⟨_, hw, rfl⟩` from `Subring.mem_map.1 hz`. Take `⟨b, hb, rfl⟩` from `Subring.mem_map.1 hw`. Simplify using `using hb`. Introduce `hz`. Conclude with `Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩`.

Establish `hτ0 : τ.symm κ ≠ 0` using `(map_ne_zero _).2 hκ0`. Establish `key` using `GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb (Oc.map (τ : ℂ →+* ℂ)) hcoef' τ.symm hτ' ψ1' ψ1 h1' h1 hcc.symm hfd.symm f' f (fun h => by`. Take `⟨x, x', hx, e1, e2⟩` from `hff h`. Establish `hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x` using `Subtype.ext hx`. Establish `e3 : GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D i) ((τ κ / κ) • x') = (κ / τ.symm κ) • x`.

Rewrite using `[map_smulₛₗ, hx', mapVV_symm_mapVV]`. Use `congr 1`. Simplify using `[map_div₀]`. Use `⟨(τ κ / κ) • x', (κ / τ.symm κ) • x, (congrArg Subtype.val e3).symm, e2, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, smul_smul, show τ.symm κ / κ * (κ / τ.symm κ) = 1 by field_simp, one_smul]`.

Use the proof step `rfl) hf'`. Rewrite `key` using `[hOO]`. Then use the resulting hypothesis.
-/
theorem coefLat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ (∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) ∧ ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (Oc : Subring ℂ), IsCoefRing σ emb Oc → (∀ h : Bridge.Gf (Vc D i), B.coefLat σ emb Oc h = Submodule.span Oc {P | ∃ Fv ∈ nabAtr emb (lamV D i) (B.latAt h), P = R.ioP i (PiTensorProduct.tprod ℂ u) (c (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) Fv))}) ∧ ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → (∀ (h : Bridge.Gf (Vc D i)) (x x' : VsV D i ℂ), ConjVec i τ x x' → (R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.coefLat σ emb Oc h ↔ R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x')) ∈ B.coefLat σ emb (Oc.map (τ : ℂ →+* ℂ)) h)) ∧ ∀ (ψ1 ψ1' : Twist D Circle), ψ1.Good → ψ1'.Good → ConjChar τ ψ1 ψ1' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧ f' h = R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x'))) → (f ∈ B.mtLat σ emb Oc ψ1 ↔ f' ∈ B.mtLat σ emb (Oc.map (τ : ℂ →+* ℂ)) ψ1') := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  obtain ⟨κ, hκ0, hval, hκ⟩ := exists_coef_scale D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  let Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank := R.ioP i (PiTensorProduct.tprod ℂ u) ∘ₗ c
  have hlam := hBo.lam
  refine ⟨κ, hκ0, hκ, existsUnique_eq Φ hB hlam hκ0 hval hκ, fun K _ _ σ emb Oc hcoef =>
    ⟨fun h => coefLat_eq_span Φ hB hlam hκ0 hval hκ σ emb Oc h,
      fun τ hτ => ⟨fun h x x' hx => conj_mem_iff Φ hlam hκ0 hval hκ σ emb Oc τ hτ h hx, ?_⟩⟩⟩
  intro ψ1 ψ1' h1 h1' hcc hfd f f' hff
  constructor
  · exact GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb Oc hcoef τ hτ ψ1 ψ1' h1 h1' hcc hfd f f' hff
  · intro hf'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hcoef' : IsCoefRing σ emb (Oc.map (τ : ℂ →+* ℂ)) :=
      ⟨hcoef.emb, fun a => Subring.mem_map.2 ⟨_, hcoef.int a, hτ _⟩⟩
    have hOO : (Oc.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = Oc := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    have hτ0 : τ.symm κ ≠ 0 := (map_ne_zero _).2 hκ0
    have key := GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb (Oc.map (τ : ℂ →+* ℂ)) hcoef' τ.symm hτ' ψ1' ψ1 h1' h1
      hcc.symm hfd.symm f' f (fun h => by
        obtain ⟨x, x', hx, e1, e2⟩ := hff h
        have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
        have e3 : GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D i) ((τ κ / κ) • x') = (κ / τ.symm κ) • x := by
          rw [map_smulₛₗ, hx', mapVV_symm_mapVV]
          congr 1
          simp [map_div₀]
        refine ⟨(τ κ / κ) • x', (κ / τ.symm κ) • x, (congrArg Subtype.val e3).symm, e2, ?_⟩
        rw [e1, smul_smul, show τ.symm κ / κ * (κ / τ.symm κ) = 1 by field_simp, one_smul]
        rfl) hf'
    rwa [hOO] at key

end GlobalTheory.CoefLatConj
