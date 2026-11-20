import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ConjDict

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

/- English proof (translation)
Unfold `GQ HFinIn HFin at *`. Use `erw [Subgroup.mem_subgroupOf] at h ⊢`. Apply the tactic sequence `convert h using 2 <;> first | rfl | exact (UJ_neg _ _)`.
-/
theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

/- English proof (translation)
Establish `I` using `GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T`. Establish `thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f)` using `fun f => (I.1 f).2.symm`. Establish `thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f)` using `fun f => by`. Use `(I.1 (cj id f)).2` as an intermediate fact. Rewrite `this` using `[cj_id_cj_id]`. Then use the resulting hypothesis.

Establish `hzS : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f))` using `fun w f => by`. Rewrite using `[(I.2 w f).2, cj_id_cj_id]`. Use `{ std := hw.std hecS := hecke_inv hw.hecS hecT := hecke_inv hw.hecT resS := resEta_inv hw.resS resT := resEta_inv hw.resT om_pres := ?_ om_heis := ?_ om_aut := ?_ om_cont := ?_ om_unit := ?_ om_split := ?_ }` and prove the remaining obligations. Introduce `p f hf`. Rewrite using `[cjOm_apply, thS, cj_id_cj_id]`.

Conclude with `hw.om_pres _ _ ((thS f).1 hf)`. Introduce `g h w₀ f hf`. Rewrite using `[cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]`. Use `erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]`. Rewrite using `[hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]`.

Introduce `γ hγ γ' hγ' f hf`. Rewrite using `[cjOm_apply]`. Use `show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0`. Rewrite using `[hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]`. Use `show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0`.

Simplify using the standard rewrite rules. Introduce `f hf w`. Establish `hc` using `hw.om_cont _ ((thS f).1 hf) w`. Simplify using `only [cjOm_apply]`. Conclude with `Complex.continuous_conj.comp (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))`.

Introduce `μ 𝓕 hμ hF p f hf`. Establish `hu` using `hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)`. Simplify using `only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢`. Conclude with `hu`. Introduce `e he g h hg hh x y hx hy`.

Take `⟨r, hr, H⟩` from `hw.om_split e he (negGA S g) h (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy`. Use `⟨r, hr, fun ℓ hℓ f hf => ?_⟩` and prove the remaining obligations. Set `ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun f => starRingEnd ℂ (ℓ (cj id f)) map_add' := fun a b => by`. Establish `: cj id (a + b) = cj id a + cj id b` using `by funext z; simp [cj_id_apply]`. Rewrite using `[this, map_add, map_add]`.

Use the proof step `map_smul' := fun c a => by`. Establish `: cj id (c • a) = starRingEnd ℂ c • cj id a` using `by funext z; simp [cj_id_apply]`. Rewrite using `[this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]`. Use `rfl }`. Establish `h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f)))` using `H ℓ' (fun u hu f' hf' => by show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))`.

Establish `e1` using `hzS u (cj id f')`. Rewrite `e1` using `[cj_id_cj_id]`. Rewrite using `[← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)`. Rewrite `h1` using `[cj_id_cj_id, ← cjOm_apply om (g, h) f]`. Rewrite using `[splitFacO_inv]`.

Establish `h2` using `congrArg (starRingEnd ℂ) h1`. Simplify using `only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2`. Conclude with `h2`.
-/
theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO S T → ℂ),
      heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f)) := fun w f => by
    rw [(I.2 w f).2, cj_id_cj_id]
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [cjOm_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]
    erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]
    rw [hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]
  · intro γ hγ γ' hγ' f hf
    rw [cjOm_apply]
    show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [cjOm_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he (negGA S g) h
      (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add, map_add]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        have e1 := hzS u (cj id f')
        rw [cj_id_cj_id] at e1
        rw [← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← cjOm_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

/- English proof (translation)
Establish `I` using `GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T`. Establish `e0 : star f = cj id f` using `rfl`. Establish `th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f)`. Use `(I.1 (cj id f)).2` as an intermediate fact. Rewrite `this` using `[cj_id_cj_id]`. Then use the resulting hypothesis.

Establish `hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f` using `fun w => by`. Use `(I.2 w (cj id f)).2` as an intermediate fact. Rewrite `this` using `[cj_id_cj_id]`. Rewrite using `[this]`. Conclude with `⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩`.

Rewrite using `[e0]`. Unfold `VacG IsLatVac`. Simplify using `only [th, hz]`.
-/
theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

/- English proof (translation)
Introduce `h1 D hq T L μ0 hL sc G W M hM i hi`. Establish `hv : ∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)` using `fun f => ((vac_star W.ψ_std (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (latRow G i) (star f)).trans (by rw [star_star])).symm`. Use `⟨weil_cjOm W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), weil_cjOm W.ψ (G.V (.core (i + 1))) (G.V (.core i)) _ _ _ (W.om_is (.core i) hi), hv, fun f => ((vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) (star f)) …` and prove the remaining obligations. Establish `e` using `h1 D hq T L μ0 hL sc G W M hM i hi (.chi i 0) (Or.inl rfl) (star f) ((hv f).1 hf) k hk 1 (one_mem _)`. Use `show star (W.om (.chi i 0) (G.toPair (.chi i 0) k 1) (star f)) = f`.

Rewrite using `[e, star_star]`.
-/
theorem conj_dict : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  intro h1 D hq T L μ0 hL sc G W M hM i hi
  have hv : ∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f) := fun f =>
    ((vac_star W.ψ_std (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (latRow G i) (star f)).trans
      (by rw [star_star])).symm
  refine ⟨weil_cjOm W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩),
    weil_cjOm W.ψ (G.V (.core (i + 1))) (G.V (.core i)) _ _ _ (W.om_is (.core i) hi), hv, fun f =>
    ((vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) (star f)).trans (by rw [star_star])).symm,
    fun g h f => rfl, fun g h f => rfl, fun f hf k hk => ?_⟩
  have e := h1 D hq T L μ0 hL sc G W M hM i hi (.chi i 0) (Or.inl rfl) (star f) ((hv f).1 hf) k hk 1 (one_mem _)
  show star (W.om (.chi i 0) (G.toPair (.chi i 0) k 1) (star f)) = f
  rw [e, star_star]

end GlobalTheory.ConjDict

end
