import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc.FamilyModel

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
Both sides reduce to the same expression.
-/
theorem part_succ {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ u) (i : ℕ)
    (hi : i < D.R.m) : part W M ρ Φ u (i + 1) hi = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, hi⟩) (part W M ρ Φ u i hi.le) := rfl

/- English proof (translation)
Unfold `part`. Use `congr 2`. Use function extensionality and compare the values at `j`. Use `h (Fin.castLE hi j) j.2` as an intermediate fact. Unfold `GridData.Weil.datum`.

Rewrite using `[this.1, this.2]`.
-/
theorem part_congr {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (ρ Φ ρ' Φ' u)
    (i : ℕ) (hi : i ≤ D.R.m) (h : ∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) :
    part W M ρ Φ u i hi = part W M ρ' Φ' u i hi := by
  unfold part
  congr 2
  funext j
  have := h (Fin.castLE hi j) j.2
  unfold GridData.Weil.datum
  rw [this.1, this.2]

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM i hi`. Establish `r1 : (G.pS (.chi i 0)).rank = rankV D (i + 1) 0` using `(node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).rank`. Establish `r0 : (G.pT (.chi i 0)).rank = rankV D i 0` using `(node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).rank`. Establish `e1` using `even_rankV D (i + 1) 0`. Establish `e0` using `even_rankV D i 0`.

Use `⟨weil_cjOm _ _ _ _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), ?_, fun ho => ?_, fun he => ?_, fun f => ?_, fun v f Ψ => ?_, fun ρ Φ u => ?_, fun ρ Φ ρ' Φ' u h => part_congr W M ρ Φ ρ' Φ' u i hi.le h, (hM.row i hi.le).haar_fund⟩` and prove the remaining obligations. Use `weil_cjOm _ _ _ _ _ _ (W.om_is (.core i) hi)` as an intermediate fact. Rewrite `this` using `[(G.chr_core hi).1, (G.chr_core hi).2]`. Then use the resulting hypothesis. Rewrite using `[GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr, if_pos (Nat.not_even_iff_odd.1 (by rw [e1]; simpa [Nat.odd_add_one] using ho)), if_neg (Nat.not_odd_iff_even.2 (e0.2 (by simpa using ho)))]`. Conclude with `⟨by simp [GridData.chr, mul_comm], rfl⟩`.

Rewrite using `[GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr, if_pos (Nat.not_even_iff_odd.1 (by rw [e0]; simpa using he)), if_neg (Nat.not_odd_iff_even.2 (e1.2 (by simpa [Nat.odd_add_one] using he)))]`. Conclude with `⟨by simp [GridData.chr, mul_comm], rfl⟩`. Conclude with `vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) f`. Use function extensionality and compare the values at `g`. Rewrite using `[liftT_apply, Pi.star_apply, dn, Complex.star_def, ← integral_conj]`.

Use `integral_congr_ae (.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only [map_mul, cjOm_apply]`. Use `congr 1`. Conclude with `congrArg (fun z => starRingEnd ℂ (W.om (.core i) (negGA _ h, g) z 0)) (cj_id_cj_id f).symm`. Use function extensionality and compare the values at `g`.

Rewrite using `[liftS_apply, Pi.star_apply, part_succ, liftA_apply, Complex.star_def, ← integral_conj]`. Use `integral_congr_ae (.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only [map_mul, cjOm_apply]`. Use `congr 1`. Conclude with `congrArg (fun z => starRingEnd ℂ (W.om (.chi i 0) (negGA _ g, h) z 0)) (cj_id_cj_id _).symm`.
-/
theorem conjRead : ConjRead := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have r1 : (G.pS (.chi i 0)).rank = rankV D (i + 1) 0 := (node_isV G hL (X := .grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).rank
  have r0 : (G.pT (.chi i 0)).rank = rankV D i 0 := (node_isV G hL (X := .grid i 0) ⟨hi.le, Nat.zero_le _⟩).rank
  have e1 := even_rankV D (i + 1) 0
  have e0 := even_rankV D i 0
  refine ⟨weil_cjOm _ _ _ _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩), ?_, fun ho => ?_, fun he => ?_, fun f => ?_,
    fun v f Ψ => ?_, fun ρ Φ u => ?_, fun ρ Φ ρ' Φ' u h => part_congr W M ρ Φ ρ' Φ' u i hi.le h, (hM.row i hi.le).haar_fund⟩
  · have := weil_cjOm _ _ _ _ _ _ (W.om_is (.core i) hi)
    rwa [(G.chr_core hi).1, (G.chr_core hi).2] at this
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e1]; simpa [Nat.odd_add_one] using ho)),
      if_neg (Nat.not_odd_iff_even.2 (e0.2 (by simpa using ho)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · rw [GridData.chrS, GridData.chrT, r1, r0, Formalism.IndefR.Lift.attChr, Formalism.IndefR.Lift.attChr,
      if_pos (Nat.not_even_iff_odd.1 (by rw [e0]; simpa using he)),
      if_neg (Nat.not_odd_iff_even.2 (e1.2 (by simpa [Nat.odd_add_one] using he)))]
    exact ⟨by simp [GridData.chr, mul_comm], rfl⟩
  · exact vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) f
  · funext g
    rw [liftT_apply, Pi.star_apply, dn, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.core i) (negGA _ h, g) z 0)) (cj_id_cj_id f).symm
  · funext g
    rw [liftS_apply, Pi.star_apply, part_succ, liftA_apply, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, cjOm_apply]
    congr 1
    exact congrArg (fun z => starRingEnd ℂ (W.om (.chi i 0) (negGA _ g, h) z 0)) (cj_id_cj_id _).symm

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM ρ Φ u i h k hk g`. Rewrite using `[part_succ W M ρ Φ u i h, liftA_apply, liftA_apply]`. Use `integral_congr_ae (.of_forall fun x => ?_)` and prove the remaining obligations. Use `h1 D hq T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ (h2 D hq T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩) 1 (one_mem _) k hk` as an intermediate fact. Establish `e : W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x (g * k) = W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x g` using `by show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0`.

Establish `e2 : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) = (negGA _ g, x) * (negGA _ k, 1)`. Rewrite using `[map_mul, Prod.mk_mul_mk, mul_one]`. Rewrite using `[e2, map_mul, Module.End.mul_apply]`. Conclude with `congrArg (fun z => W.om (.chi i 0) (negGA _ g, x) z 0) this`. Simplify using `only [e]`.
-/
theorem partFixed (h1 : DepFixed) (h2 : DatumDep) : PartFixed := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  rw [part_succ W M ρ Φ u i h, liftA_apply, liftA_apply]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have := h1 D hq T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ (h2 D hq T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩) 1 (one_mem _) k hk
  have e : W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x (g * k) = W.kerA (.right i 0) (W.datum ρ Φ ⟨i, h⟩) x g := by
    show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
    have e2 : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) = (negGA _ g, x) * (negGA _ k, 1) := by
      rw [map_mul, Prod.mk_mul_mk, mul_one]
    rw [e2, map_mul, Module.End.mul_apply]
    exact congrArg (fun z => W.om (.chi i 0) (negGA _ g, x) z 0) this
  simp only [e]

/- English proof (translation)
Take `⟨χV, χW, om, hom⟩` from `Inhab.exists_weil_pair hψ B.V W`. Take `⟨vS⟩` from `Inhab.nonempty_volM D W.rank ρ`. Take `⟨vb⟩` from `Inhab.nonempty_volM D ρ B.V₀.rank`. Take `⟨vU⟩` from `Inhab.nonempty_volU D ρ`. Take `⟨vW⟩` from `Inhab.nonempty_vol W`.

Establish `hg : gramQ W dW.e = 0` using `by rw [gramQ, ← Matrix.mul_assoc]; exact dW.ee`. Establish `hT` using `CutChar.conjBessel_isTh D ψ hψ ρ B W dW.e hg`. Establish `hn : ∀ x, ‖star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)‖ = 1` using `fun x => by`. Rewrite using `[norm_star, psiBes, psiE]`. Conclude with `hψ.1.2.1 _`.

Use `⟨⟨B.d, χV, χW, om, vS, B.vN, vb, vU, vW, dW.e, Measure.count, g, fun _ x => star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)⟩, ⟨hom, ⟨(isIsoSub_e dW).1, fun u _ => ?_⟩, inferInstanceAs (SFinite Measure.count), continuous_of_discreteTopology, fun _ => hT, hT.cont.comp continuous_snd, fun _ …` and prove the remaining obligations. Use `show adj u.1 ⬝ ((rat (gramQ W dW.e) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W dW.e)`. Rewrite using `[hg, rat_zero, Matrix.zero_mul, Matrix.mul_zero]`.
-/
theorem exists_gen {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {W W₀ : HSp D}
    (dW : HypDec W W₀ ρ) (n : ℕ) (g : Fin n → GA D B.V₀) :
    ∃ a : Gen ψ B.V B.V₀ W ρ (Fin n), a.Is ∧ a.g = g ∧ a.m = Measure.count ∧ a.x₀ = dW.e ∧
      ∀ y, ∀ x ∈ flagN a.d, ‖a.Th y x‖ = 1 := by
  obtain ⟨χV, χW, om, hom⟩ := Inhab.exists_weil_pair hψ B.V W
  obtain ⟨vS⟩ := Inhab.nonempty_volM D W.rank ρ
  obtain ⟨vb⟩ := Inhab.nonempty_volM D ρ B.V₀.rank
  obtain ⟨vU⟩ := Inhab.nonempty_volU D ρ
  obtain ⟨vW⟩ := Inhab.nonempty_vol W
  have hg : gramQ W dW.e = 0 := by rw [gramQ, ← Matrix.mul_assoc]; exact dW.ee
  have hT := CutChar.conjBessel_isTh D ψ hψ ρ B W dW.e hg
  have hn : ∀ x, ‖star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)‖ = 1 := fun x => by
    rw [norm_star, psiBes, psiE]; exact hψ.1.2.1 _
  refine ⟨⟨B.d, χV, χW, om, vS, B.vN, vb, vU, vW, dW.e, Measure.count, g, fun _ x => star (psiBes ψ B.d 1 (vecB B.o B.ζ) x)⟩,
    ⟨hom, ⟨(isIsoSub_e dW).1, fun u _ => ?_⟩, inferInstanceAs (SFinite Measure.count), continuous_of_discreteTopology, fun _ => hT,
      hT.cont.comp continuous_snd, fun _ => 1, measurable_const, fun _ x _ => (hn x).le, fun k => Integrable.of_finite⟩,
    rfl, rfl, rfl, fun _ x _ => hn x⟩
  show adj u.1 ⬝ ((rat (gramQ W dW.e) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W dW.e)
  rw [hg, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

/- English proof (translation)
Take `⟨⟨ψ, hψ⟩, -⟩` from `Inhab.exists_chain D`. Take `⟨a, h1, -, h2, -, h3⟩` from `exists_gen hψ (Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) one_ne_zero) (hypDecThree D) 2 fun _ => 1`. Conclude with `⟨ψ, _, _, _, a, h1, rfl, rfl, h2, h3⟩`.
-/
theorem gen_inhabited (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (a : Gen ψ V V₀ W 1 (Fin 2)),
    a.Is ∧ V₀.rank = 2 ∧ W.rank = 3 ∧ a.m = Measure.count ∧ ∀ y, ∀ x ∈ flagN a.d, ‖a.Th y x‖ = 1 := by
  obtain ⟨⟨ψ, hψ⟩, -⟩ := Inhab.exists_chain D
  obtain ⟨a, h1, -, h2, -, h3⟩ := exists_gen hψ (Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) one_ne_zero) (hypDecThree D) 2 fun _ => 1
  exact ⟨ψ, _, _, _, a, h1, rfl, rfl, h2, h3⟩

/- English proof (translation)
Rewrite using `[Gen.lhs, h, integral_count]`.
-/
theorem lhs_count {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ n : ℕ} (a : Gen ψ V V₀ W ρ (Fin n)) (h : a.m = Measure.count) (G Φ) :
    a.lhs G Φ = ∑ y, ∫ x in a.vN.𝓝, a.Th y x.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (x.1 * a.d.emb0 (a.g y)) ∂a.vN.ν := by
  rw [Gen.lhs, h, integral_count]

/- English proof (translation)
Take `⟨r', hr', c, hc, b', hb', rfl⟩` from `hh`. Conclude with `⟨r * r', mul_mem hr hr', c, hc, b' * b, mul_mem hb' hb, by group⟩`.
-/
theorem strip_stable (W : HSp D) (R : Subgroup (GA D W)) (C : Set (GA D W)) {h r b : GA D W} (hh : h ∈ strip W R C) (hr : r ∈ R)
    (hb : b ∈ GfC W) : r * h * b ∈ strip W R C := by
  obtain ⟨r', hr', c, hc, b', hb', rfl⟩ := hh
  exact ⟨r * r', mul_mem hr hr', c, hc, b' * b, mul_mem hb' hb, by group⟩

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp k`. Proceed by induction on `k with`. Consider the case `zero => exact fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp h)`. Consider the case `succ k ih`. Conclude with `fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu _ h (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h (by omega) (ih (by omega)))`.
-/
theorem top_of_rungs (h0 : Rung0) (hB : RungB) (hJ : RungJ) :
    OnTower fun {_} _ _ _ {G} W M v F Ψ u _ => per0 G M (Ψ 0) u ≠ 0 → ∀ k h, NZB W M v F Ψ u k h := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp k
  induction k with
  | zero => exact fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hp h)
  | succ k ih =>
    exact fun h => hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu _ h
      (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h (by omega) (ih (by omega)))

/- English proof (translation)
Introduce and unpack `⟨ρ, Φ, hne⟩`. Conclude with `hne (by simp [BesL.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun])`.
-/
theorem not_nzb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G)
    (F : Frames G) (u k h) : ¬ NZB W M v F (fun _ => 0) u k h := by
  rintro ⟨ρ, Φ, hne⟩
  exact hne (by simp [BesL.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun])

/- English proof (translation)
Introduce and unpack `⟨_, _, -, ρ, Φ, Φ₀, -, hne⟩`. Conclude with `hne (by simp [JacL.per, fjSrc, fjSrcFun])`.
-/
theorem not_nzj {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G)
    (F : Frames G) (u ΓL k h) : ¬ NZJ W M v F (fun _ => 0) u ΓL k h := by
  rintro ⟨_, _, -, ρ, Φ, Φ₀, -, hne⟩
  exact hne (by simp [JacL.per, fjSrc, fjSrcFun])

end GlobalTheory.Asc.FamilyModel

end
