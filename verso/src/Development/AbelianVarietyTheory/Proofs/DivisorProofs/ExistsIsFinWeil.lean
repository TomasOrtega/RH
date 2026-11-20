import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerFixesOfLocalVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlacesSelectingAdelicIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairActionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

/- English proof (translation)
Rewrite using `[gamF, gamF, coe_rhoF, coe_rhoF, GlobalTheory.T.symplecticForm_unitaryPairAction]`.
-/
theorem gamF_rhoF (p : GA D S × GA D T) (x y : XF S T) :
    gamF ψ S T (rhoF S T p x) (rhoF S T p y) = gamF ψ S T x y := by
  rw [gamF, gamF, coe_rhoF, coe_rhoF, GlobalTheory.T.symplecticForm_unitaryPairAction]

/- English proof (translation)
Rewrite using `[phase, phase, coe_rhoF, ← actO_smul, symplOH, symplOH, GlobalTheory.T.symplecticForm_unitaryPairAction]`.
-/
theorem phase_rhoF (w : 𝓞 D.host.E) (p : GA D S × GA D T) (x : XF S T) :
    phase ψ w (rhoF S T p x) = phase ψ w x := by
  rw [phase, phase, coe_rhoF, ← actO_smul, symplOH, symplOH, GlobalTheory.T.symplecticForm_unitaryPairAction]

structure IsLatRep (hψ : IsCharAF D.host.F ψ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (lam : ℕ →* ℂ)
    (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)) : Prop where
  hw : w + sgO D w = 1
  sd : SelfDual (gamF ψ S T) (latF S T ΛS ΛT)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e ∧ m = opF hψ S T w x e} = ⊤
  fin : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0
  op : ∀ p x v, Om p (opF hψ S T w x v) = opF hψ S T w (rhoF S T p x) (Om p v)
  sd' : ∀ p, SelfDual (gamF ψ S T) ((latF S T ΛS ΛT).map (rhoF S T p))
  vac : ∀ p e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e →
    Om p e = normOp lam (opF hψ S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) e

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_w D`. Establish `H` using `isHeis_opF hψ.1 S T hw`. Establish `hA` using `selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1`. Take `⟨hlev, hmov⟩` from `GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT)`. Establish `hspan` using `GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (smooth_theta hψ.1 hS hT hw hA hlev)`.

Establish `hidx : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0` using `fun p => by`. Take `⟨N, hN, h⟩` from `hmov p.1 p.2`. Use `idx_latF_ne_zero hS hT _ hN ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `h a ha`.

Take `⟨Om, h1, h2⟩` from `GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoF S T) gamF_rhoF hidx`. Conclude with `⟨w, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2⟩`.
-/
theorem exists_isLatRep (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {lam : ℕ →* ℂ}
    (hlam : GoodNorm (sgO D) lam) : ∃ w Om, IsLatRep hψ.1 ΛS ΛT w lam Om := by
  obtain ⟨w, hw⟩ := exists_w D
  have H := isHeis_opF hψ.1 S T hw
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨hlev, hmov⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT)
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (smooth_theta hψ.1 hS hT hw hA hlev)
  have hidx : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0 := fun p => by
    obtain ⟨N, hN, h⟩ := hmov p.1 p.2
    refine idx_latF_ne_zero hS hT _ hN ?_
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoF S T) gamF_rhoF hidx
  exact ⟨w, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2⟩

namespace IsLatRep

variable {hψ : IsCharAF D.host.F ψ} {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
  {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ ΛS ΛT w lam Om)
include h

/- English proof (translation)
Rewrite using `[h.vac p e he]`. Conclude with `normOp_of_le (isHeis_opF hψ S T h.hw) lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he`.
-/
theorem fix_vac {p : GA D S × GA D T} (hp : ∀ a ∈ latF S T ΛS ΛT, rhoF S T p a ∈ latF S T ΛS ΛT) (e : thetaSub ψ S T)
    (he : Fixes (opF hψ S T w) (latF S T ΛS ΛT) e) : Om p e = e := by
  rw [h.vac p e he]
  exact normOp_of_le (isHeis_opF hψ S T h.hw) lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he

/- English proof (translation)
Establish `: Om (g, k) = LinearMap.id`. Use `LinearMap.ext_on h.span ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, e, he, rfl⟩`. Rewrite using `[h.op, rhoF_real hg hk, h.fix_vac (fun a ha => by rwa [rhoF_real hg hk]) e he, LinearMap.id_apply]`. Rewrite using `[this, LinearMap.id_apply]`.
-/
theorem real_triv {g : GA D S} {k : GA D T} (hg : g ∈ GinfC S) (hk : k ∈ GinfC T) (f : thetaSub ψ S T) :
    Om (g, k) f = f := by
  have : Om (g, k) = LinearMap.id := by
    refine LinearMap.ext_on h.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    rw [h.op, rhoF_real hg hk, h.fix_vac (fun a ha => by rwa [rhoF_real hg hk]) e he, LinearMap.id_apply]
  rw [this, LinearMap.id_apply]

/- English proof (translation)
Establish `: Om p ∘ₗ L = L ∘ₗ Om p`. Use `LinearMap.ext_on h.span ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, e, he, rfl⟩`. Establish `he' : Fixes (opF hψ S T w) (latF S T ΛS ΛT) (L e)` using `fun a ha => by rw [← hL, he a ha]`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hL, h.op, h.op, hL, h.vac p e he, h.vac p _ he', normOp_comm (isHeis_opF hψ S T h.hw) lam (h.sd' p) (h.fin p) L hL he]`.

Conclude with `LinearMap.congr_fun this f`.
-/
theorem comm (L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T) (hL : ∀ x v, L (opF hψ S T w x v) = opF hψ S T w x (L v))
    (p : GA D S × GA D T) (f : thetaSub ψ S T) : Om p (L f) = L (Om p f) := by
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on h.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opF hψ S T w) (latF S T ΛS ΛT) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, h.op, h.op, hL, h.vac p e he, h.vac p _ he',
      normOp_comm (isHeis_opF hψ S T h.hw) lam (h.sd' p) (h.fin p) L hL he]
  exact LinearMap.congr_fun this f

/- English proof (translation)
Establish `h1 : opF hψ S T w x f = phase ψ w x • f'` using `Subtype.ext (by rw [coe_opF, Submodule.coe_smul, hf])`. Establish `h2` using `congrArg Subtype.val (h.op p x f)`. Rewrite `h2` using `[h1, map_smul, Submodule.coe_smul, coe_opF, phase_rhoF, coe_rhoF]`. Conclude with `smul_right_injective _ (phase_ne_zero w x) h2`.
-/
theorem heis_fin (p : GA D S × GA D T) (x : XF S T) (f f' : thetaSub ψ S T)
    (hf : (f' : WO S T → ℂ) = heisO ψ S T x f) :
    (Om p f' : WO S T → ℂ) = heisO ψ S T (actO S T p.1 p.2 x) (Om p f) := by
  have h1 : opF hψ S T w x f = phase ψ w x • f' := Subtype.ext (by rw [coe_opF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (h.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opF, phase_rhoF, coe_rhoF] at h2
  exact smul_right_injective _ (phase_ne_zero w x) h2

/- English proof (translation)
Establish `H` using `isHeis_opF hψ S T h.hw`. Establish `hgen` using `GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT`. Take `⟨hlev, -⟩` from `GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT hgen`. Take `⟨h1, h2⟩` from `GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice D S T ΛS ΛT hS hT hgen`. Establish `hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e ∧ m = opF hψ S T w x e}`.

Rewrite using `[h.span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem _ hm`. Take `⟨x, e, he, rfl⟩` from `hm`.

Take `⟨N, hN, hNU⟩` from `hlev _ (GlobalTheory.FinTranslate.isOpen_annSub hψ (XF.fin (w • x)))`. Use `filter_upwards [h1, h2 x x.fin N hN] with p hp hp'`. Take `⟨l, hl, hl'⟩` from `hp'`. Establish `e1 : rhoF S T p x = x + N • XF.mk l (latO_fin hl)` using `XF.ext hl'`. Establish `e2 : gamF ψ S T (w • x) (N • XF.mk l (latO_fin hl)) = 1`.

Establish `e3 : ψ (symplOH S T (w • x : XF S T) (N • l)) = 1` using `(hNU l hl).2`. Rewrite using `[gamF, ← symplOH_add_self, AddChar.map_add_eq_mul, XF.coe_nsmul, XF.coe_mk, e3, one_mul]`. Establish `e4` using `H.comp x (N • XF.mk l (latO_fin hl)) e`. Rewrite `e4` using `[he _ (nsmul_mem (show XF.mk l (latO_fin hl) ∈ latF S T ΛS ΛT from hl) N), e2, one_smul]`. Rewrite using `[h.op, h.fix_vac (fun a ha => hp a ha) e he, e1, ← e4]`.

Consider the case `zero => exact Filter.Eventually.of_forall fun p => map_zero _`. Consider the case `add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]`. Consider the case `smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]`.
-/
theorem eventually_fix (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (f : thetaSub ψ S T) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), Om p f = f := by
  have H := isHeis_opF hψ S T h.hw
  have hgen := GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT
  obtain ⟨hlev, -⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT hgen
  obtain ⟨h1, h2⟩ := GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice D S T ΛS ΛT hS hT hgen
  have hf : f ∈ Submodule.span ℂ
      {m | ∃ x e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e ∧ m = opF hψ S T w x e} := by
    rw [h.span]; trivial
  induction hf using Submodule.span_induction with
  | mem _ hm =>
    obtain ⟨x, e, he, rfl⟩ := hm
    obtain ⟨N, hN, hNU⟩ := hlev _ (GlobalTheory.FinTranslate.isOpen_annSub hψ (XF.fin (w • x)))
    filter_upwards [h1, h2 x x.fin N hN] with p hp hp'
    obtain ⟨l, hl, hl'⟩ := hp'
    have e1 : rhoF S T p x = x + N • XF.mk l (latO_fin hl) := XF.ext hl'
    have e2 : gamF ψ S T (w • x) (N • XF.mk l (latO_fin hl)) = 1 := by
      have e3 : ψ (symplOH S T (w • x : XF S T) (N • l)) = 1 := (hNU l hl).2
      rw [gamF, ← symplOH_add_self, AddChar.map_add_eq_mul, XF.coe_nsmul, XF.coe_mk, e3, one_mul]
    have e4 := H.comp x (N • XF.mk l (latO_fin hl)) e
    rw [he _ (nsmul_mem (show XF.mk l (latO_fin hl) ∈ latF S T ΛS ΛT from hl) N), e2, one_smul] at e4
    rw [h.op, h.fix_vac (fun a ha => hp a ha) e he, e1, ← e4]
  | zero => exact Filter.Eventually.of_forall fun p => map_zero _
  | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]
  | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]

/- English proof (translation)
Use `haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))`. Use `haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))`. Use `continuous_iff_continuousAt.2 fun q => ?_` and prove the remaining obligations. Establish `h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1)` using `(continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)`. Use `continuousAt_const.congr (f := fun _ => (Om q f : WO S T → ℂ) u) ?_` and prove the remaining obligations.

Use `filter_upwards [h1.eventually (h.eventually_fix hS hT f)] with p hp`. Use `conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]`.
-/
theorem cont (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (f : thetaSub ψ S T) (u : WO S T) :
    Continuous fun p => (Om p f : WO S T → ℂ) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WO S T → ℂ) u) ?_
  filter_upwards [h1.eventually (h.eventually_fix hS hT f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

/- English proof (translation)
Take `⟨B, hB, hB'⟩` from `GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form D ψ S T hψ (thetaSub ψ S T) (fun _ hf => hf) μ 𝓕 hμ h𝓕`. Rewrite using `[hB', hB', GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opF hψ S T h.hw) (fun x y => hψ.2.1 _) lam hlam _ h.sd h.span (rhoF S T p) (gamF_rhoF p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) B]`. Introduce `x u v`. Establish `h1 : ∀ u : thetaSub ψ S T, opF hψ S T w x u = phase ψ w x • ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ x.fin u.2⟩` using `fun u => rfl`. Establish `h2 : phase ψ w x * (starRingEnd ℂ) (phase ψ w x) = 1`.

Rewrite using `[Complex.mul_conj', show ‖phase ψ w x‖ = 1 from hψ.2.1 _]`. Simplify using the standard rewrite rules. Rewrite using `[h1, h1, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]`. Conclude with `hB x u v _ _ rfl rfl`.
-/
theorem unit (hlam : GoodNorm (sgO D) lam) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (p : GA D S × GA D T) (f : thetaSub ψ S T) :
    ∫⁻ u in 𝓕, ‖(Om p f : WO S T → ℂ) u‖ₑ ^ 2 ∂μ = ∫⁻ u in 𝓕, ‖(f : WO S T → ℂ) u‖ₑ ^ 2 ∂μ := by
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form D ψ S T hψ (thetaSub ψ S T) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB', hB', GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opF hψ S T h.hw) (fun x y => hψ.2.1 _) lam hlam _ h.sd h.span (rhoF S T p)
    (gamF_rhoF p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) B]
  intro x u v
  have h1 : ∀ u : thetaSub ψ S T, opF hψ S T w x u =
      phase ψ w x • ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ x.fin u.2⟩ := fun u => rfl
  have h2 : phase ψ w x * (starRingEnd ℂ) (phase ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phase ψ w x‖ = 1 from hψ.2.1 _]; simp
  rw [h1, h1, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB x u v _ _ rfl rfl

/- English proof (translation)
Establish `he'` using `isSplitIdem_conj he`. Establish `hm : ∀ (a b : AE D) (x : XF S T), mulF S T a (mulF S T b x) = (a * b) • x` using `fun a b x => smul_smul a b x`. Establish `hc : ∀ (a : AE D) (x : XF S T), rhoF S T (g, k) (mulF S T a x) = mulF S T a (rhoF S T (g, k) x)` using `fun a x => XF.ext (actO_smul _ _ _ _)`. Take `⟨n, hn, hℓ⟩` from `GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opF hψ S T h.hw) lam _ h.sd h.span (rhoF S T (g, k)) (gamF_rhoF _) (h.sd' _) (h.fin _) (Om (g, k)) (h.op _) (h.vac _) (mulF S T e) (mulF S T (cA D e)) (fun x => by rw [hm, he.1, mulF_apply]) (fun x => by rw [ …`. Use `off_smul_actO hg hk (x : WO S T)` as an intermediate fact.

Rewrite `this` using `[sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub]`. Conclude with `this))`. Establish `hi` using `h.fin (g, k)`. Establish `hl` using `hsq _ hi (by`. Rewrite `hi`, the goal using `[idx_latF_eq]`.

Use `GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace D S T e he _ _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _) ?_ ?_ ?_ hi` and prove the remaining obligations. Introduce and unpack `a ha _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨a • x, GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hx, rfl⟩, actO_smul g k a x⟩`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.fin`.

Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ show (1 - (e + cA D e)) • actO S T g k x ∈ _`. Rewrite using `[off_smul_actO hg hk, sub_smul, add_smul, one_smul]`. Conclude with `sub_mem hx (add_mem (idem_smul_mem he.1 _ hx) (idem_smul_mem he'.1 _ hx)))`. Use `⟨(Real.sqrt (idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, k))) : ℕ))⁻¹ * n, mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn), fun ℓ h1 f => ?_⟩` and prove the remaining obligations. Use `hℓ (ℓ ∘ₗ (thetaSub ψ S T).subtype) (fun u m => by` as an intermediate fact.

Establish `h2 : IsHalf (cA D e) (mulF S T (cA D e) u : WO S T)` using `isHalf_smul he'.1 _`. Use `show ℓ (opF hψ S T w (mulF S T (cA D e) u) m : WO S T → ℂ) = ℓ m`. Rewrite using `[coe_opF, phase_half he' w h2, one_smul]`. Conclude with `h1 _ h2 _ m.2) f`. Rewrite `this` using `[hl]`.

Use `push_cast`. Conclude with `this`.
-/
theorem split
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {e : AE D} (he : IsSplitIdem D e) {g : GA D S} {k : GA D T} (hg : SuppAt e S g) (hk : SuppAt e T k) :
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f : thetaSub ψ S T, ℓ (Om (g, k) f) = (r : ℂ) * ℓ f := by
  have he' := isSplitIdem_conj he
  have hm : ∀ (a b : AE D) (x : XF S T), mulF S T a (mulF S T b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hc : ∀ (a : AE D) (x : XF S T), rhoF S T (g, k) (mulF S T a x) = mulF S T a (rhoF S T (g, k) x) :=
    fun a x => XF.ext (actO_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opF hψ S T h.hw) lam _ h.sd h.span (rhoF S T (g, k)) (gamF_rhoF _)
    (h.sd' _) (h.fin _) (Om (g, k)) (h.op _) (h.vac _) (mulF S T e) (mulF S T (cA D e))
    (fun x => by rw [hm, he.1, mulF_apply]) (fun x => by rw [hm, he'.1, mulF_apply])
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul])
    (fun a ha => idem_smul_mem he.1 _ ha) (fun a ha => idem_smul_mem he'.1 _ ha) (hc e) (hc _)
    (fun x => XF.ext (by
      have := off_smul_actO hg hk (x : WO S T)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := h.fin (g, k)
  have hl := hsq _ hi (by
    rw [idx_latF_eq] at hi ⊢
    refine GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace D S T e he _ _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _) ?_ ?_ ?_ hi
    · rintro a ha _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨a • x, GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hx, rfl⟩, actO_smul g k a x⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.fin
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      show (1 - (e + cA D e)) • actO S T g k x ∈ _
      rw [off_smul_actO hg hk, sub_smul, add_smul, one_smul]
      exact sub_mem hx (add_mem (idem_smul_mem he.1 _ hx) (idem_smul_mem he'.1 _ hx)))
  refine ⟨(Real.sqrt (idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (thetaSub ψ S T).subtype) (fun u m => by
    have h2 : IsHalf (cA D e) (mulF S T (cA D e) u : WO S T) := isHalf_smul he'.1 _
    show ℓ (opF hψ S T w (mulF S T (cA D e) u) m : WO S T → ℂ) = ℓ m
    rw [coe_opF, phase_half he' w h2, one_smul]
    exact h1 _ h2 _ m.2) f
  rw [hl] at this
  push_cast
  exact this

/- English proof (translation)
Establish `hoff` using `smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)`. Establish `hP : ∀ a ∈ latF S T ΛS ΛT, mulF S T (algebraMap (AF D.host.F) (AE D) η) a ∈ latF S T ΛS ΛT` using `fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hv.1) _ ha`. Take `⟨b, hb, hb'⟩` from `exists_half_of_nonSplit hv`. Use `GlobalTheory.T.intertwiner_fixes_of_local_vacuum' (isHeis_opF hψ S T h.hw) _ h.sd h.span (rhoF S T (g, k)) (Om (g, k)) (h.op _) (h.fix_vac fun a ha => ?_) (mulF S T (algebraMap (AF D.host.F) (AE D) η)) (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap] …` and prove the remaining obligations. Establish `e1 : actO S T g k a = actO S T g k (algebraMap (AF D.host.F) (AE D) η • (a : WO S T)) + (a - algebraMap (AF D.host.F) (AE D) η • (a : WO S T))`.

Use `hoff (a : WO S T)` as an intermediate fact. Rewrite `this` using `[sub_smul, sub_smul, one_smul, one_smul]`. Rewrite using `[← this, actO_smul, add_sub_cancel]`. Use `show actO S T g k a ∈ latO S T ΛS ΛT fun _ => True`. Rewrite using `[e1]`.

Conclude with `add_mem (GlobalTheory.PlaceModel.latO_le_top _ (hst _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha))) (sub_mem ha (hP a ha))`. Establish `e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) = (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T)`. Rewrite using `[sub_smul, one_smul]`. Both sides reduce to the same expression. Rewrite using `[coe_rhoF, e1, actO_smul, hoff]`.

Establish `e1 : mulF S T (algebraMap (AF D.host.F) (AE D) η) a = 2 • (b • a)`. Rewrite using `[mulF_apply, ← hb', two_mul, add_smul, two_nsmul]`. Establish `e2 : b • a ∈ latF S T ΛS ΛT` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha`. Rewrite using `[coe_opF, coe_mulF, hf _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha), e1, phase_two h.sd w e2, one_smul]`.
-/
theorem inert {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D S} {k : GA D T}
    (hg : SuppPl η S g) (hk : SuppPl η T k)
    (hst : ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), actO S T g k u ∈ (latO S T ΛS ΛT fun w => w = v))
    (f : thetaSub ψ S T) (hf : ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f) : Om (g, k) f = f := by
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have hP : ∀ a ∈ latF S T ΛS ΛT, mulF S T (algebraMap (AF D.host.F) (AE D) η) a ∈ latF S T ΛS ΛT :=
    fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hv.1) _ ha
  obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
  refine GlobalTheory.T.intertwiner_fixes_of_local_vacuum' (isHeis_opF hψ S T h.hw) _ h.sd h.span (rhoF S T (g, k)) (Om (g, k)) (h.op _)
    (h.fix_vac fun a ha => ?_) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap]) hP (fun x => XF.ext ?_) f
    fun a ha => Subtype.ext ?_
  · have e1 : actO S T g k a = actO S T g k (algebraMap (AF D.host.F) (AE D) η • (a : WO S T)) +
        (a - algebraMap (AF D.host.F) (AE D) η • (a : WO S T)) := by
      have := hoff (a : WO S T)
      rw [sub_smul, sub_smul, one_smul, one_smul] at this
      rw [← this, actO_smul, add_sub_cancel]
    show actO S T g k a ∈ latO S T ΛS ΛT fun _ => True
    rw [e1]
    exact add_mem (GlobalTheory.PlaceModel.latO_le_top _ (hst _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha)))
      (sub_mem ha (hP a ha))
  · have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
        (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
      rw [sub_smul, one_smul]; rfl
    rw [coe_rhoF, e1, actO_smul, hoff]
  · have e1 : mulF S T (algebraMap (AF D.host.F) (AE D) η) a = 2 • (b • a) := by
      rw [mulF_apply, ← hb', two_mul, add_smul, two_nsmul]
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    rw [coe_opF, coe_mulF, hf _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha), e1, phase_two h.sd w e2, one_smul]

end IsLatRep

/- English proof (translation)
Set `L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T` to `(heisL ψ S T (realIdem D • u)).restrict fun _ hf => GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (real_smul_real u) hf`. Establish `hL : ∀ m, (L m : WO S T → ℂ) = heisO ψ S T (realIdem D • u) m` using `fun _ => rfl`. Establish `hdec : ∀ z : WO S T, z = realIdem D • z + (1 - realIdem D) • z` using `fun z => by`. Rewrite using `[← add_smul, add_sub_cancel, one_smul]`. Set `f₁ : thetaSub ψ S T` to `⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_smul_fin u) f.2⟩`.

Use `⟨L f₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hL, ← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin u)), ← hdec]`. Rewrite using `[h.comm L (fun x v => Subtype.ext (by`. Rewrite using `[hL, coe_opF, coe_opF, hL, heisO_smul, heisO_comm, symplO_real_fin S T (real_smul_real u) x.fin, AddChar.map_zero_eq_one, one_smul])), hL,`. Use the proof step `h.heis_fin (g, k) (XF.mk _ (fin_smul_fin u)) f f₁ rfl, XF.coe_mk, actO_smul,`.

Use the proof step `← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin _)),`. Use the proof step `← smul_actO (real_smul_mt hg) (real_smul_mt hk) u, ← hdec]`.
-/
theorem IsLatRep.Heisenberg₂ (hψ : IsStdChar D ψ (-1)) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ.1 ΛS ΛT w lam Om)
    {g : GA D S} {k : GA D T} (hg : g ∈ GfC S) (hk : k ∈ GfC T) (u : WO S T) (f : thetaSub ψ S T) :
    ∃ f' : thetaSub ψ S T, (f' : WO S T → ℂ) = heisO ψ S T u f ∧
      (Om (g, k) f' : WO S T → ℂ) = heisO ψ S T (actO S T g k u) (Om (g, k) f) := by
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (heisL ψ S T (realIdem D • u)).restrict
    fun _ hf => GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (real_smul_real u) hf
  have hL : ∀ m, (L m : WO S T → ℂ) = heisO ψ S T (realIdem D • u) m := fun _ => rfl
  have hdec : ∀ z : WO S T, z = realIdem D • z + (1 - realIdem D) • z := fun z => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let f₁ : thetaSub ψ S T := ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_smul_fin u) f.2⟩
  refine ⟨L f₁, ?_, ?_⟩
  · rw [hL, ← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin u)), ← hdec]
  · rw [h.comm L (fun x v => Subtype.ext (by
        rw [hL, coe_opF, coe_opF, hL, heisO_smul, heisO_comm, symplO_real_fin S T (real_smul_real u) x.fin,
          AddChar.map_zero_eq_one, one_smul])), hL,
      h.heis_fin (g, k) (XF.mk _ (fin_smul_fin u)) f f₁ rfl, XF.coe_mk, actO_smul,
      ← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin _)),
      ← smul_actO (real_smul_mt hg) (real_smul_mt hk) u, ← hdec]

/- English proof (translation)
Take `⟨lam, hlam, hsq⟩` from `exists_goodNorm D`. Take `⟨w, Om, h⟩` from `exists_isLatRep hψ hS hT hlam`. Take `⟨ε, hε⟩` from `GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D`. Take `⟨c, c1, c2, c3, c4⟩` from `GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε S χT _ hχT hrT`. Take `⟨d, d1, d2, d3, d4⟩` from `GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε T χS _ hχS hrS`.

Set `z : GA D S × GA D T → Circle` to `fun p => (c p.1)⁻¹ * d p.2`. Establish `z1 : z 1 = 1` using `by simp [z]`. Establish `z2 : ∀ p q, z (p * q) = z p * z q` using `fun p q => by`. Simplify using `only [z, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]`. Conclude with `mul_mul_mul_comm _ _ _ _`.

Establish `z3 : Continuous z` using `(c1.comp continuous_fst).inv.mul (d1.comp continuous_snd)`. Take `⟨om, hom⟩` from `exists_extend (thetaSub ψ S T) ({ toFun := fun p => (z p : ℂ) • Om p map_one' := by rw [z1, Circle.coe_one, one_smul, map_one] map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))`. Establish `ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WO S T → ℂ)` using `fun p f hf => hom p ⟨f, hf⟩`. Use `⟨om, ⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_, fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_, fun v η hv g k hg hk hst f hf hfix => ?_⟩` and prove the remaining obligations. Rewrite using `[ho p f hf]`.

Conclude with `(thetaSub ψ S T).smul_mem _ (Om p ⟨f, hf⟩).2`. Simplify using `only [ho _ f hf, Pi.smul_apply, smul_eq_mul]`. Conclude with `(continuous_subtype_val.comp z3).mul (h.cont hS hT ⟨f, hf⟩ u)`. Rewrite using `[← h.unit hlam μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]`. Use `lintegral_congr fun u => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]`. Rewrite using `[ho _ f hf, h.real_triv hg hk, show z (g, k) = 1 by simp [z, c2 g hg, d2 k hk], Circle.coe_one, one_smul]`. Take `⟨f', h1, h2⟩` from `h.Heisenberg₂ hψ hg hk u ⟨f, hf⟩`. Rewrite using `[ho _ f hf, heisO_smul, ← h2, ← h1]`. Conclude with `hom _ f'`.

Take `⟨r, hr, h1⟩` from `h.split hsq he hg hk`. Use `⟨r, hr, fun ℓ hℓ f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul, show z (g, k) = splitFacO χS χT x y by simp only [z, splitFacO, c4 e he g x hg hx, d4 e he k y hk hy]]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ho _ f hf, h.inert hv hg hk (fun u hu => (hst u).1 hu) ⟨f, hf⟩ hfix, show z (g, k) = 1 by simp [z, c3 v η hv g hg, d3 v η hv k hk], Circle.coe_one, one_smul]`.
-/
theorem exists_isFinWeil (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (χS χT : (AE D)ˣ →* Circle)
    (hχS : IsHeckeChar D χS) (hχT : IsHeckeChar D χT) (hrS : ResEta D χS S.rank) (hrT : ResEta D χT T.rank) :
    ∃ om, IsFinWeil ψ S T ΛS ΛT χS χT om := by
  obtain ⟨lam, hlam, hsq⟩ := exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D
  obtain ⟨c, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε S χT _ hχT hrT
  obtain ⟨d, d1, d2, d3, d4⟩ := GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε T χS _ hχS hrS
  let z : GA D S × GA D T → Circle := fun p => (c p.1)⁻¹ * d p.2
  have z1 : z 1 = 1 := by simp [z]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := (c1.comp continuous_fst).inv.mul (d1.comp continuous_snd)
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_, fun v η hv g k hg hk hst f hf hfix => ?_⟩
  · rw [ho p f hf]
    exact (thetaSub ψ S T).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (h.cont hS hT ⟨f, hf⟩ u)
  · rw [← h.unit hlam μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, h.real_triv hg hk, show z (g, k) = 1 by simp [z, c2 g hg, d2 k hk], Circle.coe_one, one_smul]
  · obtain ⟨f', h1, h2⟩ := h.Heisenberg₂ hψ hg hk u ⟨f, hf⟩
    rw [ho _ f hf, heisO_smul, ← h2, ← h1]
    exact hom _ f'
  · obtain ⟨r, hr, h1⟩ := h.split hsq he hg hk
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacO χS χT x y by simp only [z, splitFacO, c4 e he g x hg hx, d4 e he k y hk hy]]
    ring
  · rw [ho _ f hf, h.inert hv hg hk (fun u hu => (hst u).1 hu) ⟨f, hf⟩ hfix,
      show z (g, k) = 1 by simp [z, c3 v η hv g hg, d3 v η hv k hk], Circle.coe_one, one_smul]

end GlobalTheory.FinWeilO

end
