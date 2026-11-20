import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseCmp
open GlobalTheory.FlatVecSum (princ princ_good)
section Real
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle}
  {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ}
end Real
section Coef
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}
end Coef
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
end Move
section Read
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {X : Type} (rd : M →ₛₗ[eK] (X → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end Read
end GlobalTheory.BaseCmp
namespace GlobalTheory.BigOn.Exp
open Formalism.MainNotions.DIV.Cons Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.BaseCmp
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
/- English proof (translation)
The claim follows from `have hc := RealDat3.characterisation_of_weak p.charW hr.exAt ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩`.
-/
theorem core_of_rows_alt (hr : p.PointConditions') : GlobalTheory.Hk3.Core p.R.toRealDat p.F.lv2 :=
  have hc := RealDat3.characterisation_of_weak p.charW hr.exAt
  ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
/- English proof (translation)
Establish `hC` using `_root_.GlobalTheory.BigOn.Exp.core_of_rows_alt hr`. Establish `hp` using `hf.pin`. Use `set i := ex.nch.twI w with hi`. Use `set b := ex.nch.sd w with hb`. Establish `hB` using `hρ.base i j b`.

Establish `hBo` using `baseOf_of_realPin hρ hp i j b`. Establish `hl : D.ntw.l i = Formalism.EigenvalueLevelCeiling.plc (D.plEq w)` using `(ex.nch.twI_l w).trans (GlobalTheory.Mem.Top.Bl.resChar_eq_plc D w)`. Establish `hpD : ∀ P, P ∈ D.ntw.pD i ↔ ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `fun P => by`. Rewrite using `[← Finset.mem_coe, D.ntw.pD_eq, hl]`. Both sides reduce to the same expression.

Establish `hQ : GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w)) = (ρ.B i j b).de.Q` using `Finset.ext fun P => by`. Rewrite using `[(placesAt hw hρ hp).1 P, GlobalTheory.OnTies.placesOver, Finset.mem_filter, hpD]`. Take `⟨χ, ξR, hK⟩` from `GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D _ _ _ _ _ p.R.toRealDat _ hC j _ hw p.charW.tup.mu_on ω φ hk`. Rewrite `hK` using `[hQ]`. Establish `hN : ownAt D (D.plEq w) ≠ 0`.

Unfold `ownAt`. Use `split_ifs`. Use `exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]`. Take `⟨k, hkf, c, m, hc, H⟩` from `exists_trace_eq hC p.qGuard (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)) hB hBo hK (hl ▸ hp.delta i j b) ⟨_, fun P h => (((placesAt hw hρ hp).1 P).1 h).1⟩ hN (fun P h => (hpD P).1 (((placesAt hw hρ hp).1 P).1 h).2) p.P.P0 p.P.ψ0⁻¹ ((p.R.eG.trans p.cG).trans (ρ. …`. Establish `e` using `hp.grp i j b (p.cG (p.R.eG g)) P h h' a c`.

Rewrite `e` using `[MulEquiv.symm_apply_apply]`. Conclude with `e)`. Use the proof step `(mem_level_iff hm hf.level i j b)`. Use the proof step `(fun u hu => by`. Use `(level_chi hm hρ hf.level i j b u hu).1.trans ?_` and prove the remaining obligations.

Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀])`. Use the proof step `(hρ.weil_base i j b)`. Take `⟨h, hh, y, hy, hx⟩` from `hx`. Take `⟨hy', hs⟩` from `H h y hy`. Take `⟨hν, c₀, ⟨gramR, c0R, c0L, hT, u, hu, hsc⟩, n₀, hn₀, hpow⟩` from `hf.norm`.

Rewrite `hpow` using `[p.phsOne, map_one, one_mul]`. Establish `hc₀ : c₀ ≠ 0` using `fun h0 => hν (pow_eq_zero_iff hn₀ |>.1 (by rw [hpow, h0, zero_pow hn₀]))`. Take `⟨cc, hcc, hbij, -⟩` from `GlobalTheory.CoefExtC.exists_extC_bijective_unique D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ hC ⟨p.fw⟩ j _ _ (p.O j) (p.pins j).2`. Take `⟨-, -, hval, -⟩` from `GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ p.O hC ⟨p.fw⟩ hr.ioExt j (p.pins j) cc hcc u hu _ hB hBo`. Establish `hmem` using `mem_span_coefLat hC hBo ⟨gramR, c0R, hT⟩ (p.R.ioP j (PiTensorProduct.tprod ℂ u)) (fun z => by obtain ⟨z, rfl⟩ := hbij.2 z; exact hval z) hc₀ hsc (ρ.eO i b).range O' hO' hy'`.

Take `⟨s, h', T, ζ, hζ, hT1, hT2⟩` from `exists_move hρ i j b (mul_mem hh hkf)`. Take `⟨-, n, hc1, -⟩` from `hc`. Establish `hN' : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hN`. Use `⟨s, h', T (c₀⁻¹ • p.R.ioP j (PiTensorProduct.tprod ℂ u) ((((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m) • y)), (c₀ / ν) * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹, n + m, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IsIntegral ℤ (c₀ / ν)` using `isIntegral_of_root ⟨n₀, hn₀, by rw [div_pow, hpow, div_self (pow_ne_zero _ hc₀)]⟩`.

Rewrite using `[show ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (n + m) * (c₀ / ν * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) = c₀ / ν * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * c) * ζ by rw [pow_add]; field_simp]`. Conclude with `(h1.mul hc1).mul (isIntegral_of_root hζ)`. Establish `h1` using `Submodule.mem_map_of_mem (f := T.restrictScalars O') hmem`. Rewrite `h1` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ h1` and prove the remaining obligations.

Introduce and unpack `_ ⟨Q, hQ, rfl⟩`. Conclude with `hT2 Q hQ`. Establish `e : p.v₀ j (sg0 D p.P.A3.A) = fun τ => (u τ : (p.R.MW j (sg0 D p.P.A3.A)).sm τ)` using `funext fun τ => (hu τ).symm`. Rewrite using `[e, hx u, one_smul, hs u]`. Express the relevant statement in the definitionally equal form `ν⁻¹ • c • ρ.theta i j b _ _ = _`.

Rewrite using `[hT1, map_smul, map_smul, map_smul]`. Simplify using `only [Setup.theta, map_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_series_alt (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) (O' : Subring ℂ) (hO' : ∀ a : 𝓞 D.what₂.LL, D.what₂.embLL a ∈ O') {ω φ}
    (hk : IsKernel p.R.toRealDat j (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w)))
      (GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w))) ω φ) {x}
    (hx : x ∈ seriesSet p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 ω φ) :
    ∃ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) (ζ : ℂ) (n : ℕ),
      IsIntegral ℤ (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * ζ) ∧
      P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q} ∧
      ν⁻¹ • adForm p.R.toRealDat j x (p.v₀ j _) = ζ • ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
  classical
  have hC := _root_.GlobalTheory.BigOn.Exp.core_of_rows_alt hr
  have hp := hf.pin
  set i := ex.nch.twI w with hi
  set b := ex.nch.sd w with hb
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hρ hp i j b
  have hl : D.ntw.l i = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := (ex.nch.twI_l w).trans (GlobalTheory.Mem.Top.Bl.resChar_eq_plc D w)
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq, hl]
    rfl
  have hQ : GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w)) = (ρ.B i j b).de.Q :=
    Finset.ext fun P => by
      rw [(placesAt hw hρ hp).1 P, GlobalTheory.OnTies.placesOver, Finset.mem_filter, hpD]
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D _ _ _ _ _ p.R.toRealDat _ hC j _ hw p.charW.tup.mu_on ω φ hk
  rw [hQ] at hK
  have hN : ownAt D (D.plEq w) ≠ 0 := by
    unfold ownAt
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  obtain ⟨k, hkf, c, m, hc, H⟩ := exists_trace_eq hC p.qGuard (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)) hB hBo hK
    (hl ▸ hp.delta i j b) ⟨_, fun P h => (((placesAt hw hρ hp).1 P).1 h).1⟩ hN
    (fun P h => (hpD P).1 (((placesAt hw hρ hp).1 P).1 h).2) p.P.P0 p.P.ψ0⁻¹ ((p.R.eG.trans p.cG).trans (ρ.eG i j b))
    (fun g P h h' a c => by
      have e := hp.grp i j b (p.cG (p.R.eG g)) P h h' a c
      rw [MulEquiv.symm_apply_apply] at e
      exact e)
    (mem_level_iff hm hf.level i j b)
    (fun u hu => by
      refine (level_chi hm hρ hf.level i j b u hu).1.trans ?_
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀])
    (hρ.weil_base i j b)
  obtain ⟨h, hh, y, hy, hx⟩ := hx
  obtain ⟨hy', hs⟩ := H h y hy
  obtain ⟨hν, c₀, ⟨gramR, c0R, c0L, hT, u, hu, hsc⟩, n₀, hn₀, hpow⟩ := hf.norm
  rw [p.phsOne, map_one, one_mul] at hpow
  have hc₀ : c₀ ≠ 0 := fun h0 => hν (pow_eq_zero_iff hn₀ |>.1 (by rw [hpow, h0, zero_pow hn₀]))
  obtain ⟨cc, hcc, hbij, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ hC ⟨p.fw⟩ j _ _
    (p.O j) (p.pins j).2
  obtain ⟨-, -, hval, -⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ p.O hC ⟨p.fw⟩ hr.ioExt j
    (p.pins j) cc hcc u hu _ hB hBo
  have hmem := mem_span_coefLat hC hBo ⟨gramR, c0R, hT⟩ (p.R.ioP j (PiTensorProduct.tprod ℂ u))
    (fun z => by obtain ⟨z, rfl⟩ := hbij.2 z; exact hval z) hc₀ hsc (ρ.eO i b).range O' hO' hy'
  obtain ⟨s, h', T, ζ, hζ, hT1, hT2⟩ := exists_move hρ i j b (mul_mem hh hkf)
  obtain ⟨-, n, hc1, -⟩ := hc
  have hN' : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  refine ⟨s, h', T (c₀⁻¹ • p.R.ioP j (PiTensorProduct.tprod ℂ u) ((((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m) • y)),
    (c₀ / ν) * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹, n + m, ?_, ?_, ?_⟩
  · have h1 : IsIntegral ℤ (c₀ / ν) := isIntegral_of_root ⟨n₀, hn₀, by rw [div_pow, hpow, div_self (pow_ne_zero _ hc₀)]⟩
    rw [show ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (n + m) * (c₀ / ν * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
      c₀ / ν * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * c) * ζ by rw [pow_add]; field_simp]
    exact (h1.mul hc1).mul (isIntegral_of_root hζ)
  · have h1 := Submodule.mem_map_of_mem (f := T.restrictScalars O') hmem
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨Q, hQ, rfl⟩
    exact hT2 Q hQ
  · have e : p.v₀ j (sg0 D p.P.A3.A) = fun τ => (u τ : (p.R.MW j (sg0 D p.P.A3.A)).sm τ) := funext fun τ => (hu τ).symm
    rw [e, hx u, one_smul, hs u]
    change ν⁻¹ • c • ρ.theta i j b _ _ = _
    rw [hT1, map_smul, map_smul, map_smul]
    simp only [Setup.theta, map_smul, smul_smul]
    congr 1
    field_simp
/- English proof (translation)
Take `⟨-, e, he1, he2⟩` from `hf.adapted`. Take `⟨Z⟩` from `hm.series`. Establish `hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm` using `GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)`. Establish `hF : Faithful (rdAt p w j hρ ν)` using `realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hf.norm.1 hr.prim.unif p.charW.base.models.HW (Z.vec j) hK`. Establish `hL : ∀ c : D.ntw.O (ex.nch.twI w), e (algebraMap _ (FractionRing (ex.nch.Oe w)) c) = ρ.e (ex.nch.twI w) (ex.nch.sd w) (algebraMap _ (FractionRing _) c)` using `fun c => by`.

Rewrite using `[IsScalarTower.algebraMap_apply _ (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)), IsScalarTower.algebraMap_apply _ (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w), he2, hρ.ek_e]`. Both sides reduce to the same expression. Use `set Ψ := readExt (rdAt p w j hρ ν) e hL with hΨ`. Establish `hint : ∀ a : 𝓞 D.what₂.LL, ∃ o : ex.nch.Oe w, algebraMap _ (FractionRing (ex.nch.Oe w)) o = ex.nch.embW w a` using `fun a => exists_of_integral e (N := 1) (n := 0) (by simp) (by`. Rewrite using `[pow_zero, one_mul, he1]`.

Conclude with `map_isIntegral_int _ a.isIntegral_coe)`. Establish `hrd : ∀ y, Ψ (rd y) = ν⁻¹ • adForm p.R.toRealDat j y (p.v₀ j _)` using `fun y => by`. Take `⟨y, rfl⟩` from `(p.nexp.fi j).e.surjective y`. Express the relevant statement in the definitionally equal form `Ψ (rd ((p.nexp.fi j).e y)) = ν⁻¹ • evW p.nexp p.v₀ j y`. Take `⟨n, β, hβ, -, -, -, hs⟩` from `hK`.

Establish `hy : y ∈ Submodule.span D.what₂.LL (Set.range β)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Use `(congrArg Ψ (hcan ⟨β a, hβ a⟩)).trans ?_` and prove the remaining obligations.

Rewrite using `[hΨ, readExt_tmul, map_one, one_smul]`. Use `(realRd_tmul p.nexp p.v₀ hρ _ j _ ν _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `mul_right_eq_self₀.2 (Or.inl (map_one (ρ.e _ _)))`. Consider the case `zero => rw [map_zero, map_zero, smul_zero]`.

Conclude with `(congrArg Ψ rd.map_zero).trans Ψ.map_zero`. Consider the case `add u v _ _ hu hv => rw [map_add, map_add, smul_add, ← hu, ← hv, ← Ψ.map_add]`. Conclude with `congrArg Ψ (rd.map_add _ _)`. Consider the case `smul c u _ hu`. Rewrite using `[map_smul, evW_smul, smul_comm, ← hu, ← he1, hΨ, ← readExt_smul]`.

Conclude with `congrArg _ (rd.map_smulₛₗ _ _)`. Set `O' : Subring ℂ` to `(e.comp (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)))).range`. Establish `hser : ∀ s h, ∀ P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q}, ∃ t ∈ baseLat p w j hρ ν, Ψ t = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P` using `fun s h P hP => by`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem Q hQ`.

Take `⟨f, e1⟩` from `hf.rat.1 s h Q hQ`. Use `⟨_, Submodule.subset_span ⟨f, ⟨s, h, Q, hQ, e1⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← e1, hΨ]`. Conclude with `(readExt_tmul _ e hL 1 f).trans (by rw [map_one, one_smul])`. Consider the case `zero => exact ⟨0, zero_mem _, Ψ.map_zero.trans (LinearMap.map_zero _).symm⟩`.

Consider the case `add _ _ _ _ h1 h2`. Take `⟨t, m1, e1⟩` from `h1`. Take `⟨t', m2, e2⟩` from `h2`. Conclude with `⟨t + t', add_mem m1 m2, by rw [Ψ.map_add, e1, e2]; exact (LinearMap.map_add _ _ _).symm⟩`. Consider the case `smul a Q _ h1`.

Take `⟨t, m1, e1⟩` from `h1`. Take `⟨_, o, rfl⟩` from `a`. Use `⟨o • t, Submodule.smul_mem _ o m1, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul (FractionRing (ex.nch.Oe w)) o t, hΨ, readExt_smul, ← hΨ, e1]`. Conclude with `(LinearMap.map_smul _ _ _).symm`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `x ∈ thetaBase p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) at hx`. Express the relevant statement in the definitionally equal form `rd x ∈ baseLat p w j hρ ν`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨ω, φ, hk, hx⟩` from `hx`. Take `⟨s, h, P, ζ, n, hζ, hP, e1⟩` from `_root_.GlobalTheory.BigOn.Exp.exists_series_alt hr hm hw hf O' (fun a => by obtain ⟨o, ho⟩ := hint a; exact ⟨o, by rw [RingHom.comp_apply, ho, he1]⟩) hk hx`. Take `⟨t, ht, e2⟩` from `hser s h P hP`. Break down `exists_scalar_of_readExt _ e hL hF (x := rd x) (t := t) (ζ := ζ) (((hrd x).trans e1).trans (congrArg _ e2.symm)) with h0 | ⟨a, ha, h0⟩` into its components or cases.

Conclude with `h0 ▸ zero_mem _`. Take `⟨o, rfl⟩` from `exists_of_integral e (isUnit_ownAt ex.nch w) (ha ▸ hζ)`. Rewrite using `[h0, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ o ht`. Consider the case `zero => exact rd.map_zero ▸ zero_mem _`.

Consider the case `add u v _ _ hu hv => exact rd.map_add u v ▸ add_mem hu hv`. Consider the case `smul a y _ hy`. Take `⟨o, ho⟩` from `hint a`. Establish `e1 : rd (a • y) = o • rd y`. Rewrite using `[← algebraMap_smul (FractionRing (ex.nch.Oe w)) o, ho]`.

Conclude with `rd.map_smulₛₗ (a : D.what₂.LL) y`. Conclude with `e1 ▸ Submodule.smul_mem _ o hy`.
-/
theorem realBase_le_baseLat_of_fit_can (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) {rd : Can p w j} (hcan : IsCan p rd) : realBase p rd ≤ baseLat p w j hρ ν := by
  obtain ⟨-, e, he1, he2⟩ := hf.adapted
  obtain ⟨Z⟩ := hm.series
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hf.norm.1 hr.prim.unif
    p.charW.base.models.HW (Z.vec j) hK
  have hL : ∀ c : D.ntw.O (ex.nch.twI w), e (algebraMap _ (FractionRing (ex.nch.Oe w)) c) =
      ρ.e (ex.nch.twI w) (ex.nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)),
      IsScalarTower.algebraMap_apply _ (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w), he2, hρ.ek_e]
    rfl
  set Ψ := readExt (rdAt p w j hρ ν) e hL with hΨ
  have hint : ∀ a : 𝓞 D.what₂.LL, ∃ o : ex.nch.Oe w, algebraMap _ (FractionRing (ex.nch.Oe w)) o = ex.nch.embW w a := fun a =>
    exists_of_integral e (N := 1) (n := 0) (by simp) (by
      rw [pow_zero, one_mul, he1]
      exact map_isIntegral_int _ a.isIntegral_coe)
  have hrd : ∀ y, Ψ (rd y) = ν⁻¹ • adForm p.R.toRealDat j y (p.v₀ j _) := fun y => by
    obtain ⟨y, rfl⟩ := (p.nexp.fi j).e.surjective y
    change Ψ (rd ((p.nexp.fi j).e y)) = ν⁻¹ • evW p.nexp p.v₀ j y
    obtain ⟨n, β, hβ, -, -, -, hs⟩ := hK
    have hy : y ∈ Submodule.span D.what₂.LL (Set.range β) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine (congrArg Ψ (hcan ⟨β a, hβ a⟩)).trans ?_
      rw [hΨ, readExt_tmul, map_one, one_smul]
      refine (realRd_tmul p.nexp p.v₀ hρ _ j _ ν _ _).trans ?_
      congr 1
      exact mul_right_eq_self₀.2 (Or.inl (map_one (ρ.e _ _)))
    | zero => rw [map_zero, map_zero, smul_zero]; exact (congrArg Ψ rd.map_zero).trans Ψ.map_zero
    | add u v _ _ hu hv => rw [map_add, map_add, smul_add, ← hu, ← hv, ← Ψ.map_add]; exact congrArg Ψ (rd.map_add _ _)
    | smul c u _ hu =>
      rw [map_smul, evW_smul, smul_comm, ← hu, ← he1, hΨ, ← readExt_smul]
      exact congrArg _ (rd.map_smulₛₗ _ _)
  let O' : Subring ℂ := (e.comp (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)))).range
  have hser : ∀ s h, ∀ P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q},
      ∃ t ∈ baseLat p w j hρ ν, Ψ t = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := fun s h P hP => by
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, e1⟩ := hf.rat.1 s h Q hQ
      refine ⟨_, Submodule.subset_span ⟨f, ⟨s, h, Q, hQ, e1⟩, rfl⟩, ?_⟩
      rw [← e1, hΨ]
      exact (readExt_tmul _ e hL 1 f).trans (by rw [map_one, one_smul])
    | zero => exact ⟨0, zero_mem _, Ψ.map_zero.trans (LinearMap.map_zero _).symm⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨t', m2, e2⟩ := h2
      exact ⟨t + t', add_mem m1 m2, by rw [Ψ.map_add, e1, e2]; exact (LinearMap.map_add _ _ _).symm⟩
    | smul a Q _ h1 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := a
      refine ⟨o • t, Submodule.smul_mem _ o m1, ?_⟩
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o t, hΨ, readExt_smul, ← hΨ, e1]
      exact (LinearMap.map_smul _ _ _).symm
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ thetaBase p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) at hx
  change rd x ∈ baseLat p w j hρ ν
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, φ, hk, hx⟩ := hx
    obtain ⟨s, h, P, ζ, n, hζ, hP, e1⟩ := _root_.GlobalTheory.BigOn.Exp.exists_series_alt hr hm hw hf O'
      (fun a => by obtain ⟨o, ho⟩ := hint a; exact ⟨o, by rw [RingHom.comp_apply, ho, he1]⟩) hk hx
    obtain ⟨t, ht, e2⟩ := hser s h P hP
    rcases exists_scalar_of_readExt _ e hL hF (x := rd x) (t := t) (ζ := ζ) (((hrd x).trans e1).trans (congrArg _ e2.symm)) with
      h0 | ⟨a, ha, h0⟩
    · exact h0 ▸ zero_mem _
    · obtain ⟨o, rfl⟩ := exists_of_integral e (isUnit_ownAt ex.nch w) (ha ▸ hζ)
      rw [h0, algebraMap_smul]
      exact Submodule.smul_mem _ o ht
  | zero => exact rd.map_zero ▸ zero_mem _
  | add u v _ _ hu hv => exact rd.map_add u v ▸ add_mem hu hv
  | smul a y _ hy =>
    obtain ⟨o, ho⟩ := hint a
    have e1 : rd (a • y) = o • rd y := by
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o, ho]
      exact rd.map_smulₛₗ (a : D.what₂.LL) y
    exact e1 ▸ Submodule.smul_mem _ o hy
/- English proof (translation)
Introduce `_ _ _` and use `_root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ _ hr hm _ hw _ _ _ _ _ hf hcan => _root_.GlobalTheory.BigOn.Exp.realBase_le_baseLat_of_fit_can hr hm.2.2 hw hf hcan`.
-/
theorem baseLe_of_cusp_decay_and_ray_class_field : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ :=
  fun _ _ _ => _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ _ hr hm _ hw _ _ _ _ _ hf hcan => _root_.GlobalTheory.BigOn.Exp.realBase_le_baseLat_of_fit_can hr hm.2.2 hw hf hcan
end GlobalTheory.BigOn.Exp
end
end
