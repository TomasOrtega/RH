import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.MultLevelP

/- English proof (translation)
Unfold `MultT Mult`. Conclude with `Submodule.map_mono (Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)`.
-/
theorem multT_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    MultT θ M J χ ≤ MultT θ M J' χ' := by
  unfold MultT Mult
  exact Submodule.map_mono (Submodule.span_mono fun T hT =>
    ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}

/- English proof (translation)
Introduce and unpack `κ ⟨hκ, hp, hr⟩`. Establish `e : Formalism.L2.DIV.rTup β L (finE V κ) = 1` using `Subgroup.mem_bot.1 hr`. Use `⟨hκ, hp, ?_⟩` and prove the remaining obligations. Use `show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H`. Rewrite using `[e]`.

Conclude with `L.P.H.one_mem`.
-/
theorem levS_flag1_sub (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : levS V β (flag1L L) ⊆ levS V β L := by
  rintro κ ⟨hκ, hp, hr⟩
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  refine ⟨hκ, hp, ?_⟩
  show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H
  rw [e]
  exact L.P.H.one_mem

/- English proof (translation)
Take `⟨-, -, hr⟩` from `hκ`. Establish `e : Formalism.L2.DIV.rTup β L (finE V κ) = 1` using `Subgroup.mem_bot.1 hr`. Establish `h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H` using `e ▸ L.P.H.one_mem`. Establish `h` using `levFn_withP (β := β) (L := L) L.P (finE V κ)`. Express the relevant statement in the definitionally equal form `Formalism.L2.DIV.levFn β L (finE V κ) = _ at h`.

Establish `e1 : (⟨_, h1⟩ : L.P.H) = 1` using `Subtype.ext e`. Unfold `levChi`. Rewrite using `[levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]`.
-/
theorem levChi_flag1 (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {κ : GA D V} (hκ : κ ∈ levS V β (flag1L L)) :
    levChi V β (flag1L L) κ = levChi V β L κ := by
  obtain ⟨-, -, hr⟩ := hκ
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  have h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H := e ▸ L.P.H.one_mem
  have h := levFn_withP (β := β) (L := L) L.P (finE V κ)
  change Formalism.L2.DIV.levFn β L (finE V κ) = _ at h
  have e1 : (⟨_, h1⟩ : L.P.H) = 1 := Subtype.ext e
  unfold levChi
  rw [levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]

end GlobalTheory.MultLevelP

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm`. Establish `hθ` using `hB.models.inf`. Establish `hc` using `hB.models.cX`. Establish `hpr` using `hB.models.prX`. Establish `hp` using `GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX`.

Establish `hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b)))) (levChi _ R.βX (flag1L (datXP R t (R.levR F b))))` using `GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b))) (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm`. Establish `e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t)` using `rfl`. Establish `hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t)))`. Rewrite using `[← e]`. Conclude with `hT0`.

Establish `X` using `GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1`. Take `⟨Fn, hFn, hmap⟩` from `X`. Use `⟨Fn, hFn, ?_, hmap⟩` and prove the remaining obligations. Introduce and unpack `⟨q, hqQ⟩ hq h`. Take `⟨κ, hκκ⟩` from `GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q`.

Establish `hκ` using `hκκ.1`. Establish `hκq` using `hκκ.2`. Take `⟨g, hg⟩` from `(finHom D.sp.X').rangeRestrict_surjective h`. Substitute `hg` using the available equality. Establish `hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q` using `by rw [hκq]; exact hqQ`.

Establish `eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩` using `Subtype.ext hκq`. Establish `hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P` using `(congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq`. Establish `key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P) (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P), ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) = ((levEnv D.s …`. Introduce and unpack `x _ rfl hx hy`. Both sides reduce to the same expression.

Establish `hbr` using `GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ`. Establish `hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b))` using `hbr.1.2 ⟨hqQ', hq'⟩`. Establish `hχ` using `hbr.2 hqQ' hq'`. Establish `hM` using `(mem_multT _ _ _ _ _).1 hTm`. Establish `hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g'`.

Introduce `x g'`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r v`. Use `(GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'` as an intermediate fact. Rewrite using `[map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]`.

Conclude with `congrArg (r * ·) this`. Consider the case `add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]`. Establish `hb` using `(GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1`. Establish `hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g`. Use `hb (LinearMap.ext fun x => ?_)` and prove the remaining obligations.

Establish `a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ)` using `congrFun (LinearMap.congr_fun hmap x) (g * κ)`. Establish `a2 : R.prX (R.cX.ext Fn g) x = Tm x g` using `congrFun (LinearMap.congr_fun hmap x) g`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]`. Express the relevant statement in the definitionally equal form `R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext`. Rewrite `hext` using `[GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul]`.

Establish `inj : Function.Injective (R.cX.ρ g⁻¹)` using `fun a a' haa => by`. Use `congrArg (R.cX.ρ g) haa` as an intermediate fact. Rewrite `this` using `[GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.MultLevelP.exists_form_of_mult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm
  have hθ := hB.models.inf
  have hc := hB.models.cX
  have hpr := hB.models.prX
  have hp := GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX
  have hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b))))
      (levChi _ R.βX (flag1L (datXP R t (R.levR F b)))) :=
    GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b)))
      (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm
  have e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t) := rfl
  have hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t))) := by
    rw [← e]; exact hT0
  have X := GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1
  obtain ⟨Fn, hFn, hmap⟩ := X
  refine ⟨Fn, hFn, ?_, hmap⟩
  rintro ⟨q, hqQ⟩ hq h
  obtain ⟨κ, hκκ⟩ := GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q
  have hκ := hκκ.1
  have hκq := hκκ.2
  obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective h
  subst hg
  have hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by rw [hκq]; exact hqQ
  have eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩ := Subtype.ext hκq
  have hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P :=
    (congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq
  have key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P)
      (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P),
      ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ((levEnv D.sp.X' R.βX (R.datXt t)).ch y : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hy⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro x _ rfl hx hy
    rfl
  have hbr := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ
  have hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b)) := hbr.1.2 ⟨hqQ', hq'⟩
  have hχ := hbr.2 hqQ' hq'
  have hM := (mem_multT _ _ _ _ _).1 hTm
  have hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g' := by
    intro x g'
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  have hb := (GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1
  have hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g := by
    refine hb (LinearMap.ext fun x => ?_)
    have a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ) := congrFun (LinearMap.congr_fun hmap x) (g * κ)
    have a2 : R.prX (R.cX.ext Fn g) x = Tm x g := congrFun (LinearMap.congr_fun hmap x) g
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]
  change R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) =
    levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext
  rw [GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul] at hext
  have inj : Function.Injective (R.cX.ρ g⁻¹) := fun a a' haa => by
    have := congrArg (R.cX.ρ g) haa
    rwa [GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
  calc Fn ((finHom D.sp.X').rangeRestrict g * q) = Fn ((finHom D.sp.X').rangeRestrict g * (finHom D.sp.X').rangeRestrict κ) :=
      congrArg (fun x => Fn ((finHom D.sp.X').rangeRestrict g * x)) hκq.symm
    _ = levChi _ R.βX (datXP R t (R.levR F b)) κ • Fn ((finHom D.sp.X').rangeRestrict g) :=
      inj (hext.trans ((R.cX.ρ g⁻¹).map_smul _ _).symm)
    _ = _ := congrArg (fun c : ℂ => c • Fn ((finHom D.sp.X').rangeRestrict g)) (hχ.trans (key _ _ eQ hq' hq))

end
