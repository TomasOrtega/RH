import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocycleFormEqConnectionFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CrysCmp

/- English proof (translation)
Take `⟨f, rfl⟩` from `H1.mk_surjective _ c`. Establish `hb` using `(GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2`. Establish `hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1`. Use `AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))` and prove the remaining obligations. Use function extensionality and compare the values at `T T' T'' φ ψ`.

Express the relevant statement in the definitionally equal form `mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0`. Rewrite using `[f.2 φ ψ]`. Normalize the expressions using the abelian group laws. Take `⟨q, hq⟩` from `hb (QuotientAddGroup.mk ⟨_, hfe⟩)`. Take `⟨k₀, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Establish `hq'` using `QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)`. Rewrite `hq'` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨g, hg⟩` from `hq'`. Establish `hk` using `AddMonoidHom.mem_ker.1 k₀.2`. Set `f₀ : Z1 (O (dp0 R) s)` to `⟨k₀.1.1, fun T T' T'' φ ψ ↦ by`.

Use `congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ` as an intermediate fact. Express the relevant statement in the definitionally equal form `mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this`. Express the relevant statement in the definitionally equal form `k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ`. Take the linear combination `(norm := abel1) -this⟩`. Use `⟨f₀, k₀, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[H1.mk_eq_mk]`. Use `⟨-g, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Use `congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ` as an intermediate fact. Express the relevant statement in the definitionally equal form `g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this`.

Express the relevant statement in the definitionally equal form `-g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ`. Rewrite using `[map_neg]`. Take the linear combination `(norm := abel1) -this`.
-/
theorem exists_compatibleFormsCocycle_deRhamClass {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : FirstDeRham s) :
    ∃ (f₀ : Z1 (O (dp0 R) s)) (k₀ : (KK (dp0 R) s).Z1), k₀.1.1 = f₀.1 ∧ H1.mk _ f₀ = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hb := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2
  have hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1 := by
    refine AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
    funext T T' T'' φ ψ
    change mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0
    rw [f.2 φ ψ]; abel
  obtain ⟨q, hq⟩ := hb (QuotientAddGroup.mk ⟨_, hfe⟩)
  obtain ⟨k₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hq' := QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hq'
  obtain ⟨g, hg⟩ := hq'
  have hk := AddMonoidHom.mem_ker.1 k₀.2
  let f₀ : Z1 (O (dp0 R) s) := ⟨k₀.1.1, fun T T' T'' φ ψ ↦ by
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ
    change mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this
    change k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ
    linear_combination (norm := abel1) -this⟩
  refine ⟨f₀, k₀, rfl, ?_⟩
  rw [H1.mk_eq_mk]
  refine ⟨-g, ?_⟩
  funext T T' φ
  have := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
  change g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this
  change -g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ
  rw [map_neg]
  linear_combination (norm := abel1) -this

section Theta

variable {D : Data} (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i)

def thAlg (U : AffOp D.X) : Sec D.s U.unop.1 →ₐ[D.R] (m.obj (Λ.L.obj U)).B :=
  { (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) with commutes' := fun r ↦ (Λ.e U).commutes r }

def theta (U : AffOp D.X) :
    Thick.triv (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop) ⟶ m.obj (Λ.L.obj U) :=
  Thick.trivHom (thAlg Λ m U) (Λ.pt U)

end Theta

/- English proof (translation)
Rewrite using `[sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]`.
-/
theorem key4 {G : Type} [AddCommGroup G] (A B C E : G) (h : A + B = C + E) : E - A = B - C := by
  rw [sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]

/- English proof (translation)
Introduce `D Λ m c`. Take `⟨f₀, k₀, hk, rfl⟩` from `exists_compatibleFormsCocycle_deRhamClass D.s c`. Set `k` to `(morMap m).z1 k₀`. Set `k'` to `((KK D.κ D.t).resMap Λ.L).p1 k.1`. Establish `hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1` using `(((KK D.κ D.t).resMap Λ.L).z1 k).2`.

Take `⟨w, hw, -⟩` from `((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).1 k'`. Establish `hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)` using `((((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).2.2 k' w hw).1.1 hk')`. Use `⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩` and prove the remaining obligations. Rewrite using `[comparison_mk, Hyp1.mk_eq_mk]`. Use `⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) = w.1 U V a - (cmpZZ D.s f₀).1.1 U V a`. Apply `(Λ.e V).injective` to reduce the goal to its premises. Establish `h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a))`. Use `(hw.1 U V a).symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `k₀.1.1 _ _ _ = _`.

Rewrite using `[hk]`. Both sides reduce to the same expression. Establish `h2` using `Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))`. Use `erw [AlgEquiv.apply_symm_apply] at h2`. Establish `sq` using `ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a)) (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop)) (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V) (by intro c; exact (Λ.nat a c).symm)`.

Rewrite using `[map_sub, map_sub, h1, cmpZZ_f]`. Use `erw [AlgEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `_ - Λ.e V (mp (OAff D.s) a _) = _`. Rewrite using `[h2]`. Conclude with `key4 _ _ _ _ sq`.

Express the relevant statement in the definitionally equal form `KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) = w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)`. Establish `hrel : rel D.R (Λ.L.obj U).δ = ⊥` using `(GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le`. Establish `inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R], (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y`. Introduce `x y h`. Rewrite `h` using `[Submodule.Quotient.eq]`.

Establish `h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ` using `h`. Rewrite `h'` using `[hrel, Ideal.mem_bot, map_sub, sub_eq_zero]`. Conclude with `(ExteriorAlgebra.ι_inj _ _ _).1 h'`. Establish `hk0` using `AddMonoidHom.mem_ker.1 k₀.2`. Establish `hcoc` using `congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)`.

Establish `hc` using `GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)`. Establish `e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) + kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U))`. Establish `: k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) - kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0` using `hcoc`. Rewrite `this` using `[hk]`. Conclude with `sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)`.

Rewrite `e1` using `[hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add]`. Establish `e2` using `hw.2 U`. Express the relevant statement in the definitionally equal form `km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2`. Rewrite `e2` using `[e1]`. Use `erw [divPowerCompatOneFormMap_mk] at e2`.

Establish `e3` using `inj _ _ e2`. Establish `e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) + KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U))`. Rewrite using `[← e3, map_add]`. Use `congr 1`. Conclude with `SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _`.

Conclude with `SemiHom.m1_D _ _`. Establish `semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1)` using `fun r b ↦ map_smul (Λ.e U).symm r b`. Establish `linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω` using `fun ω ↦ (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1))) (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)`. Establish `e5` using `congrArg semiInv.m1 e3'`. Rewrite `e5` using `[map_add, linv, linv]`.

Rewrite using `[e5, add_sub_cancel_left]`. Conclude with `(SemiHom.m1_D semiInv _).symm`. Use function extensionality and compare the values at `T T' φ`. Express the relevant statement in the definitionally equal form `k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)`. Rewrite using `[hk]`.
-/
theorem lift_rel1_pull1_cmp1 : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  intro D Λ m c
  obtain ⟨f₀, k₀, hk, rfl⟩ := exists_compatibleFormsCocycle_deRhamClass D.s c
  let k := (morMap m).z1 k₀
  let k' := ((KK D.κ D.t).resMap Λ.L).p1 k.1
  have hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1 := (((KK D.κ D.t).resMap Λ.L).z1 k).2
  obtain ⟨w, hw, -⟩ := ((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).1 k'
  have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).2.2 k' w hw).1.1 hk')
  refine ⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩

  · rw [comparison_mk, Hyp1.mk_eq_mk]
    refine ⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩
    · change (Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.1 U V a - (cmpZZ D.s f₀).1.1 U V a
      apply (Λ.e V).injective
      have h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a)) := by
        refine (hw.1 U V a).symm.trans ?_
        change k₀.1.1 _ _ _ = _
        rw [hk]; rfl
      have h2 := Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))
      erw [AlgEquiv.apply_symm_apply] at h2
      have sq := ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a))
          (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop))
            (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V)
          (by intro c; exact (Λ.nat a c).symm)
      rw [map_sub, map_sub, h1, cmpZZ_f]
      erw [AlgEquiv.apply_symm_apply]
      change _ - Λ.e V (mp (OAff D.s) a _) = _
      rw [h2]
      exact key4 _ _ _ _ sq
    · change KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)
      have hrel : rel D.R (Λ.L.obj U).δ = ⊥ :=
        (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le
      have inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R],
          (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y := by
        intro x y h
        rw [Submodule.Quotient.eq] at h
        have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
        rw [hrel, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
        exact (ExteriorAlgebra.ι_inj _ _ _).1 h'
      have hk0 := AddMonoidHom.mem_ker.1 k₀.2
      have hcoc := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)
      have hc := GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)
      have e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) +
          kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U)) := by
        have : k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) -
            kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0 := hcoc
        rw [hk] at this
        exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)
      rw [hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add] at e1
      have e2 := hw.2 U
      change km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2
      rw [e1] at e2
      erw [divPowerCompatOneFormMap_mk] at e2
      have e3 := inj _ _ e2
      have e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) +
          KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U)) := by
        rw [← e3, map_add]
        congr 1
        · exact SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _
        · exact SemiHom.m1_D _ _
      have semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
        fun r b ↦ map_smul (Λ.e U).symm r b
      have linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω := fun ω ↦
        (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1)))
          (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)
      have e5 := congrArg semiInv.m1 e3'
      rw [map_add, linv, linv] at e5
      rw [e5, add_sub_cancel_left]
      exact (SemiHom.m1_D semiInv _).symm
  · funext T T' φ
    change k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)
    rw [hk]

end GlobalTheory.PDForm.CrysCmp
