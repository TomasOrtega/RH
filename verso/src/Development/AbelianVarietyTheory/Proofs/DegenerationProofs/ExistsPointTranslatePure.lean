import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusTranslate

/- English proof (translation)
Substitute `e` using the available equality. Establish `: f.app U ≫ Y.presheaf.map (homOfLE h).op ≫ m.appLE W ⊤ hm = (m ≫ f).appLE U ⊤ hg`. Rewrite using `[Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]`. Conclude with `congrArg (fun φ => φ.hom u.val) this`.
-/
theorem appLE_res_pullU {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h (pullU f U u)).val = (g.appLE U ⊤ hg).hom u.val := by
  subst e
  have : f.app U ≫ Y.presheaf.map (homOfLE h).op ≫ m.appLE W ⊤ hm = (m ≫ f).appLE U ⊤ hg := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  exact congrArg (fun φ => φ.hom u.val) this

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.
-/
theorem appLE_app {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (hm : ⊤ ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)) :
    (m.appLE (f ⁻¹ᵁ U) ⊤ hm).hom ((f.app U).hom u) = (g.appLE U ⊤ hg).hom u := by
  subst e
  rw [Scheme.Hom.comp_appLE]
  rfl

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom u.val) (Scheme.Hom.map_appLE m hm (homOfLE h).op)`.
-/
theorem appLE_res {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U W : Y.Opens) (h : W ≤ U)
    (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ m ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h u).val = (m.appLE U ⊤ hg).hom u.val :=
  congrArg (fun φ => φ.hom u.val) (Scheme.Hom.map_appLE m hm (homOfLE h).op)

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}

/- English proof (translation)
Rewrite using `[Category.assoc, D.isKernel.w, ← Category.assoc, Hom.one_def]`. Use `congr 1`. Conclude with `toUnit_unique _ _`.
-/
theorem torus_comp_q (τ : Z ⟶ splitTorus S E.X) : (τ ≫ D.i) ≫ D.q = 1 := by
  rw [Category.assoc, D.isKernel.w, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

/- English proof (translation)
Use `D.q_hom` as an intermediate fact. Rewrite using `[← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, torus_comp_q, _root_.one_mul]`.
-/
theorem translate_comp_q (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) :
    ((τ ≫ D.i) * x).left ≫ D.q.left = x.left ≫ D.q.left := by
  have := D.q_hom
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, torus_comp_q, _root_.one_mul]

/- English proof (translation)
Rewrite `h`, the goal using `[← Scheme.Hom.comp_preimage]`. Rewrite using `[translate_comp_q]` and apply the resulting hypothesis.
-/
theorem translate_le (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (V : E.B.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage] at h ⊢
  rwa [translate_comp_q]

/- English proof (translation)
Set `m : Z ⟶ splitTorus S E.X ⊗ G` to `lift τ x`. Establish `e1 : m.left ≫ (fst (splitTorus S E.X) G).left = τ.left`. Rewrite using `[← Over.comp_left, lift_fst]`. Establish `e2 : m.left ≫ (snd (splitTorus S E.X) G).left = x.left`. Rewrite using `[← Over.comp_left, lift_snd]`.

Establish `e3 : m.left ≫ (lift (fst (splitTorus S E.X) G ≫ D.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left = ((τ ≫ D.i) * x).left`. Rewrite using `[← Over.comp_left, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]`. Establish `hm : ⊤ ≤ m.left ⁻¹ᵁ ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j))`. Rewrite using `[← Scheme.Hom.comp_preimage, e2]`. Conclude with `h`.

Establish `key` using `congrArg (m.left.appLE _ ⊤ hm).hom (congrArg Units.val (D.equiv j k))`. Simplify using `only [Units.val_mul, map_mul] at key`. Rewrite `key` using `[appLE_res_pullU _ _ _ e3 _ _ _ hm h']`. Rewrite using `[key]`. Use `congr 1`.

Use `(appLE_res_pullU _ _ _ e1 ⊤ _ _ hm le_top _).trans ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Conclude with `appLE_app _ _ _ e2 _ hm h _`.
-/
theorem translate_coord (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (k : Module.Free.ChooseBasisIndex ℤ E.X)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (D.u j k).val =
      τ.left.appTop.hom (charUnit S E.X (E.basis k)).val * (x.left.appLE _ ⊤ h).hom (D.u j k).val := by
  let m : Z ⟶ splitTorus S E.X ⊗ G := lift τ x
  have e1 : m.left ≫ (fst (splitTorus S E.X) G).left = τ.left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : m.left ≫ (snd (splitTorus S E.X) G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : m.left ≫ (lift (fst (splitTorus S E.X) G ≫ D.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left
      = ((τ ≫ D.i) * x).left := by
    rw [← Over.comp_left, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hm : ⊤ ≤ m.left ⁻¹ᵁ ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) := by
    rw [← Scheme.Hom.comp_preimage, e2]; exact h
  have key := congrArg (m.left.appLE _ ⊤ hm).hom (congrArg Units.val (D.equiv j k))
  simp only [Units.val_mul, map_mul] at key
  rw [appLE_res_pullU _ _ _ e3 _ _ _ hm h'] at key
  rw [key]
  congr 1
  · refine (appLE_res_pullU _ _ _ e1 ⊤ _ _ hm le_top _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  · exact appLE_app _ _ _ e2 _ hm h _

/- English proof (translation)
Establish `hsingle : (Equiv.ofBijective _ (D.coord j V hV hle)).symm s = AddMonoidAlgebra.single α (D.weight j V hV hle α s)`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `β`. Distinguish the cases in `hβ : β = α`. Substitute `hβ` using the available equality.

Simplify using `[SplitExt.GtDatum.weight]`. Use `hs β hβ` as an intermediate fact. Rewrite `this` using `[SplitExt.GtDatum.weight]`. Rewrite using `[this]`. Simplify using `[Ne.symm hβ]`.

Generalize the expression as in `D.weight j V hV hle α s = w at hsingle`. Rewrite `hsingle` using `[Equiv.symm_apply_eq, Equiv.ofBijective_apply, AddMonoidAlgebra.liftNCRingHom_single]`. Set `c : E.X →ₗ[ℤ] Additive Γ(G.left, D.q.left ⁻¹ᵁ V)ˣ` to `E.basis.constr ℤ (fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)))`. Establish `hs' : s = (D.q.left.app V).hom w * (Additive.toMul (c α)).val` using `hsingle`. Set `f₁ : E.X →+ Additive Γ(Z.left, ⊤)ˣ` to `(Units.map (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom`.

Set `f₂ : E.X →+ Additive Γ(Z.left, ⊤)ˣ` to `(Units.map (x.left.appLE _ ⊤ h).hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom`. Set `f₀ : E.X →+ Additive Γ(Z.left, ⊤)ˣ` to `MonoidHom.toAdditiveRight (splitTorusPointsEquiv S E.X Z τ)`. Establish `hf : f₁.toIntLinearMap = (f₀ + f₂).toIntLinearMap`. Use `E.basis.ext fun k => ?_` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Establish `hc : c (E.basis k) = Additive.ofMul (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k))` using `E.basis.constr_basis _ _ _`. Express the relevant statement in the definitionally equal form `(((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c (E.basis k))).val = (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))).val * (x.left.appLE _ ⊤ h).hom (Additive.toMul (c (E.basis k))).val`. Establish `g : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)` using `h.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hle))`. Rewrite using `[hc, toMul_ofMul, splitTorusPointsEquiv_val, appLE_res _ _ _ _ h' (translate_le D τ x _ g), appLE_res _ _ _ _ h g]`.

Conclude with `translate_coord D τ x j k g _`. Establish `hα : (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c α)).val = (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd α)).val * (x.left.appLE _ ⊤ h).hom (Additive.toMul (c α)).val` using `congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hf α)`. Establish `g : ⊤ ≤ (x.left ≫ D.q.left) ⁻¹ᵁ V` using `h`. Rewrite using `[hs', map_mul, map_mul, hα, splitTorusPointsEquiv_val, appLE_app _ _ _ (translate_comp_q D τ x) V h' g, appLE_app _ _ _ rfl V h g]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_pure (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (V : E.B.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ E.chart j) (α : E.X)
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (hs : ∀ β, β ≠ α → D.weight j V hV hle β s = 0)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom s =
      τ.left.appTop.hom (charUnit S E.X α).val * (x.left.appLE _ ⊤ h).hom s := by
  have hsingle : (Equiv.ofBijective _ (D.coord j V hV hle)).symm s =
      AddMonoidAlgebra.single α (D.weight j V hV hle α s) := by
    apply AddMonoidAlgebra.ext
    ext β
    by_cases hβ : β = α
    · subst hβ
      simp [SplitExt.GtDatum.weight]
    · have := hs β hβ
      rw [SplitExt.GtDatum.weight] at this
      rw [this]
      simp [Ne.symm hβ]
  generalize D.weight j V hV hle α s = w at hsingle
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, AddMonoidAlgebra.liftNCRingHom_single] at hsingle
  let c : E.X →ₗ[ℤ] Additive Γ(G.left, D.q.left ⁻¹ᵁ V)ˣ := E.basis.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)))
  have hs' : s = (D.q.left.app V).hom w * (Additive.toMul (c α)).val := hsingle
  let f₁ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₂ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (x.left.appLE _ ⊤ h).hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₀ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    MonoidHom.toAdditiveRight (splitTorusPointsEquiv S E.X Z τ)
  have hf : f₁.toIntLinearMap = (f₀ + f₂).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    apply Additive.toMul.injective
    apply Units.ext
    have hc : c (E.basis k) = Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)) := E.basis.constr_basis _ _ _
    change (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c (E.basis k))).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c (E.basis k))).val
    have g : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j) :=
      h.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hle))
    rw [hc, toMul_ofMul, splitTorusPointsEquiv_val,
      appLE_res _ _ _ _ h' (translate_le D τ x _ g), appLE_res _ _ _ _ h g]
    exact translate_coord D τ x j k g _
  have hα : (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c α)).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd α)).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c α)).val :=
    congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hf α)
  have g : ⊤ ≤ (x.left ≫ D.q.left) ⁻¹ᵁ V := h
  rw [hs', map_mul, map_mul, hα, splitTorusPointsEquiv_val,
    appLE_app _ _ _ (translate_comp_q D τ x) V h' g, appLE_app _ _ _ rfl V h g]
  ring

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

/- English proof (translation)
Introduce `k _ Φ t`. Use `Φ.D.i_hom` as an intermediate fact. Set `κ : kˣ →* Γ((Out.baseOver (Sp k)).left, ⊤)ˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom`. Set `e` to `splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k))`. Set `τ` to `e.symm (κ.comp t)`.

Establish `hτ : e τ = κ.comp t` using `e.apply_symm_apply _`. Use `⟨τ ≫ Φ.D.i, torus_comp_q Φ.D τ, fun n hn => ?_, fun d α φ hφ x l hx => ?_⟩` and prove the remaining obligations. Establish `: τ ^ n = 1`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_pow, map_one, hτ]`.

Use `MonoidHom.ext fun χ => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun hn χ` as an intermediate fact. Rewrite `this` using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, this, map_one, MonoidHom.one_apply]`. Rewrite using `[← MonObj.pow_comp, this, MonObj.one_comp]`.

Establish `hx'` using `translate_le Φ.D τ x (Φ.N₀.U l) hx`. Use `⟨hx', ?_⟩` and prove the remaining obligations. Establish `key` using `translate_pure Φ.D τ x (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l) (fun β hβ => by`. Assume the negation of the conclusion as `hne`. Conclude with `hβ (hφ ⟨l, hne⟩)) hx hx'`.

Rewrite `key` using `[← splitTorusPointsEquiv_val]`. Establish `hv : (splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k)) τ (Multiplicative.ofAdd α)).val = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd α) : k)`. Express the relevant statement in the definitionally equal form `(e τ _).val = _`. Rewrite using `[hτ]`. Both sides reduce to the same expression.

Rewrite `key` using `[hv]`. Establish `key2` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom key`. Use `Eq.trans ?_ (Eq.trans key2 (Eq.trans ((map_mul _ _ _)) ?_))` and prove the remaining obligations. Conclude with `dif_pos hx'`. Use `congr 1`.

Conclude with `Iso.inv_hom_id_apply _ _`. Use `symm`. Conclude with `dif_pos hx`.
-/
theorem exists_point_translate_pure : (∀ (k : Type) [Field k] (Φ : FibPre k) (t : Multiplicative Φ.E.X →* kˣ), ∃ a : Φ.Pt, a ≫ Φ.D.q = 1 ∧ (∀ n : ℕ, t ^ n = 1 → a ^ n = 1) ∧ ∀ (d : ℕ) (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → ∀ (x : Φ.Pt) (l : Φ.N₀.ι), ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l → ⊤ ≤ (a * x).left ⁻¹ᵁ (Φ.H d).U l ∧ valF (a * x).left ((Φ.H d).U l) (φ.f l) = (t (Multiplicative.ofAdd α) : k) * valF x.left ((Φ.H d).U l) (φ.f l)) := by
  intro k _ Φ t
  have := Φ.D.i_hom
  let κ : kˣ →* Γ((Out.baseOver (Sp k)).left, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom
  let e := splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k))
  let τ := e.symm (κ.comp t)
  have hτ : e τ = κ.comp t := e.apply_symm_apply _
  refine ⟨τ ≫ Φ.D.i, torus_comp_q Φ.D τ, fun n hn => ?_, fun d α φ hφ x l hx => ?_⟩
  · have : τ ^ n = 1 := by
      apply e.injective
      rw [map_pow, map_one, hτ]
      refine MonoidHom.ext fun χ => ?_
      have := DFunLike.congr_fun hn χ
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, this, map_one, MonoidHom.one_apply]
    rw [← MonObj.pow_comp, this, MonObj.one_comp]
  · have hx' := translate_le Φ.D τ x (Φ.N₀.U l) hx
    refine ⟨hx', ?_⟩
    have key := translate_pure Φ.D τ x (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
      (fun β hβ => by
        by_contra hne
        exact hβ (hφ ⟨l, hne⟩)) hx hx'
    rw [← splitTorusPointsEquiv_val] at key
    have hv : (splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k)) τ
        (Multiplicative.ofAdd α)).val =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd α) : k) := by
      change (e τ _).val = _
      rw [hτ]; rfl
    rw [hv] at key
    have key2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom key
    refine Eq.trans ?_ (Eq.trans key2 (Eq.trans ((map_mul _ _ _)) ?_))
    · exact dif_pos hx'
    · congr 1
      · exact Iso.inv_hom_id_apply _ _
      · symm
        exact dif_pos hx

end GlobalTheory.TorusTranslate
