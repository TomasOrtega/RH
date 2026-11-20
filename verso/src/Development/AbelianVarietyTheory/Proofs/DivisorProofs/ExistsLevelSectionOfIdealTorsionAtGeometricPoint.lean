import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section
open CartesianMonoidalCategory MonObj

namespace GlobalTheory.TorsSpec

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ I hI Ω _ _ x P hP hT`. Establish `cart` using `TF.Y.m.cart`. Establish `hpb` using `GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ`. Establish `hQw : (P ≫ GlobalTheory.EqvAct.pullψ TF Z φ) ≫ TF.Y.t.G.hom = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.jQ ≫ pullback.fst _ _)`. Rewrite using `[Category.assoc, hpb.1.w, ← Category.assoc, hP, Category.assoc, reassoc_of% hℓ, Category.assoc, j₀_ι]`.

Both sides reduce to the same expression. Set `Q` to `cart.1.lift _ _ hQw`. Establish `hQφ : Q ≫ TF.Y.m.φ = P ≫ GlobalTheory.EqvAct.pullψ TF Z φ` using `cart.1.lift_fst _ _ hQw`. Establish `hQh : Q ≫ TF.Y.oF.t.G.hom = x ≫ i₀ TF.Y Z` using `cart.1.lift_snd _ _ hQw`. Set `Q' : Over.mk (x ≫ i₀ TF.Y Z) ⟶ TF.Y.oF.t.G` to `Over.homMk Q hQh`.

Establish `htu : ∀ {S : Scheme.{0}} (T : Over S), (toUnit T).left = T.hom` using `fun T => (Category.comp_id _).symm.trans (Over.w (toUnit T))`. Establish `hcartη` using `eta_comp_of_isGrpPullback cart`. Establish `hpbη` using `eta_comp_of_isGrpPullback hpb`. Establish `htors : ∀ a ∈ I, Q' ≫ TF.Y.oF.t.act.act a = 1`. Introduce `a ha`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Hom.one_def, Over.comp_left, Over.comp_left, htu]`. Use `show Q ≫ _ = (x ≫ i₀ TF.Y Z) ≫ _`. Apply `cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, TF.Y.m.act, reassoc_of% hQφ, ← GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% (hT a ha), hpbη, Category.assoc, Category.assoc, hcartη, reassoc_of% hP]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hℓ, reassoc_of% j₀_ι]`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, Over.w, hQh, Category.assoc, Over.w]`. Conclude with `(Category.comp_id _).symm`.

Set `s0 : Xo.XF c ⟶ Sp (KA l)` to `pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s`. Set `β : KA l →+* Ω` to `(Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ s0)).hom`. Establish `hβ : (x ≫ i₀ TF.Y Z) ≫ s0 = spMap β` using `((congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage _)).symm`. Establish `hg` using `TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z) β hβ`. Take `⟨TI, -, -, hη⟩` from `hg.2`.

Establish `hMI : ((l.M : ℕ) : 𝓞 E) ∈ I`. Apply `hI` to reduce the goal to its premises. Establish `h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`.

Conclude with `Ideal.mul_le_left h1`. Establish `hM0 : 0 < l.M` using `by have := l.three_le; omega`. Establish `hpow : Q' ^ l.M = 1`. Rewrite using `[← GlobalTheory.GrpTangent.comp_mulN, ← act_natCast (E := E) TF.Y.oF.t.act, htors _ hMI]`. Take `⟨a, ha⟩` from `(TI.onto l.M hM0 Q').1 hpow`.

Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))`. Establish `hev : Q' = TI.ev l.M (v • a)`. Establish `e1 : TI.ev l.M (u • a) = 1`. Rewrite using `[TI.lin, ha]`. Conclude with `htors u (hI hu)`.

Establish `e2` using `TI.add l.M (u • a) (v • a)`. Rewrite `e2` using `[← add_smul, huv, one_smul, ha, e1, _root_.one_mul]`. Conclude with `e2`. Establish `hvm : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La)` using `Submodule.smul_mem_smul hv Submodule.mem_top`. Establish `hQeta : Q = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta (v • a)).left`.

Use `congrArg (fun q => q.left) (hev.trans (hη _ hvm).symm)` as an intermediate fact. Simplify using `only [Q', Over.homMk_left, Over.comp_left, htu] at this`. Conclude with `this`. Use `⟨Submodule.Quotient.mk (v • a), hpb.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, etaSecL_ψ, ← hQφ, hQeta]`.

Simplify using `only [Category.assoc]`. Rewrite using `[hP, Category.assoc, etaSecL_w]`.
-/
theorem exists_etaSecL_of_torsI : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (I : Ideal (𝓞 E)) (hI : l.Mb ≤ I) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (P : Sp Ω ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left)
    (hP : P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = x ≫ ℓ)
    (hT : ∀ a ∈ I, P ≫ ((GlobalTheory.EqvAct.pullAct TF Z φ).act a).left =
      P ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ GlobalTheory.EqvAct.pullG TF Z φ).left), ∃ c, P = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c := by
  intro E _ _ _ H Dw l Xo c TF Z X' φ ℓ hℓ I hI Ω _ _ x P hP hT
  have cart := TF.Y.m.cart
  have hpb := GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z φ
  have hQw : (P ≫ GlobalTheory.EqvAct.pullψ TF Z φ) ≫ TF.Y.t.G.hom = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.jQ ≫ pullback.fst _ _) := by
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hP, Category.assoc, reassoc_of% hℓ, Category.assoc, j₀_ι]
    rfl
  let Q := cart.1.lift _ _ hQw
  have hQφ : Q ≫ TF.Y.m.φ = P ≫ GlobalTheory.EqvAct.pullψ TF Z φ := cart.1.lift_fst _ _ hQw
  have hQh : Q ≫ TF.Y.oF.t.G.hom = x ≫ i₀ TF.Y Z := cart.1.lift_snd _ _ hQw
  let Q' : Over.mk (x ≫ i₀ TF.Y Z) ⟶ TF.Y.oF.t.G := Over.homMk Q hQh
  have htu : ∀ {S : Scheme.{0}} (T : Over S), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have hcartη := eta_comp_of_isGrpPullback cart
  have hpbη := eta_comp_of_isGrpPullback hpb
  have htors : ∀ a ∈ I, Q' ≫ TF.Y.oF.t.act.act a = 1 := by
    intro a ha
    apply Over.OverMorphism.ext
    rw [Hom.one_def, Over.comp_left, Over.comp_left, htu]
    show Q ≫ _ = (x ≫ i₀ TF.Y Z) ≫ _
    apply cart.1.hom_ext
    · rw [Category.assoc, TF.Y.m.act, reassoc_of% hQφ, ← GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% (hT a ha),
        hpbη, Category.assoc, Category.assoc, hcartη, reassoc_of% hP]
      simp only [Category.assoc]
      rw [reassoc_of% hℓ, reassoc_of% j₀_ι]
      rfl
    · rw [Category.assoc, Over.w, hQh, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  let s0 : Xo.XF c ⟶ Sp (KA l) := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
  let β : KA l →+* Ω := (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ s0)).hom
  have hβ : (x ≫ i₀ TF.Y Z) ≫ s0 = spMap β :=
    ((congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage _)).symm
  have hg := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z) β hβ
  obtain ⟨TI, -, -, hη⟩ := hg.2
  have hMI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    apply hI
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hpow : Q' ^ l.M = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN, ← act_natCast (E := E) TF.Y.oF.t.act, htors _ hMI]
  obtain ⟨a, ha⟩ := (TI.onto l.M hM0 Q').1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hev : Q' = TI.ev l.M (v • a) := by
    have e1 : TI.ev l.M (u • a) = 1 := by
      rw [TI.lin, ha]
      exact htors u (hI hu)
    have e2 := TI.add l.M (u • a) (v • a)
    rw [← add_smul, huv, one_smul, ha, e1, _root_.one_mul] at e2
    exact e2
  have hvm : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hQeta : Q = (x ≫ i₀ TF.Y Z) ≫ (TF.Y.oF.eta (v • a)).left := by
    have := congrArg (fun q => q.left) (hev.trans (hη _ hvm).symm)
    simp only [Q', Over.homMk_left, Over.comp_left, htu] at this
    exact this
  refine ⟨Submodule.Quotient.mk (v • a), hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, etaSecL_ψ, ← hQφ, hQeta]
    simp only [Category.assoc]
  · rw [hP, Category.assoc, etaSecL_w]

end GlobalTheory.TorsSpec
