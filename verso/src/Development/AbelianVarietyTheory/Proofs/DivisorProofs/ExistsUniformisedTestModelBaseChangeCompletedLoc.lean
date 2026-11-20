import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpenStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfPullbackChainThroughSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi p _ y ev hCen hev y₀ hAt`. Take `⟨V, _, _, _, ev₀, i, hVc, hev₀, hi, hiinj, -, huniq⟩` from `GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hcpl p y hCen.1`. Establish `hevi : ev = i.comp ev₀` using `huniq ev hev`. Establish `hinj : Function.Injective ((OO p).subtype.comp i)` using `Subtype.val_injective.comp hiinj`. Use `letI alg : Algebra (FractionRing V) (PadicAlgCl p) := (IsFractionRing.lift (K := FractionRing V) hinj).toAlgebra`.

Use `haveI := ArithBase.ded (o := o') (Ω := Ω)`. Use `haveI := M.lft`. Use `haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s`. Set `Wab : M.Z.Opens` to `⟨abLocus FinalForm.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian FinalForm.G FinalForm.semi⟩`. Set `W : (Sp R).Opens` to `(spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ Wab`.

Establish `hgenU : (spMap j ≫ M.Z.fromSpecStalk x) (spMap ev₀ (genericPoint (Sp V))) ∈ U₀`. Establish `hw` using `hCen.2 ⟨genericPoint (Sp (PadicAlgCl p)), rfl⟩`. Establish `e2 : (spMap ((OO p).subtype.comp i)).base (genericPoint (Sp (PadicAlgCl p))) = genericPoint (Sp V)`. Rewrite using `[genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Use `show Ideal.comap ((OO p).subtype.comp i) ⊥ = ⊥`. Conclude with `Ideal.comap_bot_of_injective _ hinj`. Establish `e3 : gPt p ≫ y = spMap ((OO p).subtype.comp i) ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x`. Rewrite using `[← hev, hevi]`. Simplify using `only [gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Rewrite `hw` using `[e3]`. Rewrite using `[← e2]`. Conclude with `hw`. Establish `hU₀ab : (U₀ : Set M.Z) ⊆ abLocus FinalForm.G` using `GlobalTheory.T.semiAbelianExtension_abelian_over_open_part o' Ω S ρ M U₀ EE FinalForm hAdm.1`. Establish `hgenW : spMap ev₀ (genericPoint (Sp V)) ∈ W` using `hU₀ab hgenU`.

Establish `hsemi : IsSemiAbelian G`. Take `⟨e, he, -⟩` from `grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G _)`. Use `haveI := he`. Conclude with `GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)`. Establish `hadm : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hVc⟩`.

Take `⟨D', A', hD, U', hU'⟩` from `GlobalTheory.T.uniformisation_baseChange_of_kernel_in_generating_open R hBase D A G hsemi U V hadm ev₀ hev₀ W hpsi hgenW ((Over.pullback (specOf ev₀)).obj G) (Iso.refl _) (show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩)`. Establish `hgenV : (jK V).base (genericPoint (Sp (FractionRing V))) = genericPoint (Sp V)`. Rewrite using `[genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥`.

Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))`. Establish `hrange : Set.range (jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x).base ⊆ Set.range U₀.ι.base`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hw : w = genericPoint (Sp (FractionRing V))` using `Subsingleton.elim _ _`.

Substitute `hw` using the available equality. Use `show (spMap j ≫ M.Z.fromSpecStalk x).base ((spMap ev₀).base ((jK V).base _)) ∈ U₀`. Rewrite using `[hgenV]`. Conclude with `hgenU`. Take `⟨m, hm⟩ : ∃ m : Sp (FractionRing V) ⟶ U₀.toScheme, m ≫ U₀.ι = jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x` from `⟨IsOpenImmersion.lift U₀.ι _ hrange, IsOpenImmersion.lift_fac _ _ _⟩`.

Take `⟨yK, hyK⟩ : ∃ yK : S.R →+* FractionRing V, spMap yK = m ≫ FinalForm.u₀` from `⟨(Spec.preimage (m ≫ FinalForm.u₀)).hom, Spec.map_preimage _⟩`. Establish `hval : ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : S.R →+* K), spMap f = q ≫ FinalForm.u₀ → ∀ a : S.R, M.val (q ≫ U₀.ι) (a : Ω) = f a` using `fun K _ q f hf a => GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra o' Ω M U₀ S.R FinalForm.u₀ hAdm.1.ne FinalForm.u₀_gen K q f hf a`. Establish `hlift : ∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) v) = (i v : PadicAlgCl p)` using `fun v => IsFractionRing.lift_algebraMap (K := FractionRing V) hinj v`. Establish `e1 : gPt p ≫ spMap (i.comp ev₀) = spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ jK V ≫ spMap ev₀`. Simplify using `only [gPt, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `v`. Conclude with `(hlift (ev₀ v)).symm`. Establish `hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ m) ≫ U₀.ι`. Rewrite using `[Category.assoc, hm, ← hev, hevi, ← Category.assoc, e1]`.

Simplify using `only [Category.assoc]`. Establish `hfac : (algebraMap (FractionRing V) (PadicAlgCl p)).comp yK = y₀`. Use extensionality with `a`. Rewrite using `[hAt a, hgy, hval (PadicAlgCl p) _ ((algebraMap (FractionRing V) (PadicAlgCl p)).comp yK)]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`.

Rewrite using `[← hyK]`. Establish `hid : IsMonHom (Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom` using `show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩`. Establish `hβ : (genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm) ≫ FinalForm.G.hom = A'.A.hom ≫ m ≫ U₀.ι`. Rewrite using `[hm]`. Simplify using `only [genMap, Category.assoc]`.

Rewrite using `[hgm.1.w, pullback.condition_assoc]`. Establish `h1 : pullback.fst ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ pullback.snd G.hom (specOf ev₀) = pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ jK V` using `pullback.condition`. Rewrite using `[reassoc_of% h1]`. Establish `h2 : U'.gen.inv.left ≫ pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) = A'.A.hom` using `Over.w U'.gen.inv`. Rewrite using `[reassoc_of% h2]`.

Take `⟨t, ht₁, ht₂⟩ : ∃ t : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ FinalForm.φ = genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm ∧ t ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ m` from `⟨FinalForm.cart.1.lift _ _ hβ, FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _⟩`. Establish `hcart : IsGrpPullback A'.A ρ.P.A (spMap yK) (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)` using `by haveI := U'.gen_hom haveI : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance`. Establish `c1 : IsGrpPullback A'.A ((Over.pullback (jK V)).obj ((Over.pullback (specOf ev₀)).obj G)) (𝟙 _) U'.gen.symm.hom.left` using `isGrpPullback_of_iso U'.gen.symm`. Establish `c` using `((c1.comp (isGrpPullback_pullback _ (jK V))).comp (isGrpPullback_pullback G (specOf ev₀))).comp hgm`. Establish `n : IsGrpPullback A'.A FinalForm.G (m ≫ U₀.ι) (t ≫ FinalForm.φ)`.

Use `c.congr ?_ ?_` and prove the remaining obligations. Rewrite using `[hm]`. Simplify using `[specOf, jK, spMap]`. Rewrite using `[ht₁]`. Simplify using `only [genMap, Category.assoc]`.

Both sides reduce to the same expression. Establish `c4` using `IsGrpPullback.cancel FinalForm.cart n ht₂`. Conclude with `(c4.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr hyK.symm rfl`. Establish `hlb : LBIso A'.L (ρ.P.L.pull (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀))`. Take `⟨wE, hwE⟩` from `U'.ext`.

Take `⟨wL, hwL, -⟩` from `hU'.lg`. Use `GlobalTheory.T.lineBundleIso_of_pullback_chain_through_section A'.L U'.LG.L U.LG.L FinalForm.L.L ρ.P.L U'.gen.hom.left U'.gen.inv.left (pullback.fst _ (jK V)) ((Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ev₀)) gm FinalForm.φ (pullback.fst …` and prove the remaining obligations. Rewrite using `[← Over.comp_left, Iso.inv_hom_id, Over.id_left]`. Rewrite using `[ht₁]`. Simplify using `only [genMap, Iso.refl_hom, Over.id_left, Category.assoc]`.

Use `erw [Category.id_comp]`. Use `⟨⟨V, hVc, ?_, yK, hfac, A', t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀, hcart, hlb, (Over.pullback (specOf ev₀)).obj G, IsSemiAbelian.pullback _ G hsemi, D', U'⟩, hD.xe.symm, ?_⟩` and prove the remaining obligations. Conclude with `fun x => GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff p V i hi hinj x`. Use `⟨ev₀, hev₀, hD, Iso.refl _, hid, hU', fun χ => hD.xe.apply_symm_apply χ, fun r => ?_, t, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hlift, hevi]`.

Both sides reduce to the same expression. Conclude with `ht₁.trans (by simp only [Iso.refl_hom, Over.id_left]; erw [Category.id_comp])`.
-/
theorem exists_uTest_isBC : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi p _ y ev hCen hev y₀ hAt
  obtain ⟨V, _, _, _, ev₀, i, hVc, hev₀, hi, hiinj, -, huniq⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hcpl p y hCen.1
  have hevi : ev = i.comp ev₀ := huniq ev hev
  have hinj : Function.Injective ((OO p).subtype.comp i) := Subtype.val_injective.comp hiinj
  letI alg : Algebra (FractionRing V) (PadicAlgCl p) := (IsFractionRing.lift (K := FractionRing V) hinj).toAlgebra
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  let Wab : M.Z.Opens := ⟨abLocus FinalForm.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian FinalForm.G FinalForm.semi⟩
  let W : (Sp R).Opens := (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ Wab
  have hgenU : (spMap j ≫ M.Z.fromSpecStalk x) (spMap ev₀ (genericPoint (Sp V))) ∈ U₀ := by
    have hw := hCen.2 ⟨genericPoint (Sp (PadicAlgCl p)), rfl⟩
    have e2 : (spMap ((OO p).subtype.comp i)).base (genericPoint (Sp (PadicAlgCl p))) = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap ((OO p).subtype.comp i) ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ hinj
    have e3 : gPt p ≫ y = spMap ((OO p).subtype.comp i) ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x := by
      rw [← hev, hevi]
      simp only [gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3] at hw
    rw [← e2]; exact hw
  have hU₀ab : (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := GlobalTheory.T.semiAbelianExtension_abelian_over_open_part o' Ω S ρ M U₀ EE FinalForm hAdm.1
  have hgenW : spMap ev₀ (genericPoint (Sp V)) ∈ W := hU₀ab hgenU
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  have hadm : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  obtain ⟨D', A', hD, U', hU'⟩ := GlobalTheory.T.uniformisation_baseChange_of_kernel_in_generating_open R hBase D A G hsemi U V hadm ev₀ hev₀ W hpsi hgenW
    ((Over.pullback (specOf ev₀)).obj G) (Iso.refl _) (show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩)
  have hgenV : (jK V).base (genericPoint (Sp (FractionRing V))) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hrange : Set.range (jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x).base ⊆ Set.range U₀.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w = genericPoint (Sp (FractionRing V)) := Subsingleton.elim _ _
    subst hw
    show (spMap j ≫ M.Z.fromSpecStalk x).base ((spMap ev₀).base ((jK V).base _)) ∈ U₀
    rw [hgenV]; exact hgenU
  obtain ⟨m, hm⟩ : ∃ m : Sp (FractionRing V) ⟶ U₀.toScheme,
      m ≫ U₀.ι = jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x :=
    ⟨IsOpenImmersion.lift U₀.ι _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨yK, hyK⟩ : ∃ yK : S.R →+* FractionRing V, spMap yK = m ≫ FinalForm.u₀ :=
    ⟨(Spec.preimage (m ≫ FinalForm.u₀)).hom, Spec.map_preimage _⟩
  have hval : ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : S.R →+* K), spMap f = q ≫ FinalForm.u₀ →
      ∀ a : S.R, M.val (q ≫ U₀.ι) (a : Ω) = f a :=
    fun K _ q f hf a => GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra o' Ω M U₀ S.R FinalForm.u₀ hAdm.1.ne FinalForm.u₀_gen K q f hf a
  have hlift : ∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) v) = (i v : PadicAlgCl p) :=
    fun v => IsFractionRing.lift_algebraMap (K := FractionRing V) hinj v
  have e1 : gPt p ≫ spMap (i.comp ev₀) = spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ jK V ≫ spMap ev₀ := by
    simp only [gPt, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hlift (ev₀ v)).symm
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ m) ≫ U₀.ι := by
    rw [Category.assoc, hm, ← hev, hevi, ← Category.assoc, e1]
    simp only [Category.assoc]
  have hfac : (algebraMap (FractionRing V) (PadicAlgCl p)).comp yK = y₀ := by
    ext a
    rw [hAt a, hgy, hval (PadicAlgCl p) _ ((algebraMap (FractionRing V) (PadicAlgCl p)).comp yK)]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [← hyK]
  have hid : IsMonHom (Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom := show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩
  have hβ : (genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm) ≫ FinalForm.G.hom = A'.A.hom ≫ m ≫ U₀.ι := by
    rw [hm]
    simp only [genMap, Category.assoc]
    rw [hgm.1.w, pullback.condition_assoc]
    have h1 : pullback.fst ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ pullback.snd G.hom (specOf ev₀) =
        pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ jK V :=
      pullback.condition
    rw [reassoc_of% h1]
    have h2 : U'.gen.inv.left ≫ pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) = A'.A.hom := Over.w U'.gen.inv
    rw [reassoc_of% h2]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀,
      t ≫ FinalForm.φ = genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm ∧ t ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ m :=
    ⟨FinalForm.cart.1.lift _ _ hβ, FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _⟩
  have hcart : IsGrpPullback A'.A ρ.P.A (spMap yK) (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
    haveI := U'.gen_hom
    haveI : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    have c1 : IsGrpPullback A'.A ((Over.pullback (jK V)).obj ((Over.pullback (specOf ev₀)).obj G)) (𝟙 _)
        U'.gen.symm.hom.left := isGrpPullback_of_iso U'.gen.symm
    have c := ((c1.comp (isGrpPullback_pullback _ (jK V))).comp (isGrpPullback_pullback G (specOf ev₀))).comp hgm
    have n : IsGrpPullback A'.A FinalForm.G (m ≫ U₀.ι) (t ≫ FinalForm.φ) := by
      refine c.congr ?_ ?_
      · rw [hm]; simp [specOf, jK, spMap]
      · rw [ht₁]; simp only [genMap, Category.assoc]; rfl
    have c4 := IsGrpPullback.cancel FinalForm.cart n ht₂
    exact (c4.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr hyK.symm rfl
  have hlb : LBIso A'.L (ρ.P.L.pull (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
    obtain ⟨wE, hwE⟩ := U'.ext
    obtain ⟨wL, hwL, -⟩ := hU'.lg
    refine GlobalTheory.T.lineBundleIso_of_pullback_chain_through_section A'.L U'.LG.L U.LG.L FinalForm.L.L ρ.P.L U'.gen.hom.left U'.gen.inv.left
      (pullback.fst _ (jK V)) ((Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ev₀)) gm
      FinalForm.φ (pullback.fst ρ.P.A.hom FinalForm.u₀) t A'.isLB U'.LG.isLB U.LG.isLB FinalForm.L.isLB ρ.P.isLB ?_ ⟨wE, hwE⟩ ⟨wL, hwL⟩ hLB
      ⟨FinalForm.w, FinalForm.w_gen⟩ ?_
    · rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    · rw [ht₁]; simp only [genMap, Iso.refl_hom, Over.id_left, Category.assoc]; erw [Category.id_comp]
  refine ⟨⟨V, hVc, ?_, yK, hfac, A', t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀, hcart, hlb, (Over.pullback (specOf ev₀)).obj G,
    IsSemiAbelian.pullback _ G hsemi, D', U'⟩, hD.xe.symm, ?_⟩
  · exact fun x => GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff p V i hi hinj x
  · refine ⟨ev₀, hev₀, hD, Iso.refl _, hid, hU', fun χ => hD.xe.apply_symm_apply χ, fun r => ?_, t, rfl, ?_⟩
    · rw [hlift, hevi]; rfl
    · exact ht₁.trans (by simp only [Iso.refl_hom, Over.id_left]; erw [Category.id_comp])

end GlobalTheory.Poinc.TestAtPt
