import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGenerat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalPull

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Introduce `E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ`. Use `letI := H.starRing`. Take `⟨-, -, -, h4, h5⟩` from `GlobalTheory.firstFiveLaws`. Establish `aR` using `hR.1`. Establish `aV` using `hV.1`.

Establish `hI : (maximalIdeal R).map θ ≤ maximalIdeal V` using `Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha`. Take `⟨PP', cub, sym, adj, prim, m₁, hm₁⟩` from `sabPull CubePf.cubePull (spMap θ) t`. Set `t' : SAB H (Sp V)` to `⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi, OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩`. Set `m₀ : SABMap t' t (spMap θ)` to `m₁`. Establish `hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ)` using `hm₁`.

Set `W : (Sp R).Opens` to `PrimeSpectrum.basicOpen f`. Establish `hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R))` using `hψ`. Establish `hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W`. Rewrite using `[genericPoint_eq_bot_of_affine]`. Use `show f ∉ Ideal.comap θ ⊥`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_bot]`. Conclude with `hf`. Set `x : Sp (FractionRing V) ⟶ Sp R` to `jK V ≫ specOf θ`. Establish `hxW : Set.range x ⊆ (W : Set (Sp R))`. Introduce and unpack `_ ⟨z, rfl⟩`.

Establish `hz : (jK V).base z = genericPoint (Sp V)`. Rewrite using `[genericPoint_eq_bot_of_affine]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥`. Use `haveI := z.isPrime`.

Rewrite using `[Ideal.eq_bot_of_prime z.asIdeal]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))`. Use `show (specOf θ).base ((jK V).base z) ∈ W`. Rewrite using `[hz]`. Conclude with `hgen`.

Take `⟨hamp, hkt⟩` from `GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW`. Take `⟨PK, cubK, symK, adjK, primK, mK, hmK⟩` from `sabPull CubePf.cubePull x t`. Set `tK : SAB H (Sp (FractionRing V))` to `⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi, OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩`. Establish `hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x))`. Take `⟨wK, gK, -⟩` from `mK.lin`.

Rewrite using `[P.bundle, ← hmK]`. Conclude with `⟨wK, gK⟩`. Establish `hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB` using `pull_isLB P.U.LG.isLB _`. Establish `hp : IsProper tK.G.hom` using `GlobalTheory.ZH.isProper_hom_of_relAmple hamp`. Use `haveI := hp`.

Establish `hA : RelAmple tK.G tK.PP.L` using `GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp`. Establish `hK : KTriv tK.G tK.PP.L` using `GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt`. Use `t.semi.smooth` as an intermediate fact. Use `t.semi.geomConnected` as an intermediate fact. Establish `: ConnectedSpace (Sp R)` using `inferInstanceAs (ConnectedSpace (PrimeSpectrum R))`.

Establish `: ConnectedSpace t.G.left` using `GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)`. Establish `hgA` using `GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre`. Establish `dA : d = P.A.g` using `H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd) P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))`. Establish `hpbG` using `isGrpPullback_pullback t.G x`.

Establish `hdB : SmoothOfRelativeDimension P.A.g tK.G.hom` using `dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd`. Set `A' : PolAV (Sp (FractionRing V))` to `GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK`. Set `oA' : A'.OAct (𝓞 E)` to `⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩`. Establish `mR : IsMonHom (Iso.refl t'.G).hom` using `by show IsMonHom (𝟙 _); infer_instance`. Establish `hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))` using `((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl`.

Establish `hgK` using `(isGrpPullback_pullback t'.G (jK V)).comp hbc`. Take `⟨eA, meA, heA⟩` from `grpPullback_iso hgK hpbG`. Establish `wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))), wA.IsGen`. Rewrite using `[← heA]`. Conclude with `LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _) (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩`.

Establish `hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ)` using `Category.id_comp _`. Take `⟨wL, heL, gL, rL⟩` from `rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm`. Establish `hψn` using `GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW`. Establish `extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom = eA.hom ≫ (OAct.pullback x t.G t.act).act a`. Introduce `a`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hpbG.1.hom_ext` to reduce the goal to its premises. Establish `a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) = pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left` using `pullback.lift_fst _ _ _`. Establish `a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left` using `pullback.lift_fst _ _ _`. Establish `a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ (t.act.act a).left` using `pullback.lift_fst _ _ _`.

Establish `i₀ : (Iso.refl t'.G).hom.left = 𝟙 _` using `rfl`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA, i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]`. Conclude with `(Over.w _).trans (Over.w _).symm`. Take `⟨D', hD, U', hLG, hgenU, hPU⟩` from `h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL`. Establish `extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a`.

Introduce `a`. Rewrite using `[hgenU]`. Conclude with `extA₀ a`. Take `⟨mod', oD', xl, el, lin', w0'⟩` from `h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA`. Set `P' : PELUnif (maximalIdeal V) t'` to `{ D := D' mod := mod' oD := oD' A := A' oA := oA' U := U' bundle := hLG lin := lin' w0 := w0' H.w0 P.w0 }`.

Conclude with `⟨t', P', hD, ⟨m₀⟩, xl, el⟩`.
-/
theorem exists_pelUnif_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  intro E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have aV := hV.1
  have hI : (maximalIdeal R).map θ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap θ) t
  let t' : SAB H (Sp V) := ⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap θ) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ) := hm₁
  let W : (Sp R).Opens := PrimeSpectrum.basicOpen f
  have hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R)) := hψ
  have hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    show f ∉ Ideal.comap θ ⊥
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  let x : Sp (FractionRing V) ⟶ Sp R := jK V ≫ specOf θ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK V).base z = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
    show (specOf θ).base ((jK V).base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW
  obtain ⟨PK, cubK, symK, adjK, primK, mK, hmK⟩ := sabPull CubePf.cubePull x t
  let tK : SAB H (Sp (FractionRing V)) := ⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩
  have hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x)) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    rw [P.bundle, ← hmK]
    exact ⟨wK, gK⟩
  have hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB := pull_isLB P.U.LG.isLB _
  have hp : IsProper tK.G.hom := GlobalTheory.ZH.isProper_hom_of_relAmple hamp
  haveI := hp
  have hA : RelAmple tK.G tK.PP.L :=
    GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB
      (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp
  have hK : KTriv tK.G tK.PP.L := GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt

  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have dA : d = P.A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hpbG := isGrpPullback_pullback t.G x
  have hdB : SmoothOfRelativeDimension P.A.g tK.G.hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing V)) := GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK
  let oA' : A'.OAct (𝓞 E) := ⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  have hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ)) :=
    ((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback t'.G (jK V)).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))),
      wA.IsGen := by
    rw [← heA]
    exact LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩

  have hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm
  have hψn := GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW
  have extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom =
      eA.hom ≫ (OAct.pullback x t.G t.act).act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpbG.1.hom_ext
    · have a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) =
          pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) =
          pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
          pullback.fst t.G.hom x ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have i₀ : (Iso.refl t'.G).hom.left = 𝟙 _ := rfl
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA,
        i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen
    t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL
  have extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a := by
    intro a
    rw [hgenU]
    exact extA₀ a
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      mod := mod'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := hLG
      lin := lin'
      w0 := w0' H.w0 P.w0 }
  exact ⟨t', P', hD, ⟨m₀⟩, xl, el⟩

end GlobalTheory.LocalPull
