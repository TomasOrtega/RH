import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosuresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeProjOverModL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjFormulaVert

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hqP : IsProper q`. Take `⟨N, j, _, hj⟩` from `hY`. Use `isProper_str k N` as an intermediate fact. Conclude with `hj ▸ inferInstance`. Establish `: IsSeparated (π ≫ p)` using `hπ ▸ (inferInstance : IsSeparated q)`.

Establish `hsep : IsSeparated π` using `IsSeparated.of_comp π p`. Establish `: LocallyOfFiniteType (π ≫ p)` using `hπ ▸ (inferInstance : LocallyOfFiniteType q)`. Establish `hlft : LocallyOfFiniteType π` using `locallyOfFiniteType_of_comp π p`. Establish `: IsLocallyNoetherian X`. Take `⟨N, j, _, hj⟩` from `hX`.

Establish `: LocallyOfFiniteType p` using `hj ▸ inferInstance`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian p`. Take `⟨U₀, hU₀, hxU₀, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (genericPoint X))`. Establish `hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀` using `by show π (genericPoint Y) ∈ U₀`. Rewrite using `[hg]`.

Conclude with `hxU₀`. Take `⟨V₀, hV₀, hyV₀, hVle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀`. Use `haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩`. Use `haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩`. Use `letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra`.

Use `haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩`. Use `haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) := (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)`. Use `haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) := HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle`. Use `haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle`. Take `⟨a₁, ha₁, H₁⟩` from `GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))`.

Take `⟨a₂, ha₂, H₂⟩` from `GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))`. Establish `ha : a₁ * a₂ ≠ 0` using `mul_ne_zero ha₁ ha₂`. Establish `hUU₀ : X.basicOpen (a₁ * a₂) ≤ U₀` using `X.basicOpen_le _`. Establish `hUa : IsAffineOpen (X.basicOpen (a₁ * a₂))` using `hU₀.basicOpen _`. Establish `hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂)`.

Establish `hne : X.basicOpen (a₁ * a₂) ≠ ⊥` using `fun h => ha ((basicOpen_eq_bot_iff _).1 h)`. Take `⟨z, hz⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne`. Conclude with `((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂)).isOpen).2 ⟨z, trivial, hz⟩`. Use `set U : X.Opens := X.basicOpen (a₁ * a₂) with hU_def`. Use `set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂)) with hV_def`.

Establish `hVV₀ : V ≤ V₀` using `Y.basicOpen_le _`. Establish `hVe : V = V₀ ⊓ π ⁻¹ᵁ U` using `Scheme.basicOpen_appLE π V₀ U₀ hVle _`. Establish `hVU : V ≤ π ⁻¹ᵁ U` using `by rw [hVe]; exact inf_le_right`. Establish `hVa : IsAffineOpen V` using `hV₀.basicOpen _`. Establish `hyV : genericPoint Y ∈ V`.

Rewrite using `[hVe]`. Conclude with `⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩`. Use `letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra`. Use `letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra`. Use `letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra`.

Use `letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)`. Use `haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)`. Use `haveI hlA : IsLocalization.Away (a₁ * a₂) Γ(X, U) := hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl`. Use `haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂)) Γ(Y, V) := hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl`.

Establish `e2 : a₂ * a₁ = a₁ * a₂` using `mul_comm _ _`. Establish `hfin : Module.Finite Γ(X, U) Γ(Y, V)` using `H₁ a₂ Γ(X, U) Γ(Y, V) hlA hlB`. Establish `hfree : Module.Free Γ(X, U) Γ(Y, V)` using `H₂ a₁ Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)`. Establish `hpre : π ⁻¹ᵁ U = V` using `GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin`. Establish `key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U → (letI` using `(π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W) ∧ Module.Finite Γ(X, U) Γ(Y, W)) → (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by`.

Introduce and unpack `W hW rfl h`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `h`. Take `⟨h1, h2⟩` from `key V hVU hpre.symm ⟨hfree, hfin⟩`. Conclude with `⟨U, hUa, hxU, hpre ▸ hVa, h1, h2, GlobalTheory.GenFinEtField.finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩`.
-/
theorem exists_affine_finite_free (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (hX : IsProjOver p) (hY : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hδ : π.residueDegree (genericPoint Y) ≠ 0) :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := by
    obtain ⟨N, j, _, hj⟩ := hX
    have : LocallyOfFiniteType p := hj ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
  have hUU₀ : X.basicOpen (a₁ * a₂) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂) := by
    have hne : X.basicOpen (a₁ * a₂) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e2 : a₂ * a₁ = a₁ * a₂ := mul_comm _ _
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) := H₁ a₂ Γ(X, U) Γ(Y, V) hlA hlB
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ a₁ Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W) ∧ Module.Finite Γ(X, U) Γ(Y, W)) →
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  obtain ⟨h1, h2⟩ := key V hVU hpre.symm ⟨hfree, hfin⟩
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2,
    GlobalTheory.GenFinEtField.finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.ProjFormulaVert

namespace GlobalTheory.ProjFormulaVert

/- English proof (translation)
The claim follows from `Algebra.algebra_ext a b fun r => congrFun (congrArg DFunLike.coe (RingHom.ext_zmod (@algebraMap _ _ _ _ a) (@algebraMap _ _ _ _ b))) r`.
-/
theorem algebra_zmod_eq {l : ℕ} {R : Type} [CommRing R] (a b : Algebra (ZMod l) R) : a = b :=
  Algebra.algebra_ext a b fun r => congrFun (congrArg DFunLike.coe
    (RingHom.ext_zmod (@algebraMap _ _ _ _ a) (@algebraMap _ _ _ _ b))) r

/- English proof (translation)
Introduce `k _ X Y p q D E hX hY π hπ L h h' hh hh' y l _ ⟨instW⟩`. Take `⟨g, hgc, hgen, hgdeg⟩` from `GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y`. Establish `hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y`. Rewrite using `[hgdeg, cloι_genericPoint]`. Establish `hinj : Function.Injective g.appTop.hom`.

Use `GlobalTheory.appLE_injective_of_genericPoint_map g hgen (U := ⊤) (V := g ⁻¹ᵁ ⊤) ⟨genericPoint (clo y), trivial⟩ le_rfl` as an intermediate fact. Rewrite `this` using `[← Scheme.Hom.app_eq_appLE]`. Then use the resulting hypothesis. Use `haveI : Nonempty (⊤ : (clo y).Opens) := ⟨⟨genericPoint (clo y), trivial⟩⟩`. Use `haveI : CharP Γ(clo y, ⊤) l := charP_of_injective_algebraMap (algebraMap (ZMod l) Γ(clo y, ⊤)).injective l`. Use `haveI : CharP Γ(clo (π y), ⊤) l := ⟨fun n => by`.

Rewrite using `[← CharP.cast_eq_zero_iff Γ(clo y, ⊤) l n, ← map_natCast g.appTop.hom n, map_eq_zero_iff _ hinj]⟩`. Use `letI instZ : Algebra (ZMod l) Γ(clo (π y), ⊤) := ZMod.algebra _ l`. Establish `hWp : IsProjOver (strHom (ZMod l) (clo y))` using `GlobalTheory.FibreProj.isProjOver_closed_fibre k Y q E hY (clo y) (cloι y) l`. Establish `hZp : IsProjOver (strHom (ZMod l) (clo (π y)))` using `GlobalTheory.FibreProj.isProjOver_closed_fibre k X p D hX (clo (π y)) (cloι (π y)) l`. Establish `hgs : g ≫ strHom (ZMod l) (clo (π y)) = strHom (ZMod l) (clo y)` using `comp_strHom fun r => congrFun (congrArg DFunLike.coe (RingHom.ext_zmod (g.appTop.hom.comp (algebraMap (ZMod l) _)) (algebraMap (ZMod l) _))) r`.

Take `⟨⟨m, hm⟩, -, -, -, hcl, hgd⟩` from `GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q (isAmb_of_isArithVar hY)`. Take `⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩` from `GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)`. Take `⟨d, -, hd⟩` from `hm y`. Take `⟨d', -, hd'⟩` from `hm' (π y)`. Establish `hWd : topologicalKrullDim (clo y) = d` using `(hgd (clo y) d).1 ((hcl (clo y) (cloι y) _ d).1 (by rw [cloι_genericPoint]; exact hd))`.

Establish `hZd : topologicalKrullDim (clo (π y)) = d'` using `(hgd' (clo (π y)) d').1 ((hcl' (clo (π y)) (cloι (π y)) _ d').1 (by rw [cloι_genericPoint]; exact hd'))`. Take `⟨hle, hiff⟩` from `GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q (isAmb_of_isArithVar hX) (isAmb_of_isArithVar hY) π hπ y d d' hd hd'`. Establish `e1` using `hh'.vertical (clo y) (cloι y) (ZMod l) d hWd`. Establish `e2` using `hh.vertical (clo (π y)) (cloι (π y)) (ZMod l) d' hZd`. Rewrite `e1`, `e2` using `[cloι_genericPoint]`.

Establish `ej : (cloι y ≫ π) ≫ p = cloι y ≫ q` using `by rw [Category.assoc, hπ]`. Establish `ei : (g ≫ cloι (π y)) ≫ p = g ≫ cloι (π y) ≫ p` using `Category.assoc _ _ _`. Establish `t1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull (cloι y)) d = topSelfIntersection (ZMod l) (L.B.pull (cloι y ≫ π)) d` using `topSelf_congr (ZMod l) ((L.pull π hπ).pull (cloι y) rfl).isLB (L.pull (cloι y ≫ π) ej).isLB (L.refines_pull_pull π hπ (cloι y) rfl ej).lbIso d`. Establish `t2 : topSelfIntersection (ZMod l) (L.B.pull (g ≫ cloι (π y))) d = topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d` using `topSelf_congr (ZMod l) (L.pull (g ≫ cloι (π y)) ei).isLB ((L.pull (cloι (π y)) rfl).pull g rfl).isLB (L.refines_pull_comp (cloι (π y)) rfl g rfl ei).lbIso d`. Rewrite `e1` using `[t1, ← hgc, t2]`.

Rewrite using `[e1, e2]`. It suffices to establish `key : topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d = (π.residueDegree y : ℤ) * topSelfIntersection (ZMod l) (L.B.pull (cloι (π y))) d' by`. Rewrite using `[key]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hB : (L.B.pull (cloι (π y))).IsLB` using `(L.pull (cloι (π y)) rfl).isLB`. Establish `hBg : ((L.B.pull (cloι (π y))).pull g).IsLB` using `((L.pull (cloι (π y)) rfl).pull g rfl).isLB`. Establish `hclo : topologicalKrullDim (closure ({g (genericPoint (clo y))} : Set (clo (π y)))) = d'`. Rewrite using `[hgen, (genericPoint_spec (clo (π y))).def]`. Conclude with `(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.trans hZd`.

Distinguish the cases in `h0 : π.residueDegree y = 0`. Establish `hne : d ≠ d'` using `fun e => (hiff.2 e) h0`. Establish `hlt : d' < d` using `lt_of_le_of_ne hle (Ne.symm hne)`. Establish `hz` using `GlobalTheory.PullVanish.interNum_pull_eq_zero (ZMod l) 0 d (clo y) (clo (π y)) hWp (by rw [Nat.zero_add, hWd]) g (by rw [hclo]; exact_mod_cast hlt) (fun i => i.elim0) (fun i => i.elim0) (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)`. Rewrite using `[h0, Nat.cast_zero, zero_mul, topSelf_def, ← interNum_comp_equiv (ZMod l) _ (fun _ => hBg) (Equiv.emptySum (Fin 0) (Fin d)), ← hz]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Break down `x with i | a` into its components or cases. Conclude with `i.elim0`. Both sides reduce to the same expression.

Establish `hdd : d = d'` using `hiff.1 h0`. Substitute `hdd` using the available equality. Take `⟨U, hU, hgU, hU', hfree, hfin, hrank⟩` from `exists_affine_finite_free (ZMod l) (clo (π y)) (clo y) (strHom (ZMod l) (clo (π y))) (strHom (ZMod l) (clo y)) hZp hWp g hgs hgen (hδ ▸ h0)`. Establish `key` using `GlobalTheory.FieldProj.interNum_pull_eq_mul (ZMod l) (clo y) (clo (π y)) (strHom (ZMod l) (clo (π y))) g (hgs ▸ hWp) hZp U _ hgU hU hU' ⟨hfree, hfin, hrank⟩ d hZd.le (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)`. Rewrite `key` using `[hδ]`.

Rewrite using `[topSelf_def, topSelf_def]`. Use `key using 3` and compare the differences between its conclusion and the goal. Conclude with `algebra_zmod_eq _ _`. Conclude with `algebra_zmod_eq _ _`.
-/
theorem height_pull_vertical : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime],
    Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' hh hh' y l _ ⟨instW⟩
  obtain ⟨g, hgc, hgen, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  have hinj : Function.Injective g.appTop.hom := by
    have := GlobalTheory.appLE_injective_of_genericPoint_map g hgen (U := ⊤) (V := g ⁻¹ᵁ ⊤)
      ⟨genericPoint (clo y), trivial⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  haveI : Nonempty (⊤ : (clo y).Opens) := ⟨⟨genericPoint (clo y), trivial⟩⟩
  haveI : CharP Γ(clo y, ⊤) l :=
    charP_of_injective_algebraMap (algebraMap (ZMod l) Γ(clo y, ⊤)).injective l
  haveI : CharP Γ(clo (π y), ⊤) l := ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff Γ(clo y, ⊤) l n, ← map_natCast g.appTop.hom n,
      map_eq_zero_iff _ hinj]⟩
  letI instZ : Algebra (ZMod l) Γ(clo (π y), ⊤) := ZMod.algebra _ l
  have hWp : IsProjOver (strHom (ZMod l) (clo y)) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k Y q E hY (clo y) (cloι y) l
  have hZp : IsProjOver (strHom (ZMod l) (clo (π y))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k X p D hX (clo (π y)) (cloι (π y)) l
  have hgs : g ≫ strHom (ZMod l) (clo (π y)) = strHom (ZMod l) (clo y) :=
    comp_strHom fun r => congrFun (congrArg DFunLike.coe
      (RingHom.ext_zmod (g.appTop.hom.comp (algebraMap (ZMod l) _)) (algebraMap (ZMod l) _))) r

  obtain ⟨⟨m, hm⟩, -, -, -, hcl, hgd⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q (isAmb_of_isArithVar hY)
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)
  obtain ⟨d, -, hd⟩ := hm y
  obtain ⟨d', -, hd'⟩ := hm' (π y)
  have hWd : topologicalKrullDim (clo y) = d :=
    (hgd (clo y) d).1 ((hcl (clo y) (cloι y) _ d).1 (by rw [cloι_genericPoint]; exact hd))
  have hZd : topologicalKrullDim (clo (π y)) = d' :=
    (hgd' (clo (π y)) d').1 ((hcl' (clo (π y)) (cloι (π y)) _ d').1 (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q (isAmb_of_isArithVar hX) (isAmb_of_isArithVar hY) π hπ y d d' hd hd'

  have e1 := hh'.vertical (clo y) (cloι y) (ZMod l) d hWd
  have e2 := hh.vertical (clo (π y)) (cloι (π y)) (ZMod l) d' hZd
  rw [cloι_genericPoint] at e1 e2
  have ej : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have ei : (g ≫ cloι (π y)) ≫ p = g ≫ cloι (π y) ≫ p := Category.assoc _ _ _
  have t1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull (cloι y)) d = topSelfIntersection (ZMod l) (L.B.pull (cloι y ≫ π)) d :=
    topSelf_congr (ZMod l) ((L.pull π hπ).pull (cloι y) rfl).isLB (L.pull (cloι y ≫ π) ej).isLB
      (L.refines_pull_pull π hπ (cloι y) rfl ej).lbIso d
  have t2 : topSelfIntersection (ZMod l) (L.B.pull (g ≫ cloι (π y))) d =
      topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d :=
    topSelf_congr (ZMod l) (L.pull (g ≫ cloι (π y)) ei).isLB ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
      (L.refines_pull_comp (cloι (π y)) rfl g rfl ei).lbIso d
  rw [t1, ← hgc, t2] at e1
  rw [e1, e2]
  suffices key : topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d =
      (π.residueDegree y : ℤ) * topSelfIntersection (ZMod l) (L.B.pull (cloι (π y))) d' by
    rw [key]; push_cast; ring
  have hB : (L.B.pull (cloι (π y))).IsLB := (L.pull (cloι (π y)) rfl).isLB
  have hBg : ((L.B.pull (cloι (π y))).pull g).IsLB := ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
  have hclo : topologicalKrullDim (closure ({g (genericPoint (clo y))} : Set (clo (π y)))) = d' := by
    rw [hgen, (genericPoint_spec (clo (π y))).def]
    exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.trans hZd
  by_cases h0 : π.residueDegree y = 0
  · have hne : d ≠ d' := fun e => (hiff.2 e) h0
    have hlt : d' < d := lt_of_le_of_ne hle (Ne.symm hne)
    have hz := GlobalTheory.PullVanish.interNum_pull_eq_zero (ZMod l) 0 d (clo y) (clo (π y)) hWp
      (by rw [Nat.zero_add, hWd]) g (by rw [hclo]; exact_mod_cast hlt)
      (fun i => i.elim0) (fun i => i.elim0) (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [h0, Nat.cast_zero, zero_mul, topSelf_def, ← interNum_comp_equiv (ZMod l) _ (fun _ => hBg)
      (Equiv.emptySum (Fin 0) (Fin d)), ← hz]
    congr 1
    funext x
    rcases x with i | a
    · exact i.elim0
    · rfl
  · have hdd : d = d' := hiff.1 h0
    subst hdd
    obtain ⟨U, hU, hgU, hU', hfree, hfin, hrank⟩ := exists_affine_finite_free (ZMod l) (clo (π y)) (clo y)
      (strHom (ZMod l) (clo (π y))) (strHom (ZMod l) (clo y)) hZp hWp g hgs hgen (hδ ▸ h0)
    have key := GlobalTheory.FieldProj.interNum_pull_eq_mul (ZMod l) (clo y) (clo (π y)) (strHom (ZMod l) (clo (π y))) g
      (hgs ▸ hWp) hZp U _ hgU hU hU' ⟨hfree, hfin, hrank⟩ d hZd.le (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [hδ] at key
    rw [topSelf_def, topSelf_def]
    convert key using 3
    · exact algebra_zmod_eq _ _
    · exact algebra_zmod_eq _ _

end GlobalTheory.ProjFormulaVert
