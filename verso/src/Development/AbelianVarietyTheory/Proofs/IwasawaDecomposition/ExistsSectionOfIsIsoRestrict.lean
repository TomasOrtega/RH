import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHomStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwistedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartierStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSectionsStatement

noncomputable section

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

/- English proof (translation)
Rewrite using `[← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]`. Conclude with `fun w hw => (h w hw).elim`.
-/
theorem eq_top_of_forall_notMem {W : Scheme.{0}} (I : W.IdealSheafData) (h : ∀ w, w ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
  exact fun w hw => (h w hw).elim

/- English proof (translation)
Introduce `x`. Take `⟨_, ⟨U, hU, rfl⟩, hx, -⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩`.
-/
theorem effCartier_top (W : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : W.IdealSheafData) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression.
-/
theorem mem_support_comap {W X : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (w : W) :
    w ∈ (J.comap g).support ↔ g w ∈ J.support := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

/- English proof (translation)
Take `⟨L, m, σ, hσ⟩` from `GlobalTheory.T.exists_sections_generate_ideal_projective R X s hs J`. Establish `: IsProper (PSpace.str R m)` using `isProper_str R m`. Establish `: LocallyOfFiniteType s`. Take `⟨n, i, hi, rfl⟩` from `hs`. Use `isProper_str R n` as an intermediate fact.

Use `infer_instance`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian s`. Set `U : X.Opens` to `J.support.compl`. Establish `hU : ∀ x : U.toScheme, U.ι x ∉ J.support` using `fun x => x.2`. Establish `htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤` using `fun g hg => eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)`.

Take `⟨φ, hφ, hφσ⟩` from `GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ) (by rw [htop _ hU]; exact effCartier_top _)`. Set `b` to `graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm`. Set `c` to `graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm`. Set `j` to `graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm`. Establish `hjb : j ≫ b = U.ι` using `graphClosure.incl_fst ..`.

Establish `hjc : j ≫ c = φ` using `graphClosure.incl_snd ..`. Establish `hbc : Proportional σ b c` using `.of_comp j (by rwa [hjb, hjc])`. Use `⟨_, b, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance inferInstance fun t => ?_, fun W g hg => ?_⟩, ?_, fun V hV => graphClosure.isIso_fst_restrict_of_le _ _ …` and prove the remaining obligations. Rewrite using `[mem_support_comap, ← Scheme.Hom.comp_apply, hjb]`. Conclude with `hU t`.

Take `⟨ψ, hψ, hψσ⟩` from `GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg`. Establish `hd` using `GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg`. Set `d` to `Scheme.Opens.ι (X := W) (J.comap g).support.compl`. Establish `hdU : ∀ t, (d ≫ g) t ∉ J.support` using `fun t ht => t.2 ((mem_support_comap J g _).2 ht)`. Set `w` to `IsOpenImmersion.lift U.ι (d ≫ g) (by`.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨⟨_, hdU t⟩, rfl⟩)`. Establish `hw : w ≫ U.ι = d ≫ g` using `IsOpenImmersion.lift_fac ..`. Establish `hw' : d ≫ ψ = w ≫ φ` using `GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ) (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)`. Establish `key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j` using `fun h hh => by`.

Establish `H` using `graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm`. Establish `e : w ≫ U.ι = (d ≫ h) ≫ b` using `by rw [hw, Category.assoc, hh]`. Establish `h1` using `H.lift_fst w (d ≫ h) e`. Rewrite `h1` using `[Category.comp_id]`. Rewrite using `[← H.lift_snd w (d ≫ h) e, h1]`.

Establish `hl` using `graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'`. Conclude with `⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm) (hh.trans hl.symm)⟩`. Take `⟨n, i, hi, e⟩` from `ProjSpace.isProjOver_of_isPullback (IsPullback.of_hasPullback s (PSpace.str R m)) hs (ProjSpace.isProjOver_pspace_str R m)`. Conclude with `⟨n, graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm ≫ i, inferInstance, by`. Rewrite using `[Category.assoc, e, graphClosure.ι_fst_assoc]⟩`.
-/
theorem exists_blowup {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (X' : Scheme.{0}) (b : X' ⟶ X), FinalTheorems.Blowup b J ∧ IsProjOver (b ≫ s) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V) := by
  obtain ⟨L, m, σ, hσ⟩ := GlobalTheory.T.exists_sections_generate_ideal_projective R X s hs J
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  refine ⟨_, b, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance inferInstance fun t => ?_,
    fun W g hg => ?_⟩, ?_,
    fun V hV => graphClosure.isIso_fst_restrict_of_le _ _ _ _ _ V (by rw [Scheme.Opens.opensRange_ι]; exact hV)⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · obtain ⟨n, i, hi, e⟩ := ProjSpace.isProjOver_of_isPullback (IsPullback.of_hasPullback s (PSpace.str R m)) hs
      (ProjSpace.isProjOver_pspace_str R m)
    exact ⟨n, graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm ≫ i, inferInstance, by
      rw [Category.assoc, e, graphClosure.ι_fst_assoc]⟩

/- English proof (translation)
Establish `h₁ : IsPullback (inv (f ∣_ U)) (𝟙 _) (f ∣_ U) (𝟙 _)` using `.of_horiz_isIso ⟨by simp⟩`. Establish `hj : IsPullback (inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) (𝟙 _) f U.ι`. Simplify using `using h₁.paste_horiz (isPullback_morphismRestrict f U).flip`. Use `⟨_, hj, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, -⟩` from `Scheme.exists_preimage_of_isPullback hj x ⟨f x, hx⟩ rfl`.

Conclude with `⟨y, hy⟩`.
-/
theorem exists_section_of_isIso_restrict {N X : Scheme.{0}} (f : N ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    ∃ j : U.toScheme ⟶ N, IsPullback j (𝟙 _) f U.ι ∧ ((f ⁻¹ᵁ U : N.Opens) : Set N) ⊆ Set.range j := by
  have h₁ : IsPullback (inv (f ∣_ U)) (𝟙 _) (f ∣_ U) (𝟙 _) := .of_horiz_isIso ⟨by simp⟩
  have hj : IsPullback (inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) (𝟙 _) f U.ι := by
    simpa using h₁.paste_horiz (isPullback_morphismRestrict f U).flip
  refine ⟨_, hj, fun x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hj x ⟨f x, hx⟩ rfl
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `: LocallyOfFiniteType s`. Take `⟨n, i, hi, rfl⟩` from `hs`. Use `isProper_str O n` as an intermediate fact. Use `infer_instance`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian s`.

Establish `hN : GlobalTheory.IsNormalScheme V.toScheme` using `.of_pred hV`. Establish `hfin : IsFinite V.ι.fromNormalization` using `isFinite_fromNormalization_of_locallyOfFiniteType (o := .of O) V.ι s fun x _ => hc x`. Establish `H` using `isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm`. Establish `: Flat (V.ι.toNormalization ≫ V.ι.fromNormalization ≫ s)` using `by simpa`. Use `⟨_, V.ι.fromNormalization, hfin, IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization V.ι _, ?_, ?_⟩` and prove the remaining obligations.

Establish `e` using `IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip`. Rewrite using `[← e]`. Use `infer_instance`. Use `V.ι.toNormalization.denseRange.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Express the relevant statement in the definitionally equal form `V.ι.fromNormalization (V.ι.toNormalization x) ∈ V`. Rewrite using `[← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]`. Conclude with `x.2`.
-/
theorem exists_normal_model {O : Type} [CommRing O] [IsDedekindDomain O] {X : Scheme.{0}} (s : X ⟶ Sp O) (V : X.Opens)
    (hs : IsProjOver s) (hV : Geo.Tor.IsNormalScheme V.toScheme) [Flat (V.ι ≫ s)]
    (hc : ∀ x : V.toScheme, CharZero (V.toScheme.residueField x)) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ X), IsFinite ν ∧ Geo.Tor.IsNormalScheme N ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧
      IsIso (ν ∣_ V) ∧ Dense ((ν ⁻¹ᵁ V : N.Opens) : Set N) := by
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str O n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hN : GlobalTheory.IsNormalScheme V.toScheme := .of_pred hV
  have hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := .of O) V.ι s fun x _ => hc x
  have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
  have : Flat (V.ι.toNormalization ≫ V.ι.fromNormalization ≫ s) := by simpa
  refine ⟨_, V.ι.fromNormalization, hfin, IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs,
    flat_normalization V.ι _, ?_, ?_⟩
  · have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  · refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2

end GlobalTheory.ProjBlowup

end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ProjBlowup

section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Use `(isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1` and prove the remaining obligations. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`. Break down `hW with h | h` into its components or cases.

Conclude with `absurd (by exact_mod_cast h) hp`. Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`.
-/
theorem isDiscreteValuationRing_coeff {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

/- English proof (translation)
Introduce `τ k _ i hi`. Use `⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩` and prove the remaining obligations. Use `(LieMet.isComb_iff (fun j => LieMet.tanOf (hu τ j)) (Pi.single i 1) (LieMet.tanOf (hu τ i))).2 ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same, one_smul]`.
-/
theorem sameFlag_refl (ty : (E →+* ℂ) → Finset ℕ) {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (u : Vecs Dw t R) (hu : ∀ τ i, IsTanAtG t x (u τ i)) : SameFlag ty t x u u := by
  intro τ k _ i hi
  refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  refine (LieMet.isComb_iff (fun j => LieMet.tanOf (hu τ j)) (Pi.single i 1) (LieMet.tanOf (hu τ i))).2 ?_
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul]

/- English proof (translation)
Establish `e : spMap (RingHom.id (i.c.V W)) = 𝟙 _` using `Spec.map_id _`. Establish `H₀ : IsPullback (𝟙 _) (Y i).s (Y i).s (spMap (RingHom.id (i.c.V W)))`. Rewrite using `[e]; exact IsPullback.of_horiz_isIso ⟨by simp⟩`. Use `⟨RingHom.id _, H₀.isoPullback.hom, 𝟙 _, fun _ => rfl, by simp, by simp, inferInstance, by simp, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.div_self (by have := i.l.three_le; omega), pow_one, h]; simp`.

Rewrite using `[Nat.div_self i.l.A_pos, pow_one, h]`. Simplify using the standard rewrite rules.
-/
theorem isTrans_id (i : Idx H p) (mu : SABMap (Y i).t (Y i).t (𝟙 _)) (h : mu.φ = 𝟙 _) :
    LocM.IsTrans (Y := Y) i i (𝟙 _) mu := by
  have e : spMap (RingHom.id (i.c.V W)) = 𝟙 _ := Spec.map_id _
  have H₀ : IsPullback (𝟙 _) (Y i).s (Y i).s (spMap (RingHom.id (i.c.V W))) := by
    rw [e]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨RingHom.id _, H₀.isoPullback.hom, 𝟙 _, fun _ => rfl, by simp, by simp, inferInstance, by simp,
    fun a => ?_, fun a => ?_⟩
  · rw [Nat.div_self (by have := i.l.three_le; omega), pow_one, h]; simp
  · rw [Nat.div_self i.l.A_pos, pow_one, h]; simp

/- English proof (translation)
Take `⟨mu, hmu⟩` from `ObjMaps.exists_sab_id (Y Z.i).t`. Take `⟨a, ha⟩` from `Set.mem_iUnion.1 (Z.cover.ge (hw ⟨default, rfl⟩))`. Establish `hA : IsAffineOpen (Z.U a).1` using `(Z.U a).2`. Establish `hr : Set.range w ⊆ Set.range hA.fromSpec`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[IsAffineOpen.range_fromSpec, Subsingleton.elim x default]`. Conclude with `ha`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift hA.fromSpec w hr)`. Establish `hφ' : spMap φ.hom ≫ Z.chart a = w`. Use `IsOpenImmersion.lift_fac hA.fromSpec w hr` as an intermediate fact.

Rewrite `this` using `[← hφ]`. Conclude with `this`. Establish `hf` using `GlobalTheory.T.isFrame_baseChange_ringHom E H Dw _ _ _ _ _ _ _ φ.hom _ _ (Z.frame a)`. Rewrite `hf` using `[← Category.assoc, hφ']`. Establish `hfl : Z.FlagAt w ((Z.fr a).bc φ.hom)` using `⟨a, φ.hom, hφ', hf, sameFlag_refl _ _ _ _ fun τ i => (hf.1 τ i).1⟩`.

Use `⟨𝟙 _, mu, (Z.fr a).bc φ.hom, isTrans_id _ mu hmu, by simp, hfl, ?_⟩` and prove the remaining obligations. Simplify `hfl` using `only [hmu, Category.comp_id]`.
-/
theorem natImg_refl (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (hw : Set.range w ⊆ Z.opn) :
    NatImg Z Z w w := by
  obtain ⟨mu, hmu⟩ := ObjMaps.exists_sab_id (Y Z.i).t
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge (hw ⟨default, rfl⟩))
  have hA : IsAffineOpen (Z.U a).1 := (Z.U a).2
  have hr : Set.range w ⊆ Set.range hA.fromSpec := by
    rintro _ ⟨x, rfl⟩
    rw [IsAffineOpen.range_fromSpec, Subsingleton.elim x default]
    exact ha
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hA.fromSpec w hr)
  have hφ' : spMap φ.hom ≫ Z.chart a = w := by
    have := IsOpenImmersion.lift_fac hA.fromSpec w hr
    rw [← hφ] at this
    exact this
  have hf := GlobalTheory.T.isFrame_baseChange_ringHom E H Dw _ _ _ _ _ _ _ φ.hom _ _ (Z.frame a)
  rw [← Category.assoc, hφ'] at hf
  have hfl : Z.FlagAt w ((Z.fr a).bc φ.hom) :=
    ⟨a, φ.hom, hφ', hf, sameFlag_refl _ _ _ _ fun τ i => (hf.1 τ i).1⟩
  refine ⟨𝟙 _, mu, (Z.fr a).bc φ.hom, isTrans_id _ mu hmu, by simp, hfl, ?_⟩
  simpa only [hmu, Category.comp_id] using hfl

/- English proof (translation)
Use `isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW` as an intermediate fact. Establish `hs : IsProjOver Z.s` using `⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩`. Take `⟨X', b, hb, hbs, hiso⟩` from `exists_blowup Z.s hs J.1`. Set `U : Z.X.Opens` to `⨆ a, (Z.U a).1`. Establish `hU : (U : Set Z.X) = Z.opn` using `by rw [← Z.cover]; exact TopologicalSpace.Opens.coe_iSup _`.

Establish `hbU` using `hiso U fun x hx hJ => J.2 x hJ (hU.le hx)`. Use `Z.flat` as an intermediate fact. Establish `hN : GlobalTheory.IsNormalScheme Z.X` using `Z.normal`. Establish `e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι` using `(morphismRestrict_ι b U).symm`. Establish `: IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)` using `by rw [e₀]; infer_instance`.

Establish `: Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ Z.s)` using `by rw [← Category.assoc]; infer_instance`. Establish `hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme` using `.of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)`. Take `⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩` from `exists_normal_model (b ≫ Z.s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U from x.2)`. Conclude with `charZero_of_injective_ringHom ((((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.comp ((Z.X.evaluation (Z.U a).1 _ ha).hom.comp (Z.alg a))).injective`.

Establish `hνb : IsIso ((ν ≫ b) ∣_ U)`. Rewrite using `[morphismRestrict_comp]`. Conclude with `IsIso.comp_isIso' hν hbU`. Take `⟨j, hj, hjr⟩` from `exists_section_of_isIso_restrict (ν ≫ b) U`. Establish `hjd : Dense (Set.range j)` using `hd.mono hjr`.

Take `⟨Z', e, hi, hty, hmap⟩` from `GlobalTheory.T.isPullback_of_normal_flat_proj E H Dw Xo p W Y i₀ Z N (ν ≫ b) U j hU (by rwa [Category.assoc]) hn (by rwa [Category.assoc]) hj hjd`. Use `⟨Z', hi, hty, X', b, e.hom ≫ ν, hb, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Use `hmap Z (ν ≫ b) ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => subset_rfl⟩ fun k _ w => ?_` and prove the remaining obligations. Rewrite using `[hj.w, Category.id_comp]`.

Use `natImg_refl Z _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hU.le (w x).2`.
-/
theorem exists_isNBlow (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (J : Z.Idl) :
    ∃ Z', IsNBlow Z J Z' := by
  have := isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hs : IsProjOver Z.s := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  obtain ⟨X', b, hb, hbs, hiso⟩ := exists_blowup Z.s hs J.1
  let U : Z.X.Opens := ⨆ a, (Z.U a).1
  have hU : (U : Set Z.X) = Z.opn := by rw [← Z.cover]; exact TopologicalSpace.Opens.coe_iSup _
  have hbU := hiso U fun x hx hJ => J.2 x hJ (hU.le hx)
  have := Z.flat
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι b U).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b) := by rw [e₀]; infer_instance
  have : Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ Z.s) := by rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme := .of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)
  obtain ⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩ := exists_normal_model (b ≫ Z.s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U from x.2)
    exact charZero_of_injective_ringHom ((((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.comp
      ((Z.X.evaluation (Z.U a).1 _ ha).hom.comp (Z.alg a))).injective
  have hνb : IsIso ((ν ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbU
  obtain ⟨j, hj, hjr⟩ := exists_section_of_isIso_restrict (ν ≫ b) U
  have hjd : Dense (Set.range j) := hd.mono hjr
  obtain ⟨Z', e, hi, hty, hmap⟩ := GlobalTheory.T.isPullback_of_normal_flat_proj E H Dw Xo p W Y i₀ Z N (ν ≫ b) U j hU
    (by rwa [Category.assoc]) hn (by rwa [Category.assoc]) hj hjd
  refine ⟨Z', hi, hty, X', b, e.hom ≫ ν, hb, inferInstance, ?_⟩
  rw [Category.assoc]
  refine hmap Z (ν ≫ b) ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => subset_rfl⟩ fun k _ w => ?_
  rw [hj.w, Category.id_comp]
  refine natImg_refl Z _ ?_
  rintro _ ⟨x, rfl⟩
  exact hU.le (w x).2

end

end GlobalTheory.ProjBlowup
