import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalExt

/- English proof (translation)
Use `choose Z p hp hy he using h`. Establish `: Surjective (Limits.Sigma.desc p)` using `Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hy y⟩)`. Establish `: Epi (Limits.Sigma.desc p)` using `Flat.epi_of_flat_of_surjective _`. Rewrite using `[← cancel_epi (Limits.Sigma.desc p)]`. Use `Limits.Sigma.hom_ext _ _ fun y => ?_` and prove the remaining obligations.

Rewrite using `[Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc_assoc, he]`.
-/
theorem hom_ext_of_flat_family {Y X : Scheme.{0}} (f g : Y ⟶ X)
    (h : ∀ y : Y, ∃ (Z : Scheme.{0}) (p : Z ⟶ Y), Flat p ∧ y ∈ Set.range p ∧ p ≫ f = p ≫ g) : f = g := by
  choose Z p hp hy he using h
  have : Surjective (Limits.Sigma.desc p) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hy y⟩)
  have : Epi (Limits.Sigma.desc p) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (Limits.Sigma.desc p)]
  refine Limits.Sigma.hom_ext _ _ fun y => ?_
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc_assoc, he]

/- English proof (translation)
Establish `w : ∀ z, X.hom (ψ.left z) = Y.hom z` using `fun z => by rw [← Scheme.Hom.comp_apply, Over.w]`. Establish `hy : Y.hom y ∈ Set.range f` using `by rw [← w, ← h, w]; exact hx`. Take `⟨x', rfl⟩ : x ∈ Set.range (pullback.fst Y.hom f)` from `by rw [Scheme.Pullback.range_fst]; exact hx`. Take `⟨y', rfl⟩ : y ∈ Set.range (pullback.fst Y.hom f)` from `by rw [Scheme.Pullback.range_fst]; exact hy`. Establish `e : ((Over.pullback f).map ψ).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ ψ.left` using `pullback.lift_fst _ _ _`.

Establish `e' : ∀ z, pullback.fst X.hom f (((Over.pullback f).map ψ).left z) = ψ.left (pullback.fst Y.hom f z)` using `fun z => congr($e z)`. Rewrite `h` using `[← e', ← e']`. Establish `h₁` using `(pullback.fst X.hom f).isEmbedding.injective h`. Establish `: IsIso ((Over.pullback f).map ψ).left` using `inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback f).map ψ)))`. Rewrite using `[((Over.pullback f).map ψ).left.isEmbedding.injective h₁]`.
-/
theorem eq_of_isIso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) [IsPreimmersion f] {Y X : Over S} (ψ : Y ⟶ X)
    [IsIso ((Over.pullback f).map ψ)] {x y : Y.left} (hx : Y.hom x ∈ Set.range f) (h : ψ.left x = ψ.left y) :
    x = y := by
  have w : ∀ z, X.hom (ψ.left z) = Y.hom z := fun z => by rw [← Scheme.Hom.comp_apply, Over.w]
  have hy : Y.hom y ∈ Set.range f := by rw [← w, ← h, w]; exact hx
  obtain ⟨x', rfl⟩ : x ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y', rfl⟩ : y ∈ Set.range (pullback.fst Y.hom f) := by rw [Scheme.Pullback.range_fst]; exact hy
  have e : ((Over.pullback f).map ψ).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have e' : ∀ z, pullback.fst X.hom f (((Over.pullback f).map ψ).left z) = ψ.left (pullback.fst Y.hom f z) :=
    fun z => congr($e z)
  rw [← e', ← e'] at h
  have h₁ := (pullback.fst X.hom f).isEmbedding.injective h
  have : IsIso ((Over.pullback f).map ψ).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback f).map ψ)))
  rw [((Over.pullback f).map ψ).left.isEmbedding.injective h₁]

variable {R : Type} [CommRing R] (I : Ideal R)

instance isClosedImmersion_thick (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/- English proof (translation)
Establish `h` using `_root_.range_comap_of_surjective _ (Ideal.Quotient.mk (I ^ (e + 1))) Ideal.Quotient.mk_surjective`. Rewrite `h` using `[Ideal.mk_ker]`. Use `(h.ge.antisymm h.le ▸ Iff.rfl : s ∈ Set.range (thick R I e) ↔ s ∈ PrimeSpectrum.zeroLocus (I ^ (e + 1) : Ideal R)).trans ?_` and prove the remaining obligations. Use `s.isPrime` as an intermediate fact. Conclude with `Ideal.IsPrime.pow_le_iff (I := I) (P := s.asIdeal) (Nat.succ_ne_zero e)`.
-/
theorem range_thick (e : ℕ) (s : Spec (CommRingCat.of R)) : s ∈ Set.range (thick R I e) ↔ I ≤ s.asIdeal := by
  have h := _root_.range_comap_of_surjective _ (Ideal.Quotient.mk (I ^ (e + 1))) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h
  refine (h.ge.antisymm h.le ▸ Iff.rfl : s ∈ Set.range (thick R I e) ↔ s ∈ PrimeSpectrum.zeroLocus (I ^ (e + 1) : Ideal R)).trans ?_
  have := s.isPrime
  exact Ideal.IsPrime.pow_le_iff (I := I) (P := s.asIdeal) (Nat.succ_ne_zero e)

/- English proof (translation)
Establish `e₁ : ((Over.pullback (thick R I e)).map ψ).left ≫ pullback.fst X.hom (thick R I e) = pullback.fst Y.hom (thick R I e) ≫ ψ.left` using `pullback.lift_fst _ _ _`. Use `⟨fun h => h ▸ e₁.symm, fun h => Over.OverMorphism.ext (pullback.hom_ext (e₁.trans h) ?_)⟩` and prove the remaining obligations. Conclude with `(Over.w _).trans (Over.w j).symm`.
-/
theorem map_eq_iff (e : ℕ) {Y X : Over (Spec (CommRingCat.of R))} (ψ : Y ⟶ X)
    (j : thickObj R I e Y ⟶ thickObj R I e X) :
    (Over.pullback (thick R I e)).map ψ = j ↔ (fstG I e Y).left ≫ ψ.left = j.left ≫ (fstG I e X).left := by
  have e₁ : ((Over.pullback (thick R I e)).map ψ).left ≫ pullback.fst X.hom (thick R I e) =
      pullback.fst Y.hom (thick R I e) ≫ ψ.left := pullback.lift_fst _ _ _
  refine ⟨fun h => h ▸ e₁.symm, fun h => Over.OverMorphism.ext (pullback.hom_ext (e₁.trans h) ?_)⟩
  exact (Over.w _).trans (Over.w j).symm

/- English proof (translation)
The claim follows from `(GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 X a b fun e => ((map_eq_iff I e a _).1 (h e)).trans ((map_eq_iff I e b _).1 rfl).symm`.
-/
theorem hom_ext_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] {X : Over (Spec (CommRingCat.of R))}
    [IsSeparated X.hom] {a b : H ⟶ X}
    (h : ∀ e, (Over.pullback (thick R I e)).map a = (Over.pullback (thick R I e)).map b) : a = b :=
  (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 X a b fun e =>
    ((map_eq_iff I e a _).1 (h e)).trans ((map_eq_iff I e b _).1 rfl).symm

/- English proof (translation)
Establish `h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom` using `inferInstanceAs (Smooth (𝟙 _))`. Establish `h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom` using `inferInstanceAs (GeometricallyConnected (𝟙 _))`. Establish `h2 : Smooth (G' ⊗ G').hom` using `inferInstanceAs (Smooth (pullback.fst G'.hom G'.hom ≫ G'.hom))`. Establish `h2' : GeometricallyConnected (G' ⊗ G').hom` using `GeometricallyConnected.comp (pullback.fst G'.hom G'.hom) G'.hom`. Prove the components needed by the constructor for the conclusion.

Use `hom_ext_thick I hI _ fun e => ?_` and prove the remaining obligations. Use `(h e).one_hom` as an intermediate fact. Rewrite `this` using `[Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi]`. Rewrite using `[Functor.map_comp, this]`. Use `hom_ext_thick I hI _ fun e => ?_` and prove the remaining obligations.

Use `(h e).mul_hom` as an intermediate fact. Rewrite `this` using `[Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc, cancel_epi]`. Rewrite using `[Functor.map_comp, this, Functor.map_comp]`.
-/
theorem isMonHom_of_thick [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) {G' G : Over (Spec (CommRingCat.of R))}
    [GrpObj G'] [GrpObj G] [Smooth G'.hom] [GeometricallyConnected G'.hom] [IsSeparated G.hom] (ψ : G' ⟶ G)
    (h : ∀ e, IsMonHom ((Over.pullback (thick R I e)).map ψ)) : IsMonHom ψ := by
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  have h2 : Smooth (G' ⊗ G').hom := inferInstanceAs (Smooth (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have h2' : GeometricallyConnected (G' ⊗ G').hom :=
    GeometricallyConnected.comp (pullback.fst G'.hom G'.hom) G'.hom
  constructor
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at this
    rw [Functor.map_comp, this]
  · refine hom_ext_thick I hI _ fun e => ?_
    have := (h e).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi] at this
    rw [Functor.map_comp, this, Functor.map_comp]

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Use `hG'.smooth` as an intermediate fact.

Use `hG'.separated` as an intermediate fact. Use `hG'.quasiCompact` as an intermediate fact. Use `hG'.geomConnected` as an intermediate fact. Use `GlobalTheory.GenericExt.isOpenImmersion_jK R` as an intermediate fact. Use `GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)` as an intermediate fact.

Establish `hint : IsIntegral G'.left` using `(GlobalTheory.isIntegral_and_isNormalScheme_of_smooth_dvr R (FractionRing R) G' inferInstance (inferInstanceAs (ConnectedSpace ↥(pullback G'.hom (jK R))))).1`. Establish `hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left` using `fun x hx => by show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))`. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `(range_thick I 0 _).2 hx`. Take `⟨ψ, hψ⟩` from `GlobalTheory.GenericExt.main R G' G ΦK.hom fun x hx => by`.

Take `⟨x, rfl⟩` from `hx0 x (by rw [hx, hI]; exact le_rfl)`. Take `⟨T, g', g, h₁, h₂, -, h₄, -⟩` from `H x`. Conclude with `⟨T, g', g, h₁, h₂, h₄⟩`. Establish `eψ : ΦK.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left`. Rewrite using `[← hψ]`.

Conclude with `pullback.lift_fst _ _ _`. Establish `hth : ∀ e : ℕ, (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left` using `fun e => by`. Use `hom_ext_of_flat_family _ _ fun y => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `hx0 ((fstG I e G').left y) ((range_thick I e _).1 (by`. Establish `: (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e))` using `⟨y, rfl⟩`.

Rewrite `this` using `[Scheme.Pullback.range_fst]`. Conclude with `this))`. Take `⟨T, g', g, h₁, h₂, h₃, h₄, h₅⟩` from `H x`. Establish `hg : g' ≫ ψ.left = g`. Set `a : Over.mk (g' ≫ G'.hom) ⟶ G` to `Over.homMk (g' ≫ ψ.left) (by simp)`.

Set `b : Over.mk (g' ≫ G'.hom) ⟶ G` to `Over.homMk g h₃`. Establish `: IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R))` using `inferInstance`. Establish `: IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R)))` using `inferInstance`. Use `GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b) (pullback.fst g' (pullback.fst G'.hom (jK R))) (by` as an intermediate fact. Use `h₄ _ _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm` as an intermediate fact.

Rewrite `this` using `[eψ]`. Conclude with `(pullback.condition_assoc _).trans this)`. Conclude with `congr(($this).left)`. Use `⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_snd] show (fstG I e G').left y ∈ Set.range g'`.

Rewrite using `[← hx]`. Conclude with `h₂`. Rewrite using `[h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]`. Establish `hth' : ∀ e, (Over.pullback (thick R I e)).map ψ = (j e).hom` using `fun e => (map_eq_iff I e ψ _).2 (hth e)`. Establish `hmon : IsMonHom ψ` using `isMonHom_of_thick I (by rw [hI, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ψ fun e => hth' e ▸ hj e`.

Establish `hK : IsIso ((Over.pullback (jK R)).map ψ)` using `hψ ▸ inferInstance`. Establish `h0 : IsIso ((Over.pullback (thick R I 0)).map ψ)` using `hth' 0 ▸ inferInstance`. Establish `w : ψ.left ≫ G.hom = G'.hom` using `Over.w ψ`. Establish `: IsSeparated (ψ.left ≫ G.hom)` using `w ▸ inferInstance`. Establish `: LocallyOfFiniteType (ψ.left ≫ G.hom)` using `w ▸ inferInstance`.

Establish `: QuasiCompact (ψ.left ≫ G.hom)` using `w ▸ inferInstance`. Establish `: IsSeparated ψ.left` using `.of_comp _ G.hom`. Establish `: LocallyOfFiniteType ψ.left` using `locallyOfFiniteType_of_comp _ G.hom`. Establish `: QuasiCompact ψ.left` using `.of_comp _ G.hom`. Establish `: LocallyQuasiFinite ψ.left` using `LocallyQuasiFinite.of_injective fun x y h => by`.

Distinguish the cases in `hx : G'.hom x ∈ Set.range (jK R)`. Conclude with `eq_of_isIso_pullback (jK R) ψ hx h`. Use `eq_of_isIso_pullback (thick R I 0) ψ ((range_thick I 0 _).2 ?_) h` and prove the remaining obligations. Rewrite using `[GlobalTheory.GenericExt.eq_closedPoint_of_not_mem_range R _ hx, hI]`. Conclude with `le_rfl`.

Establish `: IsIso ψ` using `GlobalTheory.isIso_of_quasiFinite_of_isIso_genericFibre_dvr R (FractionRing R) G' G ψ hmon inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hK`. Conclude with `⟨asIso ψ, hmon, hψ, hth⟩`.
-/
theorem exists_iso [IsDomain R] [IsDiscreteValuationRing R] (hI : I = IsLocalRing.maximalIdeal R)
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G) (hj : ∀ e, IsMonHom (j e).hom)
    (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (H : ∀ x : (thickObj R I 0 G').left, ∃ (T : Scheme.{0}) (g' : T ⟶ G'.left) (g : T ⟶ G.left), Flat g' ∧
      (fstG I 0 G').left x ∈ Set.range g' ∧ g ≫ G.hom = g' ≫ G'.hom ∧
      (∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
        r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧
      ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have := hG'.geomConnected
  have := GlobalTheory.GenericExt.isOpenImmersion_jK R
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have hint : IsIntegral G'.left :=
    (GlobalTheory.isIntegral_and_isNormalScheme_of_smooth_dvr R (FractionRing R) G' inferInstance
      (inferInstanceAs (ConnectedSpace ↥(pullback G'.hom (jK R))))).1
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (range_thick I 0 _).2 hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.GenericExt.main R G' G ΦK.hom fun x hx => by
    obtain ⟨x, rfl⟩ := hx0 x (by rw [hx, hI]; exact le_rfl)
    obtain ⟨T, g', g, h₁, h₂, -, h₄, -⟩ := H x
    exact ⟨T, g', g, h₁, h₂, h₄⟩
  have eψ : ΦK.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hth : ∀ e : ℕ, (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := fun e => by
    refine hom_ext_of_flat_family _ _ fun y => ?_
    obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((range_thick I e _).1 (by
      have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
      rw [Scheme.Pullback.range_fst] at this
      exact this))
    obtain ⟨T, g', g, h₁, h₂, h₃, h₄, h₅⟩ := H x
    have hg : g' ≫ ψ.left = g := by
      let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
      let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g h₃
      have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
      have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
      have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
        (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
          have := h₄ _ _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
          rw [eψ] at this
          exact (pullback.condition_assoc _).trans this)
      exact congr(($this).left)
    refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
    · rw [Scheme.Pullback.range_snd]
      show (fstG I e G').left y ∈ Set.range g'
      rw [← hx]; exact h₂
    · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]
  have hth' : ∀ e, (Over.pullback (thick R I e)).map ψ = (j e).hom := fun e => (map_eq_iff I e ψ _).2 (hth e)
  have hmon : IsMonHom ψ := isMonHom_of_thick I (by rw [hI, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ψ
    fun e => hth' e ▸ hj e
  have hK : IsIso ((Over.pullback (jK R)).map ψ) := hψ ▸ inferInstance
  have h0 : IsIso ((Over.pullback (thick R I 0)).map ψ) := hth' 0 ▸ inferInstance
  have w : ψ.left ≫ G.hom = G'.hom := Over.w ψ
  have : IsSeparated (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : LocallyOfFiniteType (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : QuasiCompact (ψ.left ≫ G.hom) := w ▸ inferInstance
  have : IsSeparated ψ.left := .of_comp _ G.hom
  have : LocallyOfFiniteType ψ.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ψ.left := .of_comp _ G.hom
  have : LocallyQuasiFinite ψ.left := LocallyQuasiFinite.of_injective fun x y h => by
    by_cases hx : G'.hom x ∈ Set.range (jK R)
    · exact eq_of_isIso_pullback (jK R) ψ hx h
    · refine eq_of_isIso_pullback (thick R I 0) ψ ((range_thick I 0 _).2 ?_) h
      rw [GlobalTheory.GenericExt.eq_closedPoint_of_not_mem_range R _ hx, hI]; exact le_rfl
  have : IsIso ψ := GlobalTheory.isIso_of_quasiFinite_of_isIso_genericFibre_dvr R (FractionRing R) G' G ψ hmon
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hK
  exact ⟨asIso ψ, hmon, hψ, hth⟩

/- English proof (translation)
Introduce `l₁ l₂ R _ _ _ I hA hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK hw`. Use `exists_iso I hI hG hG' j (fun e => (hj e).1) ΦK fun x => ?_` and prove the remaining obligations. Take `⟨B, _, _, g', g, jL, jL', h₁, -, h₃, h₄, h₅, h₆, h₇⟩` from `GlobalTheory.exists_completed_point_of_thickenings R I hA hI D D' A A' G G' hG hG' U U' hD j hj x`. Take `⟨v, hv, -⟩` from `GlobalTheory.T.generic_iso_agrees_on_complete_points_alt l₁ l₂ R I hA hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hw B g' g jL jL' h₁ ⟨h₅, h₆, h₇⟩`. Conclude with `⟨_, g', g, h₃, h₄, h₆.trans h₅.symm, fun Z ρ r h => (hv Z ρ r h).1, h₇.2.2⟩`.
-/
theorem main : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  intro l₁ l₂ R _ _ _ I hA hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK hw
  refine exists_iso I hI hG hG' j (fun e => (hj e).1) ΦK fun x => ?_
  obtain ⟨B, _, _, g', g, jL, jL', h₁, -, h₃, h₄, h₅, h₆, h₇⟩ :=
    GlobalTheory.exists_completed_point_of_thickenings R I hA hI D D' A A' G G' hG hG' U U' hD j hj x
  obtain ⟨v, hv, -⟩ := GlobalTheory.T.generic_iso_agrees_on_complete_points_alt l₁ l₂ R I hA hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hw B g' g jL jL' h₁
    ⟨h₅, h₆, h₇⟩
  exact ⟨_, g', g, h₃, h₄, h₆.trans h₅.symm, fun Z ρ r h => (hv Z ρ r h).1, h₇.2.2⟩

end GlobalTheory.FormalExt
