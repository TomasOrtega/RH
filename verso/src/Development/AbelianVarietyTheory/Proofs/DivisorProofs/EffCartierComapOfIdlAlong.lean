import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

/- English proof (translation)
Rewrite `hJ` using `[idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong]`. Use `set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he`. Establish `hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f}`. Establish `h2` using `congrArg (Ideal.map e.symm.toRingHom) hJ`. Rewrite `h2` using `[Ideal.map_span, Set.image_singleton, Ideal.map_map]`.

Establish `: e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _`. Use extensionality with `x`. Conclude with `e.symm_apply_apply x`. Rewrite `h2` using `[this, Ideal.map_id]`. Conclude with `h2`.

Introduce `x`. Use `⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩` and prove the remaining obligations. Rewrite using `[mem_nonZeroDivisors_iff]`. Use `⟨fun z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises.

Use `congrArg e hz` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, e.apply_symm_apply]`. Rewrite using `[map_zero]`. Conclude with `(mul_eq_zero.1 this).resolve_left hf`. Apply `e.injective` to reduce the goal to its premises.

Use `congrArg e hz` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, e.apply_symm_apply]`. Rewrite using `[map_zero]`. Conclude with `(mul_eq_zero.1 this).resolve_right hf`.
-/
theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift

namespace GlobalTheory.NormBlLift

/- English proof (translation)
Introduce `g n F Z S i π j _ _ J hN hji hpre R _ _ _ _ _ a y hy f hf hJ`. Take `⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩` from `hN`. Establish `hE : FinalTheorems.EffCartier (J.comap a)` using `effCartier_comap_of_idlAlong J a f hf hJ`. Establish `hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a))`. Use `effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_` and prove the remaining obligations.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf`. Rewrite using `[show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ, Ideal.map_span, Set.image_singleton]`. Take `⟨b, hb, hbu⟩` from `hB.2 _ a hE`. Establish `hK : (y ≫ j) ≫ ν = jK R ≫ b`. Use `(hB.2 _ _ hEK).unique ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, hνπ, hji, hy]`. Rewrite using `[Category.assoc, hb]`. Establish `L` using `GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK`. Take `⟨c, ⟨hc1, hc2⟩, -⟩` from `L`. Use `⟨c, by show c ≫ π = a; rw [← hνπ, ← Category.assoc, hc2, hb], fun c' hc' => ?_⟩` and prove the remaining obligations.

Establish `h1 : c' ≫ ν = b` using `hbu _ (by show (c' ≫ ν) ≫ π₀ = a; rw [Category.assoc, hνπ]; exact hc')`. Establish `hr : Set.range (jK R ≫ c') ⊆ Set.range j`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[← hpre]`. Use `show π ((jK R ≫ c') w) ∈ Set.range i`.

Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, hc', hy, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Establish `h2 : jK R ≫ c' = y ≫ j`. Establish `hl` using `IsOpenImmersion.lift_fac j (jK R ≫ c') hr`. Rewrite using `[← hl]`.

Use `congr 1`. Rewrite using `[← cancel_mono i, ← hji, ← Category.assoc, hl, Category.assoc, hc', hy, hji]`. Conclude with `(GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK).unique ⟨h2, h1⟩ ⟨hc1, hc2⟩`.
-/
theorem lift_normBl : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z S : Scheme.{0}) (i : F.X ⟶ Z) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] [IsOpenImmersion i] (J : Z.IdealSheafData), IsNormBl π J → j ≫ π = i → π ⁻¹' Set.range i = Set.range j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ F.X), jK R ≫ a = y ≫ i → ∀ f : R, f ≠ 0 → idlAlong J a = Ideal.span {f} → ∃! ξ : Sp R ⟶ S, ξ ≫ π = a := by
  intro g n F Z S i π j _ _ J hN hji hpre R _ _ _ _ _ a y hy f hf hJ
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, hbu⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  have L := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := L
  refine ⟨c, by show c ≫ π = a; rw [← hνπ, ← Category.assoc, hc2, hb], fun c' hc' => ?_⟩
  have h1 : c' ≫ ν = b := hbu _ (by show (c' ≫ ν) ≫ π₀ = a; rw [Category.assoc, hνπ]; exact hc')
  have hr : Set.range (jK R ≫ c') ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [← hpre]
    show π ((jK R ≫ c') w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, Category.assoc, hc', hy, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have h2 : jK R ≫ c' = y ≫ j := by
    have hl := IsOpenImmersion.lift_fac j (jK R ≫ c') hr
    rw [← hl]
    congr 1
    rw [← cancel_mono i, ← hji, ← Category.assoc, hl, Category.assoc, hc', hy, hji]
  exact (GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK).unique ⟨h2, h1⟩ ⟨hc1, hc2⟩

end GlobalTheory.NormBlLift
