import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

/- English proof (translation)
Substitute `hD` using the available equality. Use `(isAffineOpen_top X).isLocalization_basicOpen t` as an intermediate fact. Conclude with `RingHom.isStandardSmooth_holdsForLocalizationAway _ t`.
-/
theorem res_top_isStandardSmooth (X : Scheme.{0}) [IsAffine X] (t : Γ(X, ⊤)) (D : X.Opens) (hD : D = X.basicOpen t) :
    (X.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op).hom.IsStandardSmooth := by
  subst hD
  have := (isAffineOpen_top X).isLocalization_basicOpen t
  exact RingHom.isStandardSmooth_holdsForLocalizationAway _ t

/- English proof (translation)
Use `hV.isLocalization_basicOpen (p.appLE U V e a)` as an intermediate fact. Use `hU.isLocalization_basicOpen a` as an intermediate fact. Rewrite using `[hU.appLE_eq_away_map p hV]`. Conclude with `RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h`.
-/
theorem appLE_basicOpen_isStandardSmooth {X Y : Scheme.{0}} (p : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U) (h : (p.appLE U V e).hom.IsStandardSmooth) (a : Γ(X, U))
    (e' : Y.basicOpen (p.appLE U V e a) ≤ p ⁻¹ᵁ X.basicOpen a) :
    (p.appLE (X.basicOpen a) (Y.basicOpen (p.appLE U V e a)) e').hom.IsStandardSmooth := by
  have := hV.isLocalization_basicOpen (p.appLE U V e a)
  have := hU.isLocalization_basicOpen a
  rw [hU.appLE_eq_away_map p hV]
  exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h

/- English proof (translation)
Introduce `R _ G _ φ hsm`. Use `set s : Sp R ⟶ G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left with hsdef`. Establish `hs : s ≫ G.hom = 𝟙 (Sp R)` using `Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)`. Set `x : Sp R` to `(⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R)`. Take `⟨U, hU, V, hV, e, hxU, -, hUs, h⟩` from `GlobalTheory.LieChart.exists_isStandardSmooth_section G.hom s hs x ⊤ trivial`.

Take `⟨_, ⟨r, rfl⟩, hxr, hsub⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (show (x : PrimeSpectrum R) ∈ (SetLike.coe U : Set (PrimeSpectrum R)) from hxU) (show IsOpen (SetLike.coe U : Set (PrimeSpectrum R)) from U.isOpen)`. Establish `hr : φ r ≠ 0` using `fun h0 => hxr (show r ∈ RingHom.ker φ from h0)`. Set `t : Γ(Sp R, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of R)).inv r`. Establish `htr : (Sp R).basicOpen t = PrimeSpectrum.basicOpen r` using `basicOpen_eq_of_affine (R := CommRingCat.of R) r`. Establish `hle : (Sp R).basicOpen t ≤ U`.

Rewrite using `[htr]`. Conclude with `hsub`. Set `a : Γ(Sp R, U)` to `(Sp R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t`. Establish `hat : (Sp R).basicOpen a = (Sp R).basicOpen t`. Rewrite using `[Scheme.basicOpen_res]`.

Conclude with `inf_eq_right.2 hle`. Establish `e' : G.left.basicOpen (G.hom.appLE U V e a) ≤ G.hom ⁻¹ᵁ (Sp R).basicOpen a`. Simplify using `[Scheme.Hom.appLE]`. Establish `h1` using `appLE_basicOpen_isStandardSmooth G.hom hU hV e h a e'`. Establish `h2` using `res_top_isStandardSmooth (Sp R) t _ hat`.

Use `⟨G.left.basicOpen (G.hom.appLE U V e a), r, hV.basicOpen _, hr, ?_, ?_⟩` and prove the remaining obligations. Establish `h3 : (G.hom.appLE ⊤ (G.left.basicOpen (G.hom.appLE U V e a)) (fun _ _ => trivial)).hom.IsStandardSmooth`. Use `Scheme.Hom.map_appLE G.hom e' (homOfLE (le_top : (Sp R).basicOpen a ≤ ⊤)).op` as an intermediate fact. Establish `e3` using `congrArg CommRingCat.Hom.hom this`. Rewrite `e3` using `[CommRingCat.hom_comp]`.

Rewrite using `[← e3]`. Conclude with `h1.comp h2`. Conclude with `RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h3`. Introduce `y _`. Establish `hz : (spMap (algebraMap R (Localization.Away r))) y ∈ (Sp R).basicOpen t`.

Rewrite using `[htr]`. Use `PrimeSpectrum.localization_away_comap_range (Localization.Away r) r` as an intermediate fact. Conclude with `this.subset ⟨y, rfl⟩`. Use `set z := (spMap (algebraMap R (Localization.Away r))) y with hzdef`. Establish `hps : G.hom (s z) = z` using `by rw [← Scheme.Hom.comp_apply, hs]; rfl`.

Establish `h1 : s z ∈ V` using `hUs (hle hz)`. Establish `h2 : s z ∈ G.hom ⁻¹ᵁ (Sp R).basicOpen a` using `by show G.hom (s z) ∈ (Sp R).basicOpen a`. Rewrite using `[hps, hat]`. Conclude with `hz`. Use `show (spMap (algebraMap R (Localization.Away r)) ≫ s) y ∈ G.left.basicOpen (G.hom.appLE U V e a)`.

Rewrite using `[Scheme.Hom.comp_apply]`. Use `show s z ∈ G.left.basicOpen (G.hom.appLE U V e a)`. Simplify `And.intro h1 h2` using `[Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]`.
-/
theorem exists_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (r : R), IsAffineOpen V ∧ φ r ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    ⊤ ≤ (spMap (algebraMap R (Localization.Away r)) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left) ⁻¹ᵁ V := by
  intro R _ G _ φ hsm
  set s : Sp R ⟶ G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left with hsdef
  have hs : s ≫ G.hom = 𝟙 (Sp R) := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
  let x : Sp R := (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R)
  obtain ⟨U, hU, V, hV, e, hxU, -, hUs, h⟩ :=
    GlobalTheory.LieChart.exists_isStandardSmooth_section G.hom s hs x ⊤ trivial
  obtain ⟨_, ⟨r, rfl⟩, hxr, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
    (show (x : PrimeSpectrum R) ∈ (SetLike.coe U : Set (PrimeSpectrum R)) from hxU)
    (show IsOpen (SetLike.coe U : Set (PrimeSpectrum R)) from U.isOpen)
  have hr : φ r ≠ 0 := fun h0 => hxr (show r ∈ RingHom.ker φ from h0)
  let t : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv r
  have htr : (Sp R).basicOpen t = PrimeSpectrum.basicOpen r :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) r
  have hle : (Sp R).basicOpen t ≤ U := by
    rw [htr]; exact hsub
  let a : Γ(Sp R, U) := (Sp R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t
  have hat : (Sp R).basicOpen a = (Sp R).basicOpen t := by
    rw [Scheme.basicOpen_res]; exact inf_eq_right.2 hle
  have e' : G.left.basicOpen (G.hom.appLE U V e a) ≤ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
    simp [Scheme.Hom.appLE]
  have h1 := appLE_basicOpen_isStandardSmooth G.hom hU hV e h a e'
  have h2 := res_top_isStandardSmooth (Sp R) t _ hat
  refine ⟨G.left.basicOpen (G.hom.appLE U V e a), r, hV.basicOpen _, hr, ?_, ?_⟩
  · have h3 : (G.hom.appLE ⊤ (G.left.basicOpen (G.hom.appLE U V e a)) (fun _ _ => trivial)).hom.IsStandardSmooth := by
      have := Scheme.Hom.map_appLE G.hom e' (homOfLE (le_top : (Sp R).basicOpen a ≤ ⊤)).op
      have e3 := congrArg CommRingCat.Hom.hom this
      rw [CommRingCat.hom_comp] at e3
      rw [← e3]
      exact h1.comp h2
    exact RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h3
  · intro y _
    have hz : (spMap (algebraMap R (Localization.Away r))) y ∈ (Sp R).basicOpen t := by
      rw [htr]
      have := PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      exact this.subset ⟨y, rfl⟩
    set z := (spMap (algebraMap R (Localization.Away r))) y with hzdef
    have hps : G.hom (s z) = z := by rw [← Scheme.Hom.comp_apply, hs]; rfl
    have h1 : s z ∈ V := hUs (hle hz)
    have h2 : s z ∈ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
      show G.hom (s z) ∈ (Sp R).basicOpen a
      rw [hps, hat]; exact hz
    show (spMap (algebraMap R (Localization.Away r)) ≫ s) y ∈ G.left.basicOpen (G.hom.appLE U V e a)
    rw [Scheme.Hom.comp_apply]
    show s z ∈ G.left.basicOpen (G.hom.appLE U V e a)
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro h1 h2

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
