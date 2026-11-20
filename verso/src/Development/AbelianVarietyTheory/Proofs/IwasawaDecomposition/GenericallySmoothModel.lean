import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ModelCharts

/- English proof (translation)
Establish `hzr : z ∈ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hz`. Take `⟨z', rfl⟩` from `hzr`. Take `⟨U', x', hU', hzU', hx'⟩` from `GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'`.

Set `e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U')` to `(W.ι.appIso U').commRingCatIsoToRingEquiv`. Use `⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) = p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom` using `by first`. Consider the case `rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]`. Consider the case `(rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)`.

Consider the case `simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]`. Consider the case `(simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])`. Establish `halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U'))`. Unfold `ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX`. Rewrite using `[h2]`.

Both sides reduce to the same expression. Establish `heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[halg]`.

Introduce `i`. Simplify using the standard rewrite rules. Rewrite `hx'` using `[heq]`. Establish `h3` using `RingHom.Etale.respectsIso.left _ e.symm hx'`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `ext <;> simp`.
-/
theorem exists_etale_coords_of_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (D : ℕ)
    (W : X.Opens) [SmoothOfRelativeDimension D (W.ι ≫ p)] {z : X} (hz : z ∈ W) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have hzr : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨z', rfl⟩ := hzr
  obtain ⟨U', x', hU', hzU', hx'⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'
  let e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U') := (W.ι.appIso U').commRingCatIsoToRingEquiv
  refine ⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩
  have h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) =
      p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom := by
    first
    | rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    | (rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    | simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]
    | (simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])
  have halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX
    rw [h2]
    rfl
  have heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' =
      (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp
        (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [halg]
    · intro i; simp
  rw [heq] at hx'
  have h3 := RingHom.Etale.respectsIso.left _ e.symm hx'
  convert h3 using 1
  ext <;> simp

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `hI` using `Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hne (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)`. Take `⟨n, hn, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`.

Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero]`. Conclude with `hn0 hn`.
-/
theorem injective_emb {F : Type} [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hne (RingHom.mem_ker.2 hx)
    (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  exact hn0 hn

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Take `⟨a, ha⟩` from `y`. Take `⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ` from `⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩`. Establish `hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K)`. Rewrite using `[ha]`. Unfold `spMap`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]`. Take `⟨b, hb⟩ : ∃ b, b ≫ j = a` from `⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩`. Use `haveI : Flat (spMap (algebraMap R K)) := by`. Unfold `spMap`. Use `(HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_` and prove the remaining obligations.

Rewrite using `[CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]`. Conclude with `IsLocalization.flat K (nonZeroDivisors R)`. Use `haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by`. Unfold `spMap`. Use `(HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_` and prove the remaining obligations.

Rewrite using `[CommRingCat.hom_ofHom]`. Conclude with `RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K`. Take `⟨W, hW, hsm⟩` from `GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D (b (IsLocalRing.closedPoint ℂ))`. Use `haveI := hsm`. Establish `hz : a (IsLocalRing.closedPoint ℂ) ∈ W`.

Rewrite using `[← hb]`. Apply the tactic sequence `first | exact hW | simpa using hW`. Take `⟨U, x, hU, hzU, hx⟩` from `exists_etale_coords_of_opens p D W hz`. Take `⟨c, hc, -⟩` from `GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩) (GlobalTheory.CxPts.mem_ptsIn.2 hzU)`. Conclude with `⟨c, hc⟩`.
-/
private theorem exists_algChart_mem_source {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := by
  obtain ⟨a, ha⟩ := y
  obtain ⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ :=
    ⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩
  have hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K) := by
    rw [ha]; unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨b, hb⟩ : ∃ b, b ≫ j = a := ⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩
  haveI : Flat (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K
  obtain ⟨W, hW, hsm⟩ := GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D
    (b (IsLocalRing.closedPoint ℂ))
  haveI := hsm
  have hz : a (IsLocalRing.closedPoint ℂ) ∈ W := by
    rw [← hb]
    first | exact hW | simpa using hW
  obtain ⟨U, x, hU, hzU, hx⟩ := exists_etale_coords_of_opens p D W hz
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩)
    (GlobalTheory.CxPts.mem_ptsIn.2 hzU)
  exact ⟨c, hc⟩

/- English proof (translation)
The claim follows from `exists_algChart_mem_source h hτ y`.
-/
theorem exists_chart {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := exists_algChart_mem_source h hτ y

/- English proof (translation)
Introduce `F _ _ Y M σ`. Use `haveI : LocallyOfFinitePresentation M.p := by`. Take `⟨N, i, hi, hip⟩` from `(show ∃ N i, IsClosedImmersion i ∧ i ≫ PSpace.str (𝓞 F) N = M.p from M.ar.isProjOver)`. Rewrite using `[← hip]`. Use `haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 F) N`.

Use `first`. Consider the case `infer_instance`. Consider the case `exact (locallyOfFinitePresentation_iff_locallyOfFiniteType (f := i ≫ PSpace.str (𝓞 F) N)).2 inferInstance`. Conclude with `⟨{ ι := CxPts M.p σ chart := fun y => (exists_chart M.pb (injective_emb σ) y).choose cover := fun y => ⟨y, (exists_chart M.pb (injective_emb σ) y).choose_spec⟩ }⟩`.
-/
theorem genSmooth_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y),
    GenSmooth M.p Y.dim := by
  intro F _ _ Y M σ
  haveI : LocallyOfFinitePresentation M.p := by
    obtain ⟨N, i, hi, hip⟩ :=
      (show ∃ N i, IsClosedImmersion i ∧ i ≫ PSpace.str (𝓞 F) N = M.p from M.ar.isProjOver)
    rw [← hip]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 F) N
    first
    | infer_instance
    | exact (locallyOfFinitePresentation_iff_locallyOfFiniteType (f := i ≫ PSpace.str (𝓞 F) N)).2 inferInstance
  exact ⟨{ ι := CxPts M.p σ
           chart := fun y => (exists_chart M.pb (injective_emb σ) y).choose
           cover := fun y => ⟨y, (exists_chart M.pb (injective_emb σ) y).choose_spec⟩ }⟩

end GlobalTheory.ModelCharts
