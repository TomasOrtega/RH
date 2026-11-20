import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleApprox

/- English proof (translation)
Establish `e' : LBIso L' (L.pull (𝟙 _))` using `e.chartPull (chartPullId _) (Geo.Tor.chartPullPull L _ _ rfl)`. Conclude with `GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 S) (φ := 𝟙 A.left) (IsPullback.of_horiz_isIso ⟨by simp⟩) hL hL' e' hA`.
-/
theorem relAmple_of_lbIso_self {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L L' : LB A.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' L) (hA : Out.RelAmple A L) : Out.RelAmple A L' := by
  have e' : LBIso L' (L.pull (𝟙 _)) := e.chartPull (chartPullId _) (Geo.Tor.chartPullPull L _ _ rfl)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 S) (φ := 𝟙 A.left)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hL hL' e' hA

variable {R : Type} [CommRing R] {R₁ : Subring R} [IsNoetherianRing R₁] {A₀ : Over (Sp R₁)} [IsProper A₀.hom]
  [Flat A₀.hom] {M : LB A₀.left} {B : Over (Sp R)} {φ : B.left ⟶ A₀.left} {N : LB B.left}

/- English proof (translation)
Set `k` to `x.asIdeal.ResidueField`. Set `xr : R₁ →+* k` to `(algebraMap R k).comp R₁.subtype`. Set `p : Ideal R₁` to `RingHom.ker xr`. Establish `: p.IsPrime` using `RingHom.ker_isPrime xr`. Set `g` to `algebraMap R₁ p.ResidueField`.

Set `i : p.ResidueField →+* k` to `Ideal.ResidueField.lift p xr le_rfl fun a ha => IsUnit.mk0 _ ha`. Establish `hi : i.comp g = xr` using `RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p xr le_rfl (fun a ha => IsUnit.mk0 _ ha) a`. Establish `hu : spMap (algebraMap R k) ≫ spMap R₁.subtype = spMap i ≫ spMap g`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]`. Establish `h₂` using `IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)`.

Establish `hfib : Out.RelAmple ((Over.pullback (spMap g)).obj A₀) (M.pull (pullback.fst A₀.hom (spMap g)))` using `FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂ (LB.isLB_pull hM _) (GlobalTheory.lbIso_refl (LB.isLB_pull hM _)) (FibreAmple.relAmple_of_factor hM hφ h₂ _ hu hN e hB)`. Take `⟨r, hr, hA⟩` from `GlobalTheory.ProperFinite.relAmple_near_fibre A₀ hM g (FibreAmple.residueField_fraction p) hfib`. Use `⟨r, fun hx => hr (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 ?_)), hA⟩` and prove the remaining obligations. Conclude with `Ideal.algebraMap_residueField_eq_zero.2 hx`.
-/
theorem exists_basicOpen (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) (x : PrimeSpectrum R) :
    ∃ r : R₁, (r : R) ∉ x.asIdeal ∧
      Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r))).obj A₀)
        (M.pull (pullback.fst A₀.hom (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r)))) := by
  let k := x.asIdeal.ResidueField
  let xr : R₁ →+* k := (algebraMap R k).comp R₁.subtype
  let p : Ideal R₁ := RingHom.ker xr
  have : p.IsPrime := RingHom.ker_isPrime xr
  let g := algebraMap R₁ p.ResidueField
  let i : p.ResidueField →+* k := Ideal.ResidueField.lift p xr le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = xr := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p xr le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (algebraMap R k) ≫ spMap R₁.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  have hfib : Out.RelAmple ((Over.pullback (spMap g)).obj A₀) (M.pull (pullback.fst A₀.hom (spMap g))) :=
    FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hM _) (GlobalTheory.lbIso_refl (LB.isLB_pull hM _))
      (FibreAmple.relAmple_of_factor hM hφ h₂ _ hu hN e hB)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre A₀ hM g (FibreAmple.residueField_fraction p) hfib
  refine ⟨r, fun hx => hr (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 ?_)), hA⟩
  exact Ideal.algebraMap_residueField_eq_zero.2 hx

/- English proof (translation)
Use `choose r hr hA using exists_basicOpen hM hφ hN e hB`. Establish `hspan : Ideal.span (Set.range fun x => (r x : R)) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Conclude with `hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))`.

Establish `h1 : (1 : R) ∈ Submodule.span R (Set.range fun x => (r x : R))`. Express the relevant statement in the definitionally equal form `(1 : R) ∈ Ideal.span _`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 h1`.

Use `⟨c.support.image c, fun R₂ h hF B₂ π hπ => ?_⟩` and prove the remaining obligations. Establish `hcR : ∀ x ∈ c.support, c x ∈ R₂` using `fun x hx => hF (Finset.mem_image_of_mem c hx)`. Establish `: IsProper B₂.hom` using `MorphismProperty.of_isPullback (P := @IsProper) hπ ‹_›`. Use `GlobalTheory.AmpleLocal.relAmple_of_locally _ B₂ (M.pull π) (pull_isLB hM π) inferInstance inferInstance fun s => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨x, -, hxs⟩ : ∃ x ∈ c.support, Subring.inclusion h (r x) ∉ (s : PrimeSpectrum R₂).asIdeal := by`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `key : (∑ y ∈ c.support.attach, (⟨c y, hcR y y.2⟩ : R₂) * Subring.inclusion h (r y)) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one, ← hc, Finsupp.sum]`.

Conclude with `Finset.sum_attach c.support (fun y => c y • (r y : R))`. Apply `(s : PrimeSpectrum R₂).isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← key]`. Conclude with `Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _ (hne y y.2)`. Set `D : (Sp R₁).Opens` to `PrimeSpectrum.basicOpen (r x)`.

Set `U : (Sp R₂).Opens` to `PrimeSpectrum.basicOpen (Subring.inclusion h (r x))`. Use `⟨U, hxs, ?_⟩` and prove the remaining obligations. Establish `sq : IsPullback ((B₂.hom ⁻¹ᵁ U).ι ≫ π) (B₂.hom ∣_ U) A₀.hom (U.ι ≫ spMap (Subring.inclusion h))` using `(isPullback_morphismRestrict B₂.hom U).flip.paste_horiz hπ`. Establish `hrange : Set.range (U.ι ≫ spMap (Subring.inclusion h)) ⊆ Set.range D.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨z, rfl⟩`. Establish `hz : U.ι z ∈ (U : Set (Sp R₂))` using `by first`. Consider the case `exact (Scheme.Opens.range_ι U) ▸ ⟨z, rfl⟩`. Consider the case `(rw [← Scheme.Opens.range_ι U]; exact ⟨z, rfl⟩)`. Consider the case `exact z.2`.

Conclude with `hz`. Establish `hA'` using `FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₀.hom D.ι) sq (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hM _) (GlobalTheory.lbIso_refl (LB.isLB_pull hM _)) (hA x)`. Establish `: IsProper (Over.mk (B₂.hom ∣_ U)).hom` using `inferInstanceAs (IsProper (B₂.hom ∣_ _))`. Conclude with `relAmple_of_lbIso_self (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (FibreAmple.lbIso_pull_pull hM _ _) hA'`.
-/
theorem relAmple_spread_subring (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) :
    ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (B₂ : Over (Sp R₂))
      (π : B₂.left ⟶ A₀.left), IsPullback π B₂.hom A₀.hom (spMap (Subring.inclusion h)) →
        Out.RelAmple B₂ (M.pull π) := by
  classical
  choose r hr hA using exists_basicOpen hM hφ hN e hB
  have hspan : Ideal.span (Set.range fun x => (r x : R)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range fun x => (r x : R)) := by
    change (1 : R) ∈ Ideal.span _
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨c.support.image c, fun R₂ h hF B₂ π hπ => ?_⟩
  have hcR : ∀ x ∈ c.support, c x ∈ R₂ := fun x hx => hF (Finset.mem_image_of_mem c hx)
  have : IsProper B₂.hom := MorphismProperty.of_isPullback (P := @IsProper) hπ ‹_›
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ B₂ (M.pull π) (pull_isLB hM π) inferInstance inferInstance
    fun s => ?_
  obtain ⟨x, -, hxs⟩ : ∃ x ∈ c.support, Subring.inclusion h (r x) ∉ (s : PrimeSpectrum R₂).asIdeal := by
    by_contra hne
    push_neg at hne
    have key : (∑ y ∈ c.support.attach, (⟨c y, hcR y y.2⟩ : R₂) * Subring.inclusion h (r y)) = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one, ← hc, Finsupp.sum]
      exact Finset.sum_attach c.support (fun y => c y • (r y : R))
    apply (s : PrimeSpectrum R₂).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← key]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _ (hne y y.2)
  let D : (Sp R₁).Opens := PrimeSpectrum.basicOpen (r x)
  let U : (Sp R₂).Opens := PrimeSpectrum.basicOpen (Subring.inclusion h (r x))
  refine ⟨U, hxs, ?_⟩
  have sq : IsPullback ((B₂.hom ⁻¹ᵁ U).ι ≫ π) (B₂.hom ∣_ U) A₀.hom (U.ι ≫ spMap (Subring.inclusion h)) :=
    (isPullback_morphismRestrict B₂.hom U).flip.paste_horiz hπ
  have hrange : Set.range (U.ι ≫ spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : U.ι z ∈ (U : Set (Sp R₂)) := by
      first
        | exact (Scheme.Opens.range_ι U) ▸ ⟨z, rfl⟩
        | (rw [← Scheme.Opens.range_ι U]; exact ⟨z, rfl⟩)
        | exact z.2
    exact hz
  have hA' := FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₀.hom D.ι) sq
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hM _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hM _)) (hA x)
  have : IsProper (Over.mk (B₂.hom ∣_ U)).hom := inferInstanceAs (IsProper (B₂.hom ∣_ _))
  exact relAmple_of_lbIso_self (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)
    (FibreAmple.lbIso_pull_pull hM _ _) hA'

end GlobalTheory.AmpleApprox
