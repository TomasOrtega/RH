import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Use `⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem exists_ringHom {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    (z : Sp B ⟶ X) (hr : Set.range z ⊆ Set.range x) : ∃ a : A →+* B, spMap a ≫ x = z := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Establish `h2` using `Spec.map_injective ((cancel_mono x).1 h)`. Conclude with `congrArg (fun g => g.hom) h2`.
-/
theorem ringHom_ext {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    {a b : A →+* B} (h : spMap a ≫ x = spMap b ≫ x) : a = b := by
  have h2 := Spec.map_injective ((cancel_mono x).1 h)
  exact congrArg (fun g => g.hom) h2

/- English proof (translation)
Establish `hU : IsAffineOpen x.opensRange` using `isAffineOpen_opensRange x`. Set `R₂ : Type` to `Γ(X, x.opensRange)`. Set `x₂ : Sp R₂ ⟶ X` to `hU.fromSpec`. Establish `: IsOpenImmersion x₂` using `inferInstanceAs (IsOpenImmersion hU.fromSpec)`. Establish `hrange : Set.range x₂ = Set.range x`.

Express the relevant statement in the definitionally equal form `Set.range hU.fromSpec = _`. Rewrite using `[hU.range_fromSpec]`. Both sides reduce to the same expression. Take `⟨φ, hφ⟩` from `exists_ringHom x x₂ hrange.le`. Take `⟨φ', hφ'⟩` from `exists_ringHom x₂ x hrange.ge`.

Establish `hcomp : φ.comp φ' = RingHom.id R₂` using `ringHom_ext x₂ (by`. Rewrite using `[spMap_comp, Category.assoc, hφ', hφ]`. Simplify using `[spMap])`. Set `g : R₂ →+* X.presheaf.stalk P` to `(X.presheaf.germ x.opensRange P hP).hom`. Establish `hg : spMap g ≫ x₂ = X.fromSpecStalk P`.

Rewrite using `[← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]`. Both sides reduce to the same expression. Establish `hgφ : g.comp φ = θ` using `ringHom_ext x (by`. Rewrite using `[spMap_comp, Category.assoc, hφ, hg, hθ])`. Establish `hgs : ∀ t, θ (φ' t) = g t` using `fun t => by`.

Rewrite using `[← hgφ]`. Conclude with `congrArg g (RingHom.congr_fun hcomp t)`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)`. Use `haveI := hU.isLocalization_stalk ⟨P, hP⟩`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a`.

Use `⟨φ' r, φ' s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hgs]`. Conclude with `IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s`. Rewrite using `[hgs, hgs]`. Conclude with `hrs`.
-/
theorem exists_frac {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] (P : X)
    (hP : P ∈ x.opensRange) (θ : R →+* X.presheaf.stalk P) (hθ : spMap θ ≫ x = X.fromSpecStalk P)
    (a : X.presheaf.stalk P) : ∃ r s : R, IsUnit (θ s) ∧ a * θ s = θ r := by
  have hU : IsAffineOpen x.opensRange := isAffineOpen_opensRange x
  let R₂ : Type := Γ(X, x.opensRange)
  let x₂ : Sp R₂ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₂ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range x₂ = Set.range x := by
    change Set.range hU.fromSpec = _
    rw [hU.range_fromSpec]
    rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom x x₂ hrange.le
  obtain ⟨φ', hφ'⟩ := exists_ringHom x₂ x hrange.ge
  have hcomp : φ.comp φ' = RingHom.id R₂ := ringHom_ext x₂ (by
    rw [spMap_comp, Category.assoc, hφ', hφ]
    simp [spMap])
  let g : R₂ →+* X.presheaf.stalk P := (X.presheaf.germ x.opensRange P hP).hom
  have hg : spMap g ≫ x₂ = X.fromSpecStalk P := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]
    rfl
  have hgφ : g.comp φ = θ := ringHom_ext x (by
    rw [spMap_comp, Category.assoc, hφ, hg, hθ])
  have hgs : ∀ t, θ (φ' t) = g t := fun t => by
    rw [← hgφ]
    exact congrArg g (RingHom.congr_fun hcomp t)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)
  haveI := hU.isLocalization_stalk ⟨P, hP⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a
  refine ⟨φ' r, φ' s, ?_, ?_⟩
  · rw [hgs]
    exact IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s
  · rw [hgs, hgs]
    exact hrs

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread

namespace GlobalTheory.CompanionTheory.Ar.LocFn

/- English proof (translation)
Introduce `X G _ _ _ P ι _ e f he`. Use `haveI := Fintype.ofFinite ι`. Take `⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩` from `LieVB.exists_chart G P`. Establish `hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange`. Rewrite using `[Scheme.fromSpecStalk_closedPoint]`.

Conclude with `hP`. Take `⟨θ₁, hθ₁⟩` from `LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'`. Take `⟨Fs, _, _, ⟨Ms⟩⟩` from `lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)`. Take `⟨β, B, hB, hβ⟩` from `LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b`. Use `choose s hs using fun i => Ms.onto (e i) (he i)`.

Set `c : ι → Fin n → X.presheaf.stalk P` to `fun i k => B.repr (s i) k`. Use `choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁`. Set `h : R₁` to `den f * ∏ i, ∏ k, den (c i k)`. Establish `hunit : IsUnit (θ₁ h)`. Simplify using `only [h, map_mul, map_prod]`.

Conclude with `(hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)`. Set `R : Type` to `Localization.Away h`. Set `θ : R →+* X.presheaf.stalk P` to `IsLocalization.Away.lift h hunit`. Establish `hθc : θ.comp (algebraMap R₁ R) = θ₁` using `IsLocalization.Away.lift_comp h hunit`. Set `x : Sp R ⟶ X` to `spMap (algebraMap R₁ R) ≫ x₁`.

Establish `hopen : IsOpenImmersion (spMap (algebraMap R₁ R))` using `inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))`. Establish `hx : IsOpenImmersion x` using `inferInstance`. Establish `hxθ : spMap θ ≫ x = X.fromSpecStalk P`. Express the relevant statement in the definitionally equal form `spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _`. Rewrite using `[← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]`.

Establish `hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a` using `fun a hd => by`. Establish `hu : IsUnit (algebraMap R₁ R (den a))` using `isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)`. Take `⟨u, hu⟩` from `hu`. Establish `hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a)` using `RingHom.congr_fun hθc _`. Use `⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩` and prove the remaining obligations.

Establish `h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1`. Rewrite using `[← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]`. Establish `h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a)` using `RingHom.congr_fun hθc _`. Rewrite using `[map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]`. Establish `hdvd : ∀ i k, den (c i k) ∣ h` using `fun i k => Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _`.

Use `choose c' hc' using fun i k => hlift (c i k) (hdvd i k)`. Take `⟨f', hf'⟩` from `hlift f (Dvd.intro _ rfl)`. Take `⟨F', _, _, ⟨MR⟩⟩` from `lieModel_exists X G R x`. Take `⟨β₁, B₁, hB₁, hβ₁⟩` from `LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b`. Take `⟨j, hj⟩` from `LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms`.

Establish `hjB : ∀ k, j (B₁ k) = B k` using `fun k => LieVB.pt_left_inj Ms (by`. Rewrite using `[hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])`. Use `⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf', fun i => MR.tan _, fun i => ?_⟩` and prove the remaining obligations. Use `⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hxθ]`.

Conclude with `Scheme.fromSpecStalk_closedPoint`. Establish `hsum : j (∑ k, c' i k • B₁ k) = s i`. Rewrite using `[map_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))` and prove the remaining obligations. Rewrite using `[j.map_smulₛₗ, hc', hjB]`.

Rewrite using `[← hj, hsum, hs]`.
-/
theorem exists_chart_spread : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  intro X G _ _ _ P ι _ e f he
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩ := LieVB.exists_chart G P
  have hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  obtain ⟨θ₁, hθ₁⟩ := LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'
  obtain ⟨Fs, _, _, ⟨Ms⟩⟩ := lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)
  obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b
  choose s hs using fun i => Ms.onto (e i) (he i)
  let c : ι → Fin n → X.presheaf.stalk P := fun i k => B.repr (s i) k
  choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁
  let h : R₁ := den f * ∏ i, ∏ k, den (c i k)
  have hunit : IsUnit (θ₁ h) := by
    simp only [h, map_mul, map_prod]
    exact (hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)
  let R : Type := Localization.Away h
  let θ : R →+* X.presheaf.stalk P := IsLocalization.Away.lift h hunit
  have hθc : θ.comp (algebraMap R₁ R) = θ₁ := IsLocalization.Away.lift_comp h hunit
  let x : Sp R ⟶ X := spMap (algebraMap R₁ R) ≫ x₁
  have hopen : IsOpenImmersion (spMap (algebraMap R₁ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))
  have hx : IsOpenImmersion x := inferInstance
  have hxθ : spMap θ ≫ x = X.fromSpecStalk P := by
    change spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _
    rw [← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]
  have hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a := fun a hd => by
    have hu : IsUnit (algebraMap R₁ R (den a)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)
    obtain ⟨u, hu⟩ := hu
    have hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a) := RingHom.congr_fun hθc _
    refine ⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩
    have h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1 := by
      rw [← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a) := RingHom.congr_fun hθc _
    rw [map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]
  have hdvd : ∀ i k, den (c i k) ∣ h := fun i k =>
    Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _
  choose c' hc' using fun i k => hlift (c i k) (hdvd i k)
  obtain ⟨f', hf'⟩ := hlift f (Dvd.intro _ rfl)
  obtain ⟨F', _, _, ⟨MR⟩⟩ := lieModel_exists X G R x
  obtain ⟨β₁, B₁, hB₁, hβ₁⟩ := LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms
  have hjB : ∀ k, j (B₁ k) = B k := fun k => LieVB.pt_left_inj Ms (by
    rw [hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])
  refine ⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf',
    fun i => MR.tan _, fun i => ?_⟩
  · refine ⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hxθ]
    exact Scheme.fromSpecStalk_closedPoint
  · have hsum : j (∑ k, c' i k • B₁ k) = s i := by
      rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))
      rw [j.map_smulₛₗ, hc', hjB]
    rw [← hj, hsum, hs]

end GlobalTheory.CompanionTheory.Ar.LocFn
