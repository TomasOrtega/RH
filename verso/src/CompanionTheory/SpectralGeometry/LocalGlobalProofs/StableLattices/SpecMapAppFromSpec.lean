import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.TrivFlat

/- English proof (translation)
Establish `hZV : IsAffineOpen (i ⁻¹ᵁ V)` using `hV.preimage i`. Establish `key : Spec.map (i.app V) ≫ hV.fromSpec = hZV.fromSpec ≫ i`. Use `IsAffineOpen.SpecMap_appLE_fromSpec i hV hZV le_rfl` as an intermediate fact. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `this`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hr : Set.range z ⊆ Set.range hZV.fromSpec`. Rewrite using `[hZV.range_fromSpec]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `show i (z x) ∈ V`. Establish `e : i (z x) = hV.fromSpec ((Spec.map (CommRingCat.ofHom φ)) x)`. Rewrite using `[← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]`. Rewrite using `[e]`. Use `hV.range_fromSpec` as an intermediate fact.

Conclude with `(Set.ext_iff.1 this _).1 ⟨_, rfl⟩`. Set `w` to `IsOpenImmersion.lift hZV.fromSpec z hr`. Establish `hw : w ≫ hZV.fromSpec = z` using `IsOpenImmersion.lift_fac _ _ _`. Set `ψ` to `Spec.preimage w`. Establish `hψ : Spec.map ψ = w` using `Spec.map_preimage w`.

Establish `e : CommRingCat.ofHom φ = i.app V ≫ ψ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono hV.fromSpec, ← hz, Spec.map_comp, Category.assoc, key, hψ, ← Category.assoc, hw]`. Introduce `r hr'`. Establish `e'` using `congrArg (fun q => q.hom r) e`.

Simplify using `only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at e'`. Rewrite using `[RingHom.mem_ker, e', RingHom.mem_ker.1 hr', map_zero]`. Introduce `h`. Establish `hs` using `i.app_surjective V hV`. Set `ψ : Γ(Z, i ⁻¹ᵁ V) →+* D` to `(i.app V).hom.liftOfSurjective hs ⟨φ, h⟩`.

Establish `hψ : ψ.comp (i.app V).hom = φ` using `RingHom.liftOfRightInverse_comp _ _ _ _`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ hZV.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp, ← hψ]`. Both sides reduce to the same expression.
-/
theorem factor_iff {Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] {V : Y.Opens} (hV : IsAffineOpen V)
    (D : Type) [CommRing D] (φ : Γ(Y, V) →+* D) :
    (∃ z : Sp D ⟶ Z, z ≫ i = Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ↔
      RingHom.ker (i.app V).hom ≤ RingHom.ker φ := by
  have hZV : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
  have key : Spec.map (i.app V) ≫ hV.fromSpec = hZV.fromSpec ≫ i := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec i hV hZV le_rfl
    rw [Scheme.Hom.app_eq_appLE]
    exact this
  constructor
  · rintro ⟨z, hz⟩
    have hr : Set.range z ⊆ Set.range hZV.fromSpec := by
      rw [hZV.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      show i (z x) ∈ V
      have e : i (z x) = hV.fromSpec ((Spec.map (CommRingCat.ofHom φ)) x) := by
        rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
      rw [e]
      have := hV.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨_, rfl⟩
    let w := IsOpenImmersion.lift hZV.fromSpec z hr
    have hw : w ≫ hZV.fromSpec = z := IsOpenImmersion.lift_fac _ _ _
    let ψ := Spec.preimage w
    have hψ : Spec.map ψ = w := Spec.map_preimage w
    have e : CommRingCat.ofHom φ = i.app V ≫ ψ := by
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, ← hz, Spec.map_comp, Category.assoc, key, hψ, ← Category.assoc, hw]
    intro r hr'
    have e' := congrArg (fun q => q.hom r) e
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at e'
    rw [RingHom.mem_ker, e', RingHom.mem_ker.1 hr', map_zero]
  · intro h
    have hs := i.app_surjective V hV
    let ψ : Γ(Z, i ⁻¹ᵁ V) →+* D := (i.app V).hom.liftOfSurjective hs ⟨φ, h⟩
    have hψ : ψ.comp (i.app V).hom = φ := RingHom.liftOfRightInverse_comp _ _ _ _
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hZV.fromSpec, ?_⟩
    rw [Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp, ← hψ]
    rfl

/- English proof (translation)
Set `O` to `Localization.AtPrime p`. Establish `hmem : ∀ k, f k ∈ I.map (algebraMap C O)` using `fun k => hf ▸ Ideal.subset_span ⟨k, rfl⟩`. Use `choose x hx using fun k => (IsLocalization.mem_map_algebraMap_iff p.primeCompl O).1 (hmem k)`. Set `c : Fin g → C` to `fun k => ((x k).1 : C)`. Set `J : Ideal C` to `Ideal.span (Set.range c)`.

Establish `hJI : J ≤ I` using `Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (x k).1.2)`. Establish `hJO : I.map (algebraMap C O) ≤ J.map (algebraMap C O)`. Rewrite using `[← hf, Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hu : IsUnit (algebraMap C O ((x k).2 : C))` using `IsLocalization.map_units O (x k).2`.

Use `(Ideal.mul_unit_mem_iff_mem _ hu).1 ?_` and prove the remaining obligations. Rewrite using `[hx k]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, rfl⟩)`. Establish `key : ∀ a ∈ I, ∃ s, s ∉ p ∧ s * a ∈ J`. Introduce `a ha`.

Take `⟨⟨b, s⟩, hb⟩` from `(IsLocalization.mem_map_algebraMap_iff p.primeCompl O).1 (hJO (Ideal.mem_map_of_mem _ ha))`. Rewrite `hb` using `[← map_mul, IsLocalization.eq_iff_exists p.primeCompl O]`. Take `⟨t, ht⟩` from `hb`. Use `⟨t * s, (p.primeCompl.mul_mem t.2 s.2 : _), ?_⟩` and prove the remaining obligations. Establish `: ((t : C) * s) * a = t * b` using `by rw [← ht]; ring`.

Rewrite using `[this]`. Conclude with `J.mul_mem_left _ b.2`. Use `choose! s hsp hsJ using key`. Take `⟨G, hG⟩ : I.FG` from `IsNoetherian.noetherian I`. Set `h : C` to `∏ a ∈ G, s a`.

Establish `hGI : ∀ a ∈ G, a ∈ I` using `fun a ha => hG ▸ Ideal.subset_span ha`. Establish `hh : h ∉ p` using `(p.primeCompl.prod_mem fun a ha => hsp a (hGI a ha) : _)`. Establish `hI : ∀ a ∈ I, h * a ∈ J`. Introduce `a ha`. Rewrite `ha` using `[← hG]`.

Use `Submodule.span_induction (p := fun a _ => h * a ∈ J) ?_ ?_ ?_ ?_ ha` and prove the remaining obligations. Introduce `a ha`. Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem s ha`. Establish `: h * a = d * (s a * a)` using `by rw [show h = s a * d from hd]; ring`. Rewrite using `[this]`.

Conclude with `J.mul_mem_left _ (hsJ a (hGI a ha))`. Simplify using the standard rewrite rules. Introduce `u v _ _ hu hv`. Rewrite using `[mul_add]`. Conclude with `J.add_mem hu hv`.

Introduce `r u _ hu`. Establish `: h * r • u = r * (h * u)` using `by simp only [smul_eq_mul]; ring`. Rewrite using `[this]`. Conclude with `J.mul_mem_left _ hu`. Use `⟨h, hh, fun C' _ _ _ => ⟨fun k => algebraMap C C' (c k), ?_⟩⟩` and prove the remaining obligations.

Establish `e : Ideal.span (Set.range fun k => algebraMap C C' (c k)) = J.map (algebraMap C C')`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `le_antisymm (Ideal.map_mono hJI) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap C C' h)` using `IsLocalization.Away.algebraMap_isUnit h`. Use `Ideal.mem_comap.2 ((Ideal.unit_mul_mem_iff_mem _ hu).1 ?_)` and prove the remaining obligations. Rewrite using `[← map_mul]`. Conclude with `Ideal.mem_map_of_mem _ (hI a ha)`.
-/
theorem spread {C : Type} [CommRing C] [IsNoetherianRing C] (I p : Ideal C) [p.IsPrime] (g : ℕ)
    (f : Fin g → Localization.AtPrime p)
    (hf : Ideal.span (Set.range f) = I.map (algebraMap C (Localization.AtPrime p))) :
    ∃ h : C, h ∉ p ∧ ∀ (C' : Type) [CommRing C'] [Algebra C C'] [IsLocalization.Away h C'],
      ∃ f' : Fin g → C', Ideal.span (Set.range f') = I.map (algebraMap C C') := by
  classical
  let O := Localization.AtPrime p
  have hmem : ∀ k, f k ∈ I.map (algebraMap C O) := fun k => hf ▸ Ideal.subset_span ⟨k, rfl⟩
  choose x hx using fun k => (IsLocalization.mem_map_algebraMap_iff p.primeCompl O).1 (hmem k)
  let c : Fin g → C := fun k => ((x k).1 : C)
  let J : Ideal C := Ideal.span (Set.range c)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (x k).1.2)
  have hJO : I.map (algebraMap C O) ≤ J.map (algebraMap C O) := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have hu : IsUnit (algebraMap C O ((x k).2 : C)) := IsLocalization.map_units O (x k).2
    refine (Ideal.mul_unit_mem_iff_mem _ hu).1 ?_
    rw [hx k]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, rfl⟩)
  have key : ∀ a ∈ I, ∃ s, s ∉ p ∧ s * a ∈ J := by
    intro a ha
    obtain ⟨⟨b, s⟩, hb⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl O).1
      (hJO (Ideal.mem_map_of_mem _ ha))
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl O] at hb
    obtain ⟨t, ht⟩ := hb
    refine ⟨t * s, (p.primeCompl.mul_mem t.2 s.2 : _), ?_⟩
    have : ((t : C) * s) * a = t * b := by rw [← ht]; ring
    rw [this]
    exact J.mul_mem_left _ b.2
  choose! s hsp hsJ using key
  obtain ⟨G, hG⟩ : I.FG := IsNoetherian.noetherian I
  let h : C := ∏ a ∈ G, s a
  have hGI : ∀ a ∈ G, a ∈ I := fun a ha => hG ▸ Ideal.subset_span ha
  have hh : h ∉ p := (p.primeCompl.prod_mem fun a ha => hsp a (hGI a ha) : _)
  have hI : ∀ a ∈ I, h * a ∈ J := by
    intro a ha
    rw [← hG] at ha
    refine Submodule.span_induction (p := fun a _ => h * a ∈ J) ?_ ?_ ?_ ?_ ha
    · intro a ha
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem s ha
      have : h * a = d * (s a * a) := by rw [show h = s a * d from hd]; ring
      rw [this]
      exact J.mul_mem_left _ (hsJ a (hGI a ha))
    · simp
    · intro u v _ _ hu hv
      rw [mul_add]
      exact J.add_mem hu hv
    · intro r u _ hu
      have : h * r • u = r * (h * u) := by simp only [smul_eq_mul]; ring
      rw [this]
      exact J.mul_mem_left _ hu
  refine ⟨h, hh, fun C' _ _ _ => ⟨fun k => algebraMap C C' (c k), ?_⟩⟩
  have e : Ideal.span (Set.range fun k => algebraMap C C' (c k)) = J.map (algebraMap C C') := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [e]
  refine le_antisymm (Ideal.map_mono hJI) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  have hu : IsUnit (algebraMap C C' h) := IsLocalization.Away.algebraMap_isUnit h
  refine Ideal.mem_comap.2 ((Ideal.unit_mul_mem_iff_mem _ hu).1 ?_)
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (hI a ha)

/- English proof (translation)
Establish `ha` using `pull_isLB hL a`. Establish `hb` using `pull_isLB hL b`. Use `((cls_eq_zero_iff hb).symm.trans ?_).trans (cls_eq_zero_iff ha)` and prove the remaining obligations. Rewrite using `[cls_pull hL, cls_pull hL]`. Prove the components needed by the constructor for the conclusion.

Introduce `z`. Establish `: a = e.inv ≫ b` using `by rw [← h, Iso.inv_hom_id_assoc]`. Rewrite using `[this, pull_comp, z, map_zero]`. Introduce `z`. Rewrite using `[← h, pull_comp, z, map_zero]`.
-/
theorem triv_pull_iff {P Q X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (e : P ≅ Q) (a : Q ⟶ X) (b : P ⟶ X)
    (h : e.hom ≫ a = b) : Triv (L.pull b) ↔ Triv (L.pull a) := by
  have ha := pull_isLB hL a
  have hb := pull_isLB hL b
  refine ((cls_eq_zero_iff hb).symm.trans ?_).trans (cls_eq_zero_iff ha)
  rw [cls_pull hL, cls_pull hL]
  constructor
  · intro z
    have : a = e.inv ≫ b := by rw [← h, Iso.inv_hom_id_assoc]
    rw [this, pull_comp, z, map_zero]
  · intro z
    rw [← h, pull_comp, z, map_zero]

/- English proof (translation)
Use `letI : Algebra Γ(S, U) Γ(Y, V) := (s.appLE U V e).hom.toAlgebra`. Establish `hs' : Algebra.IsStandardSmoothOfRelativeDimension g Γ(S, U) Γ(Y, V)` using `hs.toAlgebra`. Use `letI : Algebra Γ(S, U) Γ(Z, i ⁻¹ᵁ V) := ((i ≫ s).appLE U (i ⁻¹ᵁ V) e').hom.toAlgebra`. Establish `hcomp : (i ≫ s).appLE U (i ⁻¹ᵁ V) e' = s.appLE U V e ≫ i.app V`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`.

Set `π : Γ(Y, V) →ₐ[Γ(S, U)] Γ(Z, i ⁻¹ᵁ V)` to `{ (i.app V).hom with commutes' := fun r => by`. Use `congrArg (fun q => q.hom r) hcomp` as an intermediate fact. Conclude with `this.symm }`. Establish `hπ : Function.Surjective π` using `i.app_surjective V hV`. Set `ε : (Γ(Y, V) ⧸ Ideal.span (Set.range f)) ≃ₐ[Γ(S, U)] Γ(Z, i ⁻¹ᵁ V)` to `(Ideal.quotientEquivAlgOfEq _ hf).trans (Ideal.quotientKerAlgEquivOfSurjective (f := π) hπ)`.

Establish `hq : Algebra.QuasiFinite Γ(S, U) Γ(Z, i ⁻¹ᵁ V)` using `RingHom.quasiFinite_algebraMap.1 (LocallyQuasiFinite.quasiFinite_appLE hU (hV.preimage i) e')`. Establish `hq'` using `(Algebra.QuasiFinite.iff_of_algEquiv ε).2 hq`. Establish `hfl` using `hCI Γ(S, U) Γ(Y, V) g hs' f hq'`. Conclude with `RingHom.flat_algebraMap_iff.2 (Module.Flat.of_linearEquiv ε.symm.toLinearEquiv)`.
-/
theorem flat_piece (hCI : CIFlat) {S Y Z : Scheme.{0}} (s : Y ⟶ S) (i : Z ⟶ Y) [IsClosedImmersion i]
    [LocallyQuasiFinite (i ≫ s)] {U : S.Opens} (hU : IsAffineOpen U) [IsNoetherianRing Γ(S, U)]
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ s ⁻¹ᵁ U) (e' : i ⁻¹ᵁ V ≤ (i ≫ s) ⁻¹ᵁ U) (g : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension g (s.appLE U V e).hom)
    (f : Fin g → Γ(Y, V)) (hf : Ideal.span (Set.range f) = RingHom.ker (i.app V).hom) :
    ((i ≫ s).appLE U (i ⁻¹ᵁ V) e').hom.Flat := by
  letI : Algebra Γ(S, U) Γ(Y, V) := (s.appLE U V e).hom.toAlgebra
  have hs' : Algebra.IsStandardSmoothOfRelativeDimension g Γ(S, U) Γ(Y, V) := hs.toAlgebra
  letI : Algebra Γ(S, U) Γ(Z, i ⁻¹ᵁ V) := ((i ≫ s).appLE U (i ⁻¹ᵁ V) e').hom.toAlgebra
  have hcomp : (i ≫ s).appLE U (i ⁻¹ᵁ V) e' = s.appLE U V e ≫ i.app V := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  let π : Γ(Y, V) →ₐ[Γ(S, U)] Γ(Z, i ⁻¹ᵁ V) :=
    { (i.app V).hom with
      commutes' := fun r => by
        have := congrArg (fun q => q.hom r) hcomp
        exact this.symm }
  have hπ : Function.Surjective π := i.app_surjective V hV
  let ε : (Γ(Y, V) ⧸ Ideal.span (Set.range f)) ≃ₐ[Γ(S, U)] Γ(Z, i ⁻¹ᵁ V) :=
    (Ideal.quotientEquivAlgOfEq _ hf).trans (Ideal.quotientKerAlgEquivOfSurjective (f := π) hπ)
  have hq : Algebra.QuasiFinite Γ(S, U) Γ(Z, i ⁻¹ᵁ V) :=
    RingHom.quasiFinite_algebraMap.1 (LocallyQuasiFinite.quasiFinite_appLE hU (hV.preimage i) e')
  have hq' := (Algebra.QuasiFinite.iff_of_algEquiv ε).2 hq
  have hfl := hCI Γ(S, U) Γ(Y, V) g hs' f hq'
  exact RingHom.flat_algebraMap_iff.2 (Module.Flat.of_linearEquiv ε.symm.toLinearEquiv)

/- English proof (translation)
Use `IsAffineOpen.SpecMap_appLE_fromSpec i hV hZV le_rfl` as an intermediate fact. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `this`.
-/
theorem SpecMap_app_fromSpec {Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] {V : Y.Opens}
    (hV : IsAffineOpen V) (hZV : IsAffineOpen (i ⁻¹ᵁ V)) :
    Spec.map (i.app V) ≫ hV.fromSpec = hZV.fromSpec ≫ i := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec i hV hZV le_rfl
  rw [Scheme.Hom.app_eq_appLE]
  exact this

/- English proof (translation)
Establish `hZV : IsAffineOpen (i ⁻¹ᵁ V)` using `hV.preimage i`. Set `q : Spec Γ(Z, i ⁻¹ᵁ V)` to `hZV.primeIdealOf ⟨z, hy⟩`. Establish `e : (hV.primeIdealOf ⟨i z, hy⟩ : Spec Γ(Y, V)) = Spec.map (i.app V) q`. Apply `hV.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Establish `e₁` using `hV.fromSpec_primeIdealOf ⟨i z, hy⟩`.

Establish `e₂` using `hZV.fromSpec_primeIdealOf ⟨z, hy⟩`. Establish `e₃ : hV.fromSpec (Spec.map (i.app V) q) = i (hZV.fromSpec q)` using `(Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun m : Spec Γ(Z, i ⁻¹ᵁ V) ⟶ Y => m q) (SpecMap_app_fromSpec i hV hZV)).trans (Scheme.Hom.comp_apply _ _ _))`. Use `e₁.trans (Eq.trans ?_ e₃.symm)` and prove the remaining obligations. Conclude with `congrArg i e₂.symm`. Introduce `r hr`.

Establish `e' : (hV.primeIdealOf ⟨i z, hy⟩).asIdeal = (hZV.primeIdealOf ⟨z, hy⟩).asIdeal.comap (i.app V).hom` using `congrArg PrimeSpectrum.asIdeal e`. Rewrite using `[e', Ideal.mem_comap, RingHom.mem_ker.1 hr]`. Conclude with `zero_mem _`.
-/
theorem ker_le_prime {Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] {V : Y.Opens} (hV : IsAffineOpen V)
    (z : Z) (hy : i z ∈ V) :
    RingHom.ker (i.app V).hom ≤ (hV.primeIdealOf ⟨i z, hy⟩).asIdeal := by
  have hZV : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
  let q : Spec Γ(Z, i ⁻¹ᵁ V) := hZV.primeIdealOf ⟨z, hy⟩
  have e : (hV.primeIdealOf ⟨i z, hy⟩ : Spec Γ(Y, V)) = Spec.map (i.app V) q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    have e₁ := hV.fromSpec_primeIdealOf ⟨i z, hy⟩
    have e₂ := hZV.fromSpec_primeIdealOf ⟨z, hy⟩
    have e₃ : hV.fromSpec (Spec.map (i.app V) q) = i (hZV.fromSpec q) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun m : Spec Γ(Z, i ⁻¹ᵁ V) ⟶ Y => m q) (SpecMap_app_fromSpec i hV hZV)).trans
          (Scheme.Hom.comp_apply _ _ _))
    refine e₁.trans (Eq.trans ?_ e₃.symm)
    exact congrArg i e₂.symm
  intro r hr
  have e' : (hV.primeIdealOf ⟨i z, hy⟩).asIdeal = (hZV.primeIdealOf ⟨z, hy⟩).asIdeal.comap (i.app V).hom :=
    congrArg PrimeSpectrum.asIdeal e
  rw [e', Ideal.mem_comap, RingHom.mem_ker.1 hr]
  exact zero_mem _

/- English proof (translation)
Use `(HasRingHomProperty.iff_exists_appLE (P := @Flat) (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway RingHom.Flat.holdsForLocalizationAway).1).2 fun z => ?_` and prove the remaining obligations. Take `⟨U, hU, V, hV, hy, e, hs⟩` from `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := g) (f := s) (i z)`. Use `haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Use `haveI : IsNoetherianRing Γ(Y, V) := by`. Use `letI := (s.appLE U V e).hom.toAlgebra`.

Establish `h1 : Algebra.IsStandardSmoothOfRelativeDimension g Γ(S, U) Γ(Y, V)` using `hs.toAlgebra`. Establish `h2 : Algebra.IsStandardSmooth Γ(S, U) Γ(Y, V)` using `h1.isStandardSmooth`. Establish `h3 : Algebra.FiniteType Γ(S, U) Γ(Y, V)` using `inferInstance`. Conclude with `Algebra.FiniteType.isNoetherianRing Γ(S, U) _`. Set `P` to `hV.primeIdealOf ⟨i z, hy⟩`.

Set `p` to `P.asIdeal`. Use `haveI : p.IsPrime := P.isPrime`. Establish `hI : RingHom.ker (i.app V).hom ≤ p` using `ker_le_prime i hV z hy`. Use `haveI : IsNoetherianRing (Localization.AtPrime p) := IsLocalization.isNoetherianRing p.primeCompl _ ‹_›`. Establish `hne : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) (Localization.AtPrime p)) ≠ ⊤`.

Introduce `ht`. Establish `hle : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) (Localization.AtPrime p)) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p)`. Conclude with `Ideal.map_le_iff_le_comap.2 fun r hr => (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p r).2 (hI hr)`. Rewrite `hle` using `[ht]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)`.

Take `⟨f, hf⟩` from `H V hV (Localization.AtPrime p) (algebraMap _ _) hne`. Take `⟨h, hp, hh⟩` from `spread (RingHom.ker (i.app V).hom) p g f hf`. Use `haveI := hV.isLocalization_basicOpen h`. Take `⟨f', hf'⟩` from `hh Γ(Y, Y.basicOpen h)`. Establish `hV'` using `hV.basicOpen h`.

Establish `hker : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h)) = RingHom.ker (i.app (Y.basicOpen h)).hom`. Establish `e₁` using `i.ker.map_ideal_basicOpen ⟨V, hV⟩ h`. Rewrite `e₁` using `[Scheme.Hom.ker_apply]`. Conclude with `e₁.trans (i.ker_apply (Y.affineBasicOpen (U := ⟨V, hV⟩) h))`. Establish `e₁ : Y.basicOpen h ≤ s ⁻¹ᵁ U` using `(Y.basicOpen_le h).trans e`.

Establish `hs' : RingHom.IsStandardSmoothOfRelativeDimension g (s.appLE U (Y.basicOpen h) e₁).hom`. Establish `e₂ : s.appLE U (Y.basicOpen h) e₁ = s.appLE U V e ≫ CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h))` using `(Scheme.Hom.appLE_map s e (homOfLE (Y.basicOpen_le h)).op).symm`. Rewrite using `[e₂]`. Establish `h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h))` using `RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway h`. Simplify using `using h0.comp hs`.

Establish `hmem : i z ∈ Y.basicOpen h`. Establish `e₃ : P ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen h`. Rewrite using `[hV.fromSpec_preimage_basicOpen]`. Conclude with `hp`. Establish `e₄ : hV.fromSpec P ∈ Y.basicOpen h` using `e₃`.

Rewrite `e₄` using `[hV.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Establish `e₂ : i ⁻¹ᵁ Y.basicOpen h ≤ (i ≫ s) ⁻¹ᵁ U` using `fun x hx => e₁ hx`. Conclude with `⟨⟨U, hU⟩, ⟨i ⁻¹ᵁ Y.basicOpen h, hV'.preimage i⟩, hmem, e₂, flat_piece hCI s i hU hV' e₁ e₂ g hs' f' (hf'.trans hker)⟩`.
-/
theorem flat_of_gens (hCI : CIFlat) {S Y Z : Scheme.{0}} [IsLocallyNoetherian S] (s : Y ⟶ S) (i : Z ⟶ Y)
    [IsClosedImmersion i] (g : ℕ) [SmoothOfRelativeDimension g s] [LocallyQuasiFinite (i ≫ s)]
    (H : ∀ (V : Y.Opens), IsAffineOpen V → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
      (φ : Γ(Y, V) →+* O), (RingHom.ker (i.app V).hom).map φ ≠ ⊤ →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (RingHom.ker (i.app V).hom).map φ) : Flat (i ≫ s) := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1).2 fun z => ?_
  obtain ⟨U, hU, V, hV, hy, e, hs⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := g) (f := s) (i z)
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsNoetherianRing Γ(Y, V) := by
    letI := (s.appLE U V e).hom.toAlgebra
    have h1 : Algebra.IsStandardSmoothOfRelativeDimension g Γ(S, U) Γ(Y, V) := hs.toAlgebra
    have h2 : Algebra.IsStandardSmooth Γ(S, U) Γ(Y, V) := h1.isStandardSmooth
    have h3 : Algebra.FiniteType Γ(S, U) Γ(Y, V) := inferInstance
    exact Algebra.FiniteType.isNoetherianRing Γ(S, U) _
  let P := hV.primeIdealOf ⟨i z, hy⟩
  let p := P.asIdeal
  haveI : p.IsPrime := P.isPrime
  have hI : RingHom.ker (i.app V).hom ≤ p := ker_le_prime i hV z hy
  haveI : IsNoetherianRing (Localization.AtPrime p) := IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  have hne : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) (Localization.AtPrime p)) ≠ ⊤ := by
    intro ht
    have hle : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) (Localization.AtPrime p)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      exact Ideal.map_le_iff_le_comap.2 fun r hr =>
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p r).2 (hI hr)
    rw [ht] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
  obtain ⟨f, hf⟩ := H V hV (Localization.AtPrime p) (algebraMap _ _) hne
  obtain ⟨h, hp, hh⟩ := spread (RingHom.ker (i.app V).hom) p g f hf
  haveI := hV.isLocalization_basicOpen h
  obtain ⟨f', hf'⟩ := hh Γ(Y, Y.basicOpen h)
  have hV' := hV.basicOpen h
  have hker : (RingHom.ker (i.app V).hom).map (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h)) =
      RingHom.ker (i.app (Y.basicOpen h)).hom := by
    have e₁ := i.ker.map_ideal_basicOpen ⟨V, hV⟩ h
    rw [Scheme.Hom.ker_apply] at e₁
    exact e₁.trans (i.ker_apply (Y.affineBasicOpen (U := ⟨V, hV⟩) h))
  have e₁ : Y.basicOpen h ≤ s ⁻¹ᵁ U := (Y.basicOpen_le h).trans e
  have hs' : RingHom.IsStandardSmoothOfRelativeDimension g (s.appLE U (Y.basicOpen h) e₁).hom := by
    have e₂ : s.appLE U (Y.basicOpen h) e₁ =
        s.appLE U V e ≫ CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h)) :=
      (Scheme.Hom.appLE_map s e (homOfLE (Y.basicOpen_le h)).op).symm
    rw [e₂]
    have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen h)) :=
      RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway h
    simpa using h0.comp hs
  have hmem : i z ∈ Y.basicOpen h := by
    have e₃ : P ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen h := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hp
    have e₄ : hV.fromSpec P ∈ Y.basicOpen h := e₃
    rwa [hV.fromSpec_primeIdealOf] at e₄
  have e₂ : i ⁻¹ᵁ Y.basicOpen h ≤ (i ≫ s) ⁻¹ᵁ U := fun x hx => e₁ hx
  exact ⟨⟨U, hU⟩, ⟨i ⁻¹ᵁ Y.basicOpen h, hV'.preimage i⟩, hmem, e₂,
    flat_piece hCI s i hU hV' e₁ e₂ g hs' f' (hf'.trans hker)⟩

/- English proof (translation)
Establish `ha` using `pull_isLB hL a`. Use `(cls_eq_zero_iff (pull_isLB ha b)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB hL (b ≫ a))))` and prove the remaining obligations. Rewrite using `[cls_pull ha, cls_pull hL, cls_pull hL, pull_comp]`.
-/
theorem triv_pull_pull {P Q X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Q ⟶ X) (b : P ⟶ Q) :
    Triv ((L.pull a).pull b) ↔ Triv (L.pull (b ≫ a)) := by
  have ha := pull_isLB hL a
  refine (cls_eq_zero_iff (pull_isLB ha b)).symm.trans (Iff.trans ?_ (cls_eq_zero_iff (pull_isLB hL (b ≫ a))))
  rw [cls_pull ha, cls_pull hL, cls_pull hL, pull_comp]

/- English proof (translation)
Use `haveI : IsClosedImmersion i.left := hi.1`. Set `t : Sp O ⟶ Y.left` to `spMap φ ≫ hV.fromSpec`. Set `τ : Sp O ⟶ S` to `t ≫ Y.hom`. Establish `hG` using `isGrpPullback_pullback A τ`. Establish `habO` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG`.

Establish `hsmO : SmoothOfRelativeDimension g ((Over.pullback τ).obj A).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hG.1 hsm`. Set `m : ((Over.pullback τ).obj A).left ⟶ (A ⊗ Y).left` to `pullback.lift (pullback.fst A.hom τ) (pullback.snd A.hom τ ≫ t) (by`. Rewrite using `[pullback.condition, Category.assoc])`. Use `hF O ((Over.pullback τ).obj A) g habO hsmO (N.pull m) (pull_isLB hN m) _ hne fun J => ?_` and prove the remaining obligations. Set `T : Over S` to `Over.mk (spMap (Ideal.Quotient.mk J) ≫ τ)`.

Set `yJ : T ⟶ Y` to `Over.homMk (spMap (Ideal.Quotient.mk J) ≫ t) (by simp [T, τ])`. Establish `hpb` using `(IsPullback.of_hasPullback ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J))).paste_horiz hG.1`. Set `l` to `(lift (fst A T) (snd A T ≫ yJ)).left`. Establish `hl : hpb.isoPullback.hom ≫ l = pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫ m`. Establish `l₁ : l ≫ (fst A Y).left = (fst A T).left`.

Rewrite using `[← Over.comp_left, lift_fst]`. Establish `l₂ : l ≫ (snd A Y).left = (snd A T).left ≫ yJ.left`. Rewrite using `[← Over.comp_left, lift_snd, Over.comp_left]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `(Category.assoc _ _ _).trans ((congrArg _ l₁).trans ?_)` and prove the remaining obligations.

Use `hpb.isoPullback_hom_fst.trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `congrArg _ (pullback.lift_fst _ _ _).symm`. Use `(Category.assoc _ _ _).trans ((congrArg _ l₂).trans ?_)` and prove the remaining obligations. Establish `c` using `pullback.condition (f := ((Over.pullback τ).obj A).hom) (g := spMap (Ideal.Quotient.mk J))`.

Establish `h₁ : (pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫ m) ≫ pullback.snd A.hom Y.hom = (pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫ ((Over.pullback τ).obj A).hom) ≫ t`. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `congrArg _ (pullback.lift_snd _ _ _)`. Use `Eq.trans ?_ h₁.symm` and prove the remaining obligations. Rewrite using `[c, Category.assoc]`.

Conclude with `hpb.isoPullback_hom_snd_assoc _`. Use `(triv_pull_pull hN _ _).trans ((triv_pull_iff hN hpb.isoPullback l _ hl).symm.symm.trans ?_)` and prove the remaining obligations. Use `(hi.2 T yJ).trans ?_` and prove the remaining obligations. Establish `hq` using `factor_iff i.left hV (O ⧸ J) ((Ideal.Quotient.mk J).comp φ)`. Establish `e : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp φ)) ≫ hV.fromSpec = spMap (Ideal.Quotient.mk J) ≫ t`.

Simplify using `only [t, spMap, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `Ideal.map_le_iff_le_comap.2 fun r hr => ?_` and prove the remaining obligations.

Conclude with `Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 (RingHom.mem_ker.1 (hq.1 ⟨z.left, (congrArg (fun q => q.left) hz).trans e.symm⟩ hr)))`. Introduce `hJ`. Take `⟨z, hz⟩` from `hq.2 fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ hr))`. Establish `hz' : z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ t` using `hz.trans e`. Use `⟨Over.homMk z ?_, Over.OverMorphism.ext hz'⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem few_gens (hF : FewEquations) {S : Scheme.{0}} (A Y Z : Over S) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hsm : SmoothOfRelativeDimension g A.hom) (N : LB (A ⊗ Y).left) (hN : N.IsLB) (i : Z ⟶ Y)
    (hi : IsTrivLocus A N i) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (φ : Γ(Y.left, V) →+* O)
    (hne : (RingHom.ker (i.left.app V).hom).map φ ≠ ⊤) :
    ∃ f : Fin g → O, Ideal.span (Set.range f) = (RingHom.ker (i.left.app V).hom).map φ := by
  haveI : IsClosedImmersion i.left := hi.1
  let t : Sp O ⟶ Y.left := spMap φ ≫ hV.fromSpec
  let τ : Sp O ⟶ S := t ≫ Y.hom
  have hG := isGrpPullback_pullback A τ
  have habO := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG
  have hsmO : SmoothOfRelativeDimension g ((Over.pullback τ).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hG.1 hsm
  let m : ((Over.pullback τ).obj A).left ⟶ (A ⊗ Y).left :=
    pullback.lift (pullback.fst A.hom τ) (pullback.snd A.hom τ ≫ t) (by
      rw [pullback.condition, Category.assoc])
  refine hF O ((Over.pullback τ).obj A) g habO hsmO (N.pull m) (pull_isLB hN m) _ hne fun J => ?_
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk J) ≫ τ)
  let yJ : T ⟶ Y := Over.homMk (spMap (Ideal.Quotient.mk J) ≫ t) (by simp [T, τ])
  have hpb := (IsPullback.of_hasPullback ((Over.pullback τ).obj A).hom
    (spMap (Ideal.Quotient.mk J))).paste_horiz hG.1
  let l := (lift (fst A T) (snd A T ≫ yJ)).left
  have hl : hpb.isoPullback.hom ≫ l = pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫ m := by
    have l₁ : l ≫ (fst A Y).left = (fst A T).left := by
      rw [← Over.comp_left, lift_fst]
    have l₂ : l ≫ (snd A Y).left = (snd A T).left ≫ yJ.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg _ l₁).trans ?_)
      refine hpb.isoPullback_hom_fst.trans ?_
      rw [Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg _ l₂).trans ?_)
      have c := pullback.condition (f := ((Over.pullback τ).obj A).hom) (g := spMap (Ideal.Quotient.mk J))
      have h₁ : (pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫ m) ≫
          pullback.snd A.hom Y.hom = (pullback.fst ((Over.pullback τ).obj A).hom (spMap (Ideal.Quotient.mk J)) ≫
            ((Over.pullback τ).obj A).hom) ≫ t := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (pullback.lift_snd _ _ _)
      refine Eq.trans ?_ h₁.symm
      rw [c, Category.assoc]
      exact hpb.isoPullback_hom_snd_assoc _
  refine (triv_pull_pull hN _ _).trans ((triv_pull_iff hN hpb.isoPullback l _ hl).symm.symm.trans ?_)
  refine (hi.2 T yJ).trans ?_
  have hq := factor_iff i.left hV (O ⧸ J) ((Ideal.Quotient.mk J).comp φ)
  have e : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp φ)) ≫ hV.fromSpec =
      spMap (Ideal.Quotient.mk J) ≫ t := by
    simp only [t, spMap, ← Category.assoc, ← Spec.map_comp]
    rfl
  constructor
  · rintro ⟨z, hz⟩
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    exact Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1
      (RingHom.mem_ker.1 (hq.1 ⟨z.left, (congrArg (fun q => q.left) hz).trans e.symm⟩ hr)))
  · intro hJ
    obtain ⟨z, hz⟩ := hq.2 fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ hr))
    have hz' : z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ t := hz.trans e
    refine ⟨Over.homMk z ?_, Over.OverMorphism.ext hz'⟩
    calc z ≫ Z.hom = z ≫ i.left ≫ Y.hom := by rw [Over.w]
      _ = (spMap (Ideal.Quotient.mk J) ≫ t) ≫ Y.hom := by rw [← Category.assoc, hz']
      _ = T.hom := by simp [T, τ]

/- English proof (translation)
Introduce `hF hCI S _ A Y Z _ g hab hsmA hsmY N hN i hi hqf`. Use `haveI : IsClosedImmersion i.left := hi.1`. Establish `e : i.left ≫ Y.hom = Z.hom` using `Over.w i`. Use `haveI : LocallyQuasiFinite (i.left ≫ Y.hom) := e ▸ hqf`. Establish `h` using `flat_of_gens hCI Y.hom i.left g (fun V hV O _ _ _ φ hne => few_gens hF A Y Z g hab hsmA N hN i hi hV O φ hne)`.

Conclude with `e ▸ h`.
-/
theorem trivLocusFlat : FewEquations → CIFlat → TrivLocusFlat := by
  intro hF hCI S _ A Y Z _ g hab hsmA hsmY N hN i hi hqf
  haveI : IsClosedImmersion i.left := hi.1
  have e : i.left ≫ Y.hom = Z.hom := Over.w i
  haveI : LocallyQuasiFinite (i.left ≫ Y.hom) := e ▸ hqf
  have h := flat_of_gens hCI Y.hom i.left g
    (fun V hV O _ _ _ φ hne => few_gens hF A Y Z g hab hsmA N hN i hi hV O φ hne)
  exact e ▸ h

end GlobalTheory.CompanionTheory.TrivFlat
