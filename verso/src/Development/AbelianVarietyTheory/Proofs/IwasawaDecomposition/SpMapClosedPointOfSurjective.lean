import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcIntegral

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]`. Both sides reduce to the same expression.
-/
theorem ev_factor {Z : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z₁ : Sp A ⟶ Z) (z₂ : Sp B ⟶ Z)
    (e : z₂ = spMap φ ≫ z₁) (W : Z.Opens) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W) (f : Γ(Z, W)) :
    ev z₂ W h₂ f = φ (ev z₁ W h₁ f) := by
  subst e
  rw [GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]
  rfl

/- English proof (translation)
Distinguish the cases in `h : x.asIdeal = ⊥`. Use `Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)`. Use `Or.inr (PrimeSpectrum.ext ?_)` and prove the remaining obligations.

Conclude with `IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)`.
-/
theorem point_cases (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Sp R) :
    (∃ p : Sp K, spMap (algebraMap R K) p = x) ∨ x = IsLocalRing.closedPoint R := by
  by_cases h : x.asIdeal = ⊥
  · refine Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · refine Or.inr (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)

/- English proof (translation)
The claim follows from `IsLocalRing.comap_closedPoint f`.
-/
theorem spMap_closedPoint {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  IsLocalRing.comap_closedPoint f

/- English proof (translation)
The claim follows from `haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))`.
-/
theorem spMap_closedPoint_of_surjective {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))

/- English proof (translation)
Use `letI := g.toAlgebra`. Use `haveI : Module.Finite A B := hg`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' A B`. Use `(Cardinal.mk_le_of_surjective hf).trans ?_` and prove the remaining obligations. Rewrite using `[show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]`.

Conclude with `(pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)`.
-/
theorem mk_le_continuum_of_finite {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Finite)
    (hA : Cardinal.mk A ≤ Cardinal.continuum) : Cardinal.mk B ≤ Cardinal.continuum := by
  letI := g.toAlgebra
  haveI : Module.Finite A B := hg
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]
  exact (pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)

/- English proof (translation)
Break down `ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Conclude with `⟨r, hr⟩`. Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨t, ht⟩` from `hx`.

Establish `h1 : algebraMap A B (e r * t) = 1`. Rewrite using `[map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]`. Establish `h2 : e r * t = 1` using `IsFractionRing.injective A B (h1.trans (map_one _).symm)`. Establish `hu : IsUnit r` using `isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)`. Take `⟨u, rfl⟩` from `hu`.

Use `⟨(u⁻¹ : Rˣ), ?_⟩` and prove the remaining obligations. Establish `h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1`. Rewrite using `[← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]`. Conclude with `(mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3`.
-/
theorem mem_range_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K)
    (hx : la x ∈ (algebraMap A B).range) : x ∈ (algebraMap R K).range := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨t, ht⟩ := hx
  have h1 : algebraMap A B (e r * t) = 1 := by
    rw [map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]
  have h2 : e r * t = 1 := IsFractionRing.injective A B (h1.trans (map_one _).symm)
  have hu : IsUnit r := isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  have h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1 := by
    rw [← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]
  exact (mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Establish `h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G`. Rewrite using `[Y.ab_gen]`. Conclude with `⟨x, rfl⟩`. Rewrite using `[Model.j, Scheme.Hom.comp_apply]`.

Conclude with `h`.
-/
theorem range_j_subset {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  rw [Model.j, Scheme.Hom.comp_apply]
  exact h

/- English proof (translation)
Set `u : Sp S ⟶ pullback Y.s (spMap β)` to `pullback.lift w (spMap k) (hw.trans (sp_comp _ _).symm)`. Use `Y.jQ_open` as an intermediate fact. Establish `hu : Set.range u ⊆ Set.range Y.jQ`. Rewrite using `[← Y.ab_gen]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Use `hr ⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, pullback.lift_fst]`. Use `⟨IsOpenImmersion.lift Y.jQ u hu, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`. Rewrite using `[← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]`.
-/
theorem exists_lift {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Type} [CommRing S]
    (w : Sp S ⟶ Y.X) (k : c.F →+* S) (hw : w ≫ Y.s = spMap (k.comp β)) (hr : Set.range w ⊆ abLocus Y.t.G) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = w ∧ z ≫ pullback.snd _ _ = spMap k := by
  let u : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift w (spMap k) (hw.trans (sp_comp _ _).symm)
  have := Y.jQ_open
  have hu : Set.range u ⊆ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    rintro _ ⟨x, rfl⟩
    refine hr ⟨x, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  refine ⟨IsOpenImmersion.lift Y.jQ u hu, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

/- English proof (translation)
Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Apply `hκ` to reduce the goal to its premises. Establish `e1 : HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.X : PowerSeries A) ^ N)) = HahnSeries.single (N : ℤ) 1`. Rewrite using `[map_pow, PowerSeries.map_X, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow]`.

Simplify using the standard rewrite rules. Establish `e2` using `congrArg (fun G : ℂ⸨X⸩ => G.coeff (((m : ℤ) - N) + N)) e`. Simplify using `only [e1, HahnSeries.coeff_mul_single_add] at e2`. Rewrite `e2` using `[hF _ (by omega), zero_mul, sub_add_cancel, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]`. Rewrite using `[← e2, map_zero]`.
-/
theorem X_pow_dvd {A : Type} [CommRing A] (κ : A →+* ℂ) (hκ : Function.Injective κ) (F : ℂ⸨X⸩)
    (hF : ∀ m : ℤ, m < 0 → F.coeff m = 0) (h : PowerSeries A) (N : ℕ)
    (e : F * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ (PowerSeries.X ^ N)) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ h)) : PowerSeries.X ^ N ∣ h := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  apply hκ
  have e1 : HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.X : PowerSeries A) ^ N)) =
      HahnSeries.single (N : ℤ) 1 := by
    rw [map_pow, PowerSeries.map_X, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow]
    simp
  have e2 := congrArg (fun G : ℂ⸨X⸩ => G.coeff (((m : ℤ) - N) + N)) e
  simp only [e1, HahnSeries.coeff_mul_single_add] at e2
  rw [hF _ (by omega), zero_mul, sub_add_cancel, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map] at e2
  rw [← e2, map_zero]

/- English proof (translation)
Take `⟨⟨h, s, N, rfl⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries A)) v`. Take `⟨w, hw⟩` from `hv`. Establish `hF : ∀ m : ℤ, m < 0 → (ιC v).coeff m = 0` using `fun m hm => by`. Rewrite using `[← hw]`. Conclude with `HahnSeries.embDomain_notin_range (by`.

Introduce and unpack `⟨n, hn⟩`. Establish `: ((n : ℕ) : ℤ) = m` using `by simpa using hn`. Use the proof step `omega)`. Take `⟨s, rfl⟩` from `X_pow_dvd κ hκ (ιC v) hF h N (by`. Rewrite using `[← hι, ← hι, ← map_mul]`.

Conclude with `congrArg ιC hs)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap _ S ((PowerSeries.X : PowerSeries A) ^ N))` using `IsLocalization.map_units S (⟨_, N, rfl⟩ : Submonoid.powers (PowerSeries.X : PowerSeries A))`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[mul_comm, ← map_mul]`.

Simplify using `using hs`.
-/
theorem exists_eq_of_no_pole {A : Type} [CommRing A] [IsDomain A] (κ : A →+* ℂ) (hκ : Function.Injective κ)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.X : PowerSeries A) S]
    (ιC : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A, ιC (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ s)) (v : S)
    (hv : ιC v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) : ∃ s : PowerSeries A, v = algebraMap _ S s := by
  obtain ⟨⟨h, s, N, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries A)) v
  obtain ⟨w, hw⟩ := hv
  have hF : ∀ m : ℤ, m < 0 → (ιC v).coeff m = 0 := fun m hm => by
    rw [← hw]
    exact HahnSeries.embDomain_notin_range (by
      rintro ⟨n, hn⟩
      have : ((n : ℕ) : ℤ) = m := by simpa using hn
      omega)
  obtain ⟨s, rfl⟩ := X_pow_dvd κ hκ (ιC v) hF h N (by
    rw [← hι, ← hι, ← map_mul]; exact congrArg ιC hs)
  refine ⟨s, ?_⟩
  have hu : IsUnit (algebraMap _ S ((PowerSeries.X : PowerSeries A) ^ N)) :=
    IsLocalization.map_units S (⟨_, N, rfl⟩ : Submonoid.powers (PowerSeries.X : PowerSeries A))
  apply hu.mul_left_cancel
  rw [mul_comm, ← map_mul]
  simpa using hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩`.
-/
theorem exists_frac_lift {A K L : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (f : A →+* L) (hf : Function.Injective f) : ∃ fK : K →+* L, fK.comp (algebraMap A K) = f :=
  ⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩`.
-/
theorem exists_away_lift {A S L : Type} [CommRing A] [CommRing S] [Algebra A S] (x : A) [IsLocalization.Away x S]
    [CommRing L] (f : A →+* L) (hf : IsUnit (f x)) : ∃ F : S →+* L, ∀ a, F (algebraMap A S a) = f a :=
  ⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩

/- English proof (translation)
Rewrite using `[RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]`. Conclude with `isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)`.
-/
theorem isUnit_map_X {A : Type} [CommRing A] (κ : A →+* ℂ) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ) PowerSeries.X) := by
  rw [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c V Y h3 h4 hS X π hπ U₀ W₀ f₀ hUW harc R K _ _ _ _ _ _ io z hcount hover hU hgen h`. Establish `hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ X), Set.range (w ≫ π) ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ → ⊤ ≤ w ⁻¹ᵁ W₀` using `fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, Scheme.Hom.comp_apply _ _ _⟩)`. Distinguish the cases in `hab : Set.range (z ≫ π) ⊆ abLocus Y.t.G`. Take `⟨w, hw, -⟩` from `exists_lift Y (z ≫ π) io ((Category.assoc _ _ _).trans hover) hab`. Establish `hr : Set.range (z ≫ π) ⊆ Set.range Y.j`.

Rewrite using `[← hw]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨w x, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Conclude with `⟨ev z W₀ (hzW z hr hU) f₀, (ev_factor _ z _ rfl W₀ (hzW z hr hU) h f₀).symm⟩`. Establish `hch : CharZero R` using `(RingHom.charZero_iff io.injective).1 inferInstance`.

Take `⟨T, i, hi, hil, hcard⟩` from `GlobalTheory.T.exists_complete_dvr_local_extension_of_countable R hcount`. Establish `hiF : Function.Injective ((algebraMap T.V T.Fr).comp i)` using `(IsFractionRing.injective T.V T.Fr).comp hi`. Take `⟨iK, hiK⟩` from `exists_frac_lift (K := K) _ hiF`. Set `y' : Sp T.V ⟶ Y.X` to `spMap i ≫ z ≫ π`. Set `b : V →+* T.V` to `i.comp (io.comp V.subtype)`.

Set `io' : c.F →+* T.Fr` to `(algebraMap T.V T.Fr).comp (i.comp io)`. Establish `hy' : y' ≫ Y.s = spMap b`. Simplify using `only [y', Category.assoc]`. Rewrite using `[hover, sp_comp]`. Establish `hgenT : spMap (algebraMap T.V T.Fr) ≫ y' = spMap iK ≫ spMap (algebraMap R K) ≫ z ≫ π`.

Simplify using `only [y']`. Rewrite using `[← Category.assoc, sp_comp, ← hiK, ← sp_comp, Category.assoc]`. Take `⟨zT, hzT, hzT'⟩` from `exists_lift Y (spMap (algebraMap T.V T.Fr) ≫ y') io' (by`. Rewrite using `[Category.assoc, hy', sp_comp]) (by`. Rewrite using `[hgenT]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `range_j_subset Y (hgen ⟨spMap iK x, (Scheme.Hom.comp_apply _ _ _).symm⟩))`. Establish `hbad : ¬ Set.range y' ⊆ abLocus Y.t.G` using `fun hy => hab (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Break down `point_cases R K x with ⟨p, rfl⟩ | rfl` into its components or cases.

Conclude with `range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)`. Establish `e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R` using `spMap_closedPoint i`. Use `hy ⟨IsLocalRing.closedPoint T.V, rfl⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `(spMap i ≫ (z ≫ π)) (IsLocalRing.closedPoint T.V) ∈ _ at this`. Use `erw [Scheme.Hom.comp_apply, e] at this`.

Conclude with `this)`. Take `⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩` from `GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c V Y h3 hS T io' b y' zT rfl hy' hzT' hzT hbad`. Establish `hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V` using `hϖ.maximalIdeal_eq ▸ T'.cpl`. Take `⟨χ₀, hχ, hsp⟩` from `h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)`. Take `⟨hover₀, hab₀, hopen, hW⟩` from `(hχ χ₀).1 rfl`.

Take `⟨W⟩` from `(Y.hasArcData_iff a _ _ _ χ₀).1 hW`. Take `⟨-, -, evu, hevC, hevX, -⟩` from `GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl`. Establish `hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g)` using `(IsFractionRing.injective T'.V T'.Fr).comp hg`. Take `⟨gF, hgF'⟩` from `exists_frac_lift (K := T.Fr) _ hgF`. Establish `hχy : spMap evu ≫ χ₀ = spMap g ≫ y'` using `hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Establish `e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j`. Rewrite using `[hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]`. Both sides reduce to the same expression. Conclude with `⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX`.

Use `haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg`. Establish `hχz : spMap evu ≫ χ₀ ≫ inv π = spMap g ≫ spMap i ≫ z`. Rewrite using `[← Category.assoc, hχy]`. Simplify using `only [y', Category.assoc, IsIso.hom_inv_id, Category.comp_id]`. Establish `hχU : ⊤ ≤ (χ₀ ≫ inv π) ⁻¹ᵁ U₀`.

Establish `hc : (χ₀ ≫ inv π) (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀`. Rewrite using `[← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]`. Express the relevant statement in the definitionally equal form `(spMap evu ≫ χ₀ ≫ inv π) (IsLocalRing.closedPoint T'.V) ∈ U₀`. Rewrite using `[hχz]`. Conclude with `hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))`.

Conclude with `((IsLocalRing.closed_point_mem_iff (U := (χ₀ ≫ inv π) ⁻¹ᵁ U₀)).1 hc).ge`. Establish `hle : Submonoid.powers (PowerSeries.X : PowerSeries T'.V) ≤ nonZeroDivisors _` using `powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero`. Use `haveI : IsDomain (Localization.Away (PowerSeries.X : PowerSeries T'.V)) := IsLocalization.isDomain_localization hle`. Set `ι : PowerSeries T'.V →+* Localization.Away (PowerSeries.X : PowerSeries T'.V)` to `algebraMap _ _`. Establish `huX : IsUnit (ι PowerSeries.X)` using `IsLocalization.Away.algebraMap_isUnit _`.

Take `⟨zS, hzS, -⟩` from `exists_lift Y (spMap ι ≫ χ₀) (ι.comp (PowerSeries.C.comp (g.comp (i.comp io)))) (by`. Rewrite using `[Category.assoc, hover₀, sp_comp, sp_comp]) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Express the relevant statement in the definitionally equal form `χ₀ (spMap ι x) ∈ _`. Rewrite using `[hab₀]`.

Conclude with `fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ x.asIdeal from hx) huX))`. Establish `hSW : ⊤ ≤ (spMap ι ≫ χ₀ ≫ inv π) ⁻¹ᵁ W₀` using `hzW _ (by`. Rewrite using `[Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← hzS]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨zS x, (Scheme.Hom.comp_apply _ _ _).symm⟩) (le_preimage_comp _ hχU)`.

Establish `hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum`. Rewrite using `[show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]`. Conclude with `mk_le_continuum_of_finite g hgf hcard`. Take `⟨κ, hκ⟩` from `@GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _ ((algebraMap T'.V T'.Fr).comp (g.comp (i.comp io))).toAlgebra hcard' c.F.val.toRingHom`. Set `κ₀ : T'.V →+* ℂ` to `κ.comp (algebraMap T'.V T'.Fr)`.

Establish `hκ₀ : Function.Injective κ₀` using `κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)`. Establish `hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b)`. Rewrite using `[← hκ]`. Both sides reduce to the same expression. Take `⟨h1, h2, -, hL4, hL5⟩` from `GlobalTheory.firstFiveLaws`.

Take `⟨⟨a₁, p, hp⟩, hbc⟩` from `GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ (g.comp b) a κ₀ hκ₀ _ hb'`. Take `⟨hW₁, -⟩` from `hbc a₁ p hp`. Take `⟨W₁, -⟩` from `hW₁ χ₀ W`. Establish `hXu` using `isUnit_map_X κ₀`. Take `⟨ιC, hιC'⟩` from `exists_away_lift (S := Localization.Away (PowerSeries.X : PowerSeries T'.V)) _ _ hXu`.

Establish `hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s)` using `fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)`. Establish `hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π = spMap ιC ≫ spMap ι ≫ χ₀ ≫ inv π`. Rewrite using `[← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp, show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]`. Establish `hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) ⁻¹ᵁ W₀`. Rewrite using `[hpt]`.

Conclude with `le_preimage_comp _ hSW`. Establish `hϖ0 : κ₀ ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))`. Establish `hres` using `harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) (by`. Rewrite using `[Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Conclude with `(Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by`.

Rewrite using `[Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']`. Conclude with `congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by`. Express the relevant statement in the definitionally equal form `((spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) ≫ π) x ∈ _`. Rewrite using `[Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Use `hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_` and prove the remaining obligations.

Establish `hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal` using `hm`. Rewrite `hm'` using `[map_mul, PowerSeries.map_C, PowerSeries.map_X]`. Conclude with `hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))`. Use the proof step `(le_preimage_comp _ hχU) hLh`. Rewrite `hres` using `[ev_factor ιC (spMap ι ≫ χ₀ ≫ inv π) _ hpt W₀ hSW hLh f₀]`.

Take `⟨s, hs⟩` from `exists_eq_of_no_pole κ₀ hκ₀ (Localization.Away (PowerSeries.X : PowerSeries T'.V)) ιC hιC _ hres`. Establish `hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu PowerSeries.X)`. Rewrite using `[RingHom.comp_apply, hevX]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2 hϖ.ne_zero)`. Take `⟨φS, hφS⟩` from `exists_away_lift (S := Localization.Away (PowerSeries.X : PowerSeries T'.V)) _ _ hϖu`.

Establish `hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i))` using `(IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)`. Take `⟨la, hla⟩` from `exists_frac_lift (K := K) _ hgi`. Establish `hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ ≫ inv π`. Establish `e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z`. Rewrite using `[← Category.assoc, sp_comp, hla]`.

Establish `e2 : spMap φS ≫ spMap ι ≫ χ₀ ≫ inv π = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z`. Rewrite using `[← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS, ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]`. Rewrite using `[e1, e2]`. Establish `hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s)`. Rewrite using `[← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h), GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]`.

Both sides reduce to the same expression. Use `haveI : IsLocalHom (g.comp i) := inferInstance`. Conclude with `mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩`.
-/
theorem integral_of_arcs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → ∀ (X : Scheme.{0}) (π : X ⟶ Y.X), IsIso π → ∀ (U₀ W₀ : X.Opens) (f₀ : Γ(X, W₀)), (∀ x ∈ U₀, π x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn Dw l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X (χ ≫ π) → χ ≫ π ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → π (χ x) ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (io : c.F →+* R) (z : Sp R ⟶ X), Countable R → z ≫ π ≫ Y.s = spMap (io.comp V.subtype) → ⊤ ≤ z ⁻¹ᵁ U₀ → Set.range (spMap (algebraMap R K) ≫ z ≫ π) ⊆ Set.range Y.j → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  intro E _ _ _ H Dw l Xo c V Y h3 h4 hS X π hπ U₀ W₀ f₀ hUW harc R K _ _ _ _ _ _ io z hcount hover hU hgen h
  have hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ X), Set.range (w ≫ π) ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ →
      ⊤ ≤ w ⁻¹ᵁ W₀ := fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, Scheme.Hom.comp_apply _ _ _⟩)
  by_cases hab : Set.range (z ≫ π) ⊆ abLocus Y.t.G
  · obtain ⟨w, hw, -⟩ := exists_lift Y (z ≫ π) io ((Category.assoc _ _ _).trans hover) hab
    have hr : Set.range (z ≫ π) ⊆ Set.range Y.j := by
      rw [← hw]; rintro _ ⟨x, rfl⟩; exact ⟨w x, (Scheme.Hom.comp_apply _ _ _).symm⟩
    exact ⟨ev z W₀ (hzW z hr hU) f₀, (ev_factor _ z _ rfl W₀ (hzW z hr hU) h f₀).symm⟩

  have hch : CharZero R := (RingHom.charZero_iff io.injective).1 inferInstance
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.T.exists_complete_dvr_local_extension_of_countable R hcount
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  obtain ⟨iK, hiK⟩ := exists_frac_lift (K := K) _ hiF
  let y' : Sp T.V ⟶ Y.X := spMap i ≫ z ≫ π
  let b : V →+* T.V := i.comp (io.comp V.subtype)
  let io' : c.F →+* T.Fr := (algebraMap T.V T.Fr).comp (i.comp io)
  have hy' : y' ≫ Y.s = spMap b := by
    simp only [y', Category.assoc]; rw [hover, sp_comp]
  have hgenT : spMap (algebraMap T.V T.Fr) ≫ y' = spMap iK ≫ spMap (algebraMap R K) ≫ z ≫ π := by
    simp only [y']
    rw [← Category.assoc, sp_comp, ← hiK, ← sp_comp, Category.assoc]
  obtain ⟨zT, hzT, hzT'⟩ := exists_lift Y (spMap (algebraMap T.V T.Fr) ≫ y') io' (by
      rw [Category.assoc, hy', sp_comp]) (by
      rw [hgenT]; rintro _ ⟨x, rfl⟩
      exact range_j_subset Y (hgen ⟨spMap iK x, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  have hbad : ¬ Set.range y' ⊆ abLocus Y.t.G := fun hy => hab (by
    rintro _ ⟨x, rfl⟩
    rcases point_cases R K x with ⟨p, rfl⟩ | rfl
    · exact range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)
    · have e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R := spMap_closedPoint i
      have := hy ⟨IsLocalRing.closedPoint T.V, rfl⟩
      change (spMap i ≫ (z ≫ π)) (IsLocalRing.closedPoint T.V) ∈ _ at this
      erw [Scheme.Hom.comp_apply, e] at this; exact this)
  obtain ⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c V Y h3 hS T io' b y' zT rfl hy' hzT' hzT hbad
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V := hϖ.maximalIdeal_eq ▸ T'.cpl
  obtain ⟨χ₀, hχ, hsp⟩ := h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover₀, hab₀, hopen, hW⟩ := (hχ χ₀).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ₀).1 hW
  obtain ⟨-, -, evu, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl
  have hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hg
  obtain ⟨gF, hgF'⟩ := exists_frac_lift (K := T.Fr) _ hgF
  have hχy : spMap evu ≫ χ₀ = spMap g ≫ y' := hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      have e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j := by
        rw [hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]
        rfl
      exact ⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX

  haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg
  have hχz : spMap evu ≫ χ₀ ≫ inv π = spMap g ≫ spMap i ≫ z := by
    rw [← Category.assoc, hχy]
    simp only [y', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hχU : ⊤ ≤ (χ₀ ≫ inv π) ⁻¹ᵁ U₀ := by
    have hc : (χ₀ ≫ inv π) (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀ := by
      rw [← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]
      change (spMap evu ≫ χ₀ ≫ inv π) (IsLocalRing.closedPoint T'.V) ∈ U₀
      rw [hχz]
      exact hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))
    exact ((IsLocalRing.closed_point_mem_iff (U := (χ₀ ≫ inv π) ⁻¹ᵁ U₀)).1 hc).ge

  have hle : Submonoid.powers (PowerSeries.X : PowerSeries T'.V) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero
  haveI : IsDomain (Localization.Away (PowerSeries.X : PowerSeries T'.V)) := IsLocalization.isDomain_localization hle
  let ι : PowerSeries T'.V →+* Localization.Away (PowerSeries.X : PowerSeries T'.V) := algebraMap _ _
  have huX : IsUnit (ι PowerSeries.X) := IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨zS, hzS, -⟩ := exists_lift Y (spMap ι ≫ χ₀) (ι.comp (PowerSeries.C.comp (g.comp (i.comp io)))) (by
      rw [Category.assoc, hover₀, sp_comp, sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      change χ₀ (spMap ι x) ∈ _
      rw [hab₀]
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ x.asIdeal from hx) huX))
  have hSW : ⊤ ≤ (spMap ι ≫ χ₀ ≫ inv π) ⁻¹ᵁ W₀ := hzW _ (by
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← hzS]
      rintro _ ⟨x, rfl⟩
      exact ⟨zS x, (Scheme.Hom.comp_apply _ _ _).symm⟩) (le_preimage_comp _ hχU)

  have hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum := by
    rw [show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact mk_le_continuum_of_finite g hgf hcard
  obtain ⟨κ, hκ⟩ := @GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _
    ((algebraMap T'.V T'.Fr).comp (g.comp (i.comp io))).toAlgebra hcard' c.F.val.toRingHom
  let κ₀ : T'.V →+* ℂ := κ.comp (algebraMap T'.V T'.Fr)
  have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b) := by
    rw [← hκ]; rfl
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ
    (g.comp b) a κ₀ hκ₀ _ hb'
  obtain ⟨hW₁, -⟩ := hbc a₁ p hp
  obtain ⟨W₁, -⟩ := hW₁ χ₀ W
  have hXu := isUnit_map_X κ₀
  obtain ⟨ιC, hιC'⟩ := exists_away_lift (S := Localization.Away (PowerSeries.X : PowerSeries T'.V)) _ _ hXu
  have hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s) :=
    fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)
  have hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π =
      spMap ιC ≫ spMap ι ≫ χ₀ ≫ inv π := by
    rw [← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp,
      show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]
  have hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) ⁻¹ᵁ W₀ := by
    rw [hpt]; exact le_preimage_comp _ hSW
  have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
  have hres := harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) (by
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact (Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by
      change ((spMap (PowerSeries.map κ₀) ≫ χ₀ ≫ inv π) ≫ π) x ∈ _
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      refine hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))
    (le_preimage_comp _ hχU) hLh
  rw [ev_factor ιC (spMap ι ≫ χ₀ ≫ inv π) _ hpt W₀ hSW hLh f₀] at hres
  obtain ⟨s, hs⟩ := exists_eq_of_no_pole κ₀ hκ₀ (Localization.Away (PowerSeries.X : PowerSeries T'.V)) ιC hιC _ hres

  have hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu PowerSeries.X) := by
    rw [RingHom.comp_apply, hevX]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2 hϖ.ne_zero)
  obtain ⟨φS, hφS⟩ := exists_away_lift (S := Localization.Away (PowerSeries.X : PowerSeries T'.V)) _ _ hϖu
  have hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i)) :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)
  obtain ⟨la, hla⟩ := exists_frac_lift (K := K) _ hgi
  have hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ ≫ inv π := by
    have e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, hla]
    have e2 : spMap φS ≫ spMap ι ≫ χ₀ ≫ inv π = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS,
        ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    rw [e1, e2]
  have hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s) := by
    rw [← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h),
      GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]
    rfl
  haveI : IsLocalHom (g.comp i) := inferInstance
  exact mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩

end GlobalTheory.ArcIntegral
