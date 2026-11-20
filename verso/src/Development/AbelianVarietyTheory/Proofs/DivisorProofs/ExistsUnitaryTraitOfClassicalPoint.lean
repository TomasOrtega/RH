import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UTraitPt

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_eq {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Set `V₀` to `integralClosure ℤ_[p] K`. Use `letI : Algebra V₀ W := f.toAlgebra`. Use `haveI : Module.Finite V₀ W := hfin`. Use `haveI : IsFractionRing V₀ K := integralClosure.isFractionRing_of_finite_extension ℚ_[p] K`. Set `eK : K ≃ₐ[V₀] FractionRing V₀` to `IsLocalization.algEquiv (nonZeroDivisors V₀) K (FractionRing V₀)`.

Use `letI : Algebra K (FractionRing W) := (fK.comp eK.toRingHom).toAlgebra`. Establish `e : (algebraMap W (FractionRing W)).comp (algebraMap V₀ W) = (algebraMap K (FractionRing W)).comp (algebraMap V₀ K)`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Use `show algebraMap W (FractionRing W) (f a) = fK (eK (algebraMap V₀ K a))`. Rewrite using `[AlgEquiv.commutes, hfK]`.

Take `⟨K', hKK', hK', τ, f', hτK, hτW⟩` from `GlobalTheory.SS.exists_ringHom_integralClosure p K W (FractionRing W) e`. Set `ι : FractionRing W →+* PadicAlgCl p` to `K'.val.toRingHom.comp τ`. Set `j : W →+* OO p` to `(integralClosureToPadicAlgClIntegers K').comp f'`. Establish `hj : ∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v)` using `fun v => by show ((f' v : K') : PadicAlgCl p) = ((τ (algebraMap W (FractionRing W) v) : K') : PadicAlgCl p)`. Rewrite using `[← RingHom.comp_apply τ, hτW]`.

Both sides reduce to the same expression. Establish `hball : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hint : IsIntegral ℤ_[p] (τ x)` using `(mem_integralClosure_padicInt_iff K' (τ x)).2 hx`. Set `ρ : ℤ_[p] →+* W` to `f.comp (algebraMap ℤ_[p] V₀)`. Use `letI : Algebra ℤ_[p] W := ρ.toAlgebra`. Establish `hτc : ∀ r : ℤ_[p], τ (algebraMap ℤ_[p] (FractionRing W) r) = algebraMap ℤ_[p] K' r`. Introduce `r`.

Establish `h1 : algebraMap ℤ_[p] (FractionRing W) r = (algebraMap K (FractionRing W)) (algebraMap V₀ K (algebraMap ℤ_[p] V₀ r))`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[p] W (FractionRing W)]`. Conclude with `congrArg (fun φ : V₀ →+* FractionRing W => φ (algebraMap ℤ_[p] V₀ r)) e`. Rewrite using `[h1, ← RingHom.comp_apply τ, hτK]`. Both sides reduce to the same expression.

Set `τa : FractionRing W →ₐ[ℤ_[p]] K'` to `{ τ with commutes' := hτc }`. Establish `hx' : IsIntegral ℤ_[p] x` using `(isIntegral_algHom_iff τa τ.injective).1 hint`. Establish `hxW : IsIntegral W x` using `hx'.tower_top`. Take `⟨w, hw⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hxW`. Conclude with `⟨w, hw⟩`.

Introduce and unpack `⟨w, rfl⟩`. Rewrite using `[← hj]`. Conclude with `(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (j w).2`. Use `⟨ι, j, hball, hj, ⟨fun v hv => ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hv.exists_right_inv`.

Establish `hu' : ι (algebraMap W (FractionRing W) v) * (u : PadicAlgCl p) = 1`. Rewrite using `[← hj]`. Conclude with `congrArg (fun z : OO p => (z : PadicAlgCl p)) hu`. Establish `h0 : algebraMap W (FractionRing W) v ≠ 0`. Introduce `h0`.

Rewrite `hu'` using `[h0, map_zero, zero_mul]`. Conclude with `zero_ne_one hu'`. Establish `hinv : (algebraMap W (FractionRing W) v)⁻¹ ∈ Set.range (algebraMap W (FractionRing W))`. Rewrite using `[← hball, map_inv₀, ← eq_inv_of_mul_eq_one_right hu']`. Conclude with `(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2`.

Take `⟨w, hw⟩` from `hinv`. Use `IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective W (FractionRing W) ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hw, map_one, mul_inv_cancel₀ h0]`. Rewrite using `[hj]`. Establish `h1 : algebraMap W (FractionRing W) (f a) = algebraMap K (FractionRing W) (algebraMap V₀ K a)` using `congrArg (fun φ : V₀ →+* FractionRing W => φ a) e`.

Use `show ((τ (algebraMap W (FractionRing W) (f a)) : K') : PadicAlgCl p) = _`. Rewrite using `[h1, ← RingHom.comp_apply τ, hτK]`. Both sides reduce to the same expression.
-/
theorem exists_embed_padicAlgCl (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (f : integralClosure ℤ_[p] K →+* W) (fK : FractionRing (integralClosure ℤ_[p] K) →+* FractionRing W)
    (hfin : f.Finite) (hfK : ∀ a, fK (algebraMap _ _ a) = algebraMap W (FractionRing W) (f a)) :
    ∃ (ι : FractionRing W →+* PadicAlgCl p) (j : W →+* OO p),
      (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧
      (∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v)) ∧ IsLocalHom j ∧
      ∀ a, (j (f a) : PadicAlgCl p) = ((a : K) : PadicAlgCl p) := by
  let V₀ := integralClosure ℤ_[p] K
  letI : Algebra V₀ W := f.toAlgebra
  haveI : Module.Finite V₀ W := hfin
  haveI : IsFractionRing V₀ K := integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
  let eK : K ≃ₐ[V₀] FractionRing V₀ := IsLocalization.algEquiv (nonZeroDivisors V₀) K (FractionRing V₀)
  letI : Algebra K (FractionRing W) := (fK.comp eK.toRingHom).toAlgebra
  have e : (algebraMap W (FractionRing W)).comp (algebraMap V₀ W) =
      (algebraMap K (FractionRing W)).comp (algebraMap V₀ K) := by
    refine RingHom.ext fun a => ?_
    show algebraMap W (FractionRing W) (f a) = fK (eK (algebraMap V₀ K a))
    rw [AlgEquiv.commutes, hfK]
  obtain ⟨K', hKK', hK', τ, f', hτK, hτW⟩ :=
    GlobalTheory.SS.exists_ringHom_integralClosure p K W (FractionRing W) e
  let ι : FractionRing W →+* PadicAlgCl p := K'.val.toRingHom.comp τ
  let j : W →+* OO p := (integralClosureToPadicAlgClIntegers K').comp f'
  have hj : ∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v) := fun v => by
    show ((f' v : K') : PadicAlgCl p) = ((τ (algebraMap W (FractionRing W) v) : K') : PadicAlgCl p)
    rw [← RingHom.comp_apply τ, hτW]; rfl
  have hball : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
    intro x
    constructor
    · intro hx
      have hint : IsIntegral ℤ_[p] (τ x) := (mem_integralClosure_padicInt_iff K' (τ x)).2 hx
      let ρ : ℤ_[p] →+* W := f.comp (algebraMap ℤ_[p] V₀)
      letI : Algebra ℤ_[p] W := ρ.toAlgebra
      have hτc : ∀ r : ℤ_[p], τ (algebraMap ℤ_[p] (FractionRing W) r) = algebraMap ℤ_[p] K' r := by
        intro r
        have h1 : algebraMap ℤ_[p] (FractionRing W) r =
            (algebraMap K (FractionRing W)) (algebraMap V₀ K (algebraMap ℤ_[p] V₀ r)) := by
          rw [IsScalarTower.algebraMap_apply ℤ_[p] W (FractionRing W)]
          exact congrArg (fun φ : V₀ →+* FractionRing W => φ (algebraMap ℤ_[p] V₀ r)) e
        rw [h1, ← RingHom.comp_apply τ, hτK]
        rfl
      let τa : FractionRing W →ₐ[ℤ_[p]] K' := { τ with commutes' := hτc }
      have hx' : IsIntegral ℤ_[p] x := (isIntegral_algHom_iff τa τ.injective).1 hint
      have hxW : IsIntegral W x := hx'.tower_top
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxW
      exact ⟨w, hw⟩
    · rintro ⟨w, rfl⟩
      rw [← hj]
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (j w).2
  refine ⟨ι, j, hball, hj, ⟨fun v hv => ?_⟩, fun a => ?_⟩
  · obtain ⟨u, hu⟩ := hv.exists_right_inv
    have hu' : ι (algebraMap W (FractionRing W) v) * (u : PadicAlgCl p) = 1 := by
      rw [← hj]; exact congrArg (fun z : OO p => (z : PadicAlgCl p)) hu
    have h0 : algebraMap W (FractionRing W) v ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hu'; exact zero_ne_one hu'
    have hinv : (algebraMap W (FractionRing W) v)⁻¹ ∈ Set.range (algebraMap W (FractionRing W)) := by
      rw [← hball, map_inv₀, ← eq_inv_of_mul_eq_one_right hu']
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
    obtain ⟨w, hw⟩ := hinv
    refine IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective W (FractionRing W) ?_)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ h0]
  · rw [hj]
    have h1 : algebraMap W (FractionRing W) (f a) = algebraMap K (FractionRing W) (algebraMap V₀ K a) :=
      congrArg (fun φ : V₀ →+* FractionRing W => φ a) e
    show ((τ (algebraMap W (FractionRing W) (f a)) : K') : PadicAlgCl p) = _
    rw [h1, ← RingHom.comp_apply τ, hτK]
    rfl

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

/- English proof (translation)
Use `letI := C.b.toAlgebra`. Use `haveI := C.isFractionRing`. Use `haveI := C.ded`. Use `haveI := C.iF_open`. Use `haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)`.

Use `haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance`. Establish `hinj : Function.Injective (pullback.fst C.z (spMap C.b))` using `(pullback.fst C.z (spMap C.b)).isEmbedding.injective`. Set `pt : Sp F` to `⟨⊥, Ideal.isPrime_bot⟩`. Take `⟨x, hx⟩` from `hg ⟨pt, rfl⟩`. Set `φ : C.o →+* F` to `(Spec.preimage (g ≫ C.z)).hom`.

Establish `hφ : spMap φ = g ≫ C.z` using `Spec.map_preimage _`. Establish `hφi : Function.Injective φ`. Establish `e : (spMap φ) pt = (spMap C.b) ((C.iF ≫ pullback.snd C.z (spMap C.b)) x)`. Rewrite using `[hφ, Scheme.Hom.comp_apply, ← hx]`. Use `show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _`.

Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]`. Both sides reduce to the same expression. Establish `e2 : RingHom.ker φ = ⊥`. Use `congrArg PrimeSpectrum.asIdeal e` as an intermediate fact. Establish `h1 : ((spMap φ) pt).asIdeal = RingHom.ker φ` using `by show Ideal.comap φ ⊥ = _`.

Both sides reduce to the same expression. Rewrite `this` using `[h1]`. Rewrite using `[this]`. Use `haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime`. Use `show Ideal.comap C.b _ = ⊥`.

Rewrite using `[Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.comap_bot_of_injective _ C.inj]`. Conclude with `(RingHom.injective_iff_ker_eq_bot φ).2 e2`. Set `ψ : c.F →+* F` to `IsFractionRing.lift hφi`. Establish `hψ : ψ.comp C.b = φ` using `RingHom.ext fun a => IsFractionRing.lift_algebraMap hφi a`. Establish `hsq : g ≫ C.z = spMap ψ ≫ spMap C.b`.

Rewrite using `[← hφ, ← hψ]`. Conclude with `spMap_comp_eq _ _`. Set `g₁ : Sp F ⟶ pullback C.z (spMap C.b)` to `pullback.lift g (spMap ψ) hsq`. Establish `hr : Set.range g₁ ⊆ Set.range C.iF`. Introduce and unpack `_ ⟨w, rfl⟩`.

Establish `hw : w = pt` using `Subsingleton.elim _ _`. Substitute `hw` using the available equality. Use `⟨x, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]`. Conclude with `hx`.

Use `⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩` and prove the remaining obligations. Use `show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`.
-/
theorem exists_lift_i {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (C : UCompact Xo c) (F : Type) [Field F]
    (g : Sp F ⟶ C.Z) (hg : Set.range g ⊆ Set.range C.i) : ∃ g' : Sp F ⟶ Xo.XF c, g' ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  let pt : Sp F := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, hx⟩ := hg ⟨pt, rfl⟩
  let φ : C.o →+* F := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hφi : Function.Injective φ := by
    have e : (spMap φ) pt = (spMap C.b) ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
      rw [hφ, Scheme.Hom.comp_apply, ← hx]
      show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
      rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
      rfl
    have e2 : RingHom.ker φ = ⊥ := by
      have := congrArg PrimeSpectrum.asIdeal e
      have h1 : ((spMap φ) pt).asIdeal = RingHom.ker φ := by
        show Ideal.comap φ ⊥ = _
        rfl
      rw [h1] at this
      rw [this]
      haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
      show Ideal.comap C.b _ = ⊥
      rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.comap_bot_of_injective _ C.inj]
    exact (RingHom.injective_iff_ker_eq_bot φ).2 e2
  let ψ : c.F →+* F := IsFractionRing.lift hφi
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hφi a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact spMap_comp_eq _ _
  let g₁ : Sp F ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hw : w = pt := Subsingleton.elim _ _
    subst hw
    refine ⟨x, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hx
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c C X₁ Y πY p _ y hy`. Use `haveI : Algebra.FiniteType ℤ X₁.o₁ := X₁.ar.ft`. Use `haveI := Y.lft`. Use `haveI hSpecZ : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) := by show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ X₁.o₁)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`.

Conclude with `RingHom.finiteType_algebraMap.mpr inferInstance`. Take `⟨K, hK, hKall⟩` from `padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y`. Use `haveI : FiniteDimensional ℚ_[p] K := hK`. Take `⟨j₀, y₀, hj₀, -, hy₀⟩` from `hKall K le_rfl`. Set `V₀` to `integralClosure ℤ_[p] K`.

Use `haveI hdvr : IsDiscreteValuationRing V₀ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K`. Use `haveI : Module.Finite ℤ_[p] V₀ := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _`. Use `haveI : IsAdicComplete (maximalIdeal V₀) V₀ := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] _`. Use `haveI : CharZero V₀ := inferInstance`. Establish `hB : GlobalTheory.Mum.Base V₀` using `⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩`.

Establish `hj₀i : Function.Injective ((OO p).subtype.comp j₀)`. Introduce `a b h`. Establish `h' : ((a : K) : PadicAlgCl p) = ((b : K) : PadicAlgCl p)`. Rewrite using `[← hj₀, ← hj₀]`. Conclude with `h`.

Conclude with `Subtype.ext (Subtype.ext h')`. Take `⟨e₀, he₀'⟩ : ∃ e₀ : FractionRing V₀ →+* PadicAlgCl p, ∀ a, e₀ (algebraMap V₀ (FractionRing V₀) a) = ((OO p).subtype.comp j₀) a` from `⟨IsFractionRing.lift hj₀i, fun a => IsFractionRing.lift_algebraMap hj₀i a⟩`. Establish `he₀ : e₀.comp (algebraMap V₀ (FractionRing V₀)) = (OO p).subtype.comp j₀` using `RingHom.ext he₀'`. Establish `hgy : gPt p ≫ y = spMap e₀ ≫ jK V₀ ≫ y₀`. Rewrite using `[← hy₀, ← Category.assoc, ← Category.assoc]`.

Use `congr 1`. Use `show spMap (OO p).subtype ≫ spMap j₀ = spMap e₀ ≫ spMap (algebraMap V₀ (FractionRing V₀))`. Rewrite using `[← spMap_comp_eq, ← spMap_comp_eq, he₀]`. Set `gen₀ : Sp (FractionRing V₀) ⟶ C.Z` to `jK V₀ ≫ y₀ ≫ πY ≫ X₁.π`. Establish `hgen : Set.range gen₀ ⊆ Set.range C.i`.

Introduce and unpack `_ ⟨w, rfl⟩`. Set `q : Sp (PadicAlgCl p)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hw : w = (spMap e₀) q` using `Subsingleton.elim _ _`. Apply `hy` to reduce the goal to its premises. Use `⟨q, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw, ← Scheme.Hom.comp_apply]`. Use `congr 1`. Rewrite using `[← Category.assoc, hgy]`. Simplify using `only [gen₀, Category.assoc]`. Take `⟨yK, hyK⟩` from `exists_lift_i C (FractionRing V₀) gen₀ hgen`.

Take `⟨T, f, fK, -, -, hfin, hfK, hTy⟩` from `GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V₀ hB hdvr yK`. Use `haveI : IsDiscreteValuationRing T.V := T.cdvr.1`. Take `⟨ι, j, hball, hj, hloc, hjf⟩` from `exists_embed_padicAlgCl p K T.V f fK hfin hfK`. Use `⟨T, ι, j, spMap f ≫ y₀, hball, hj, hloc, ?_, ?_⟩` and prove the remaining obligations. Establish `hjf' : j.comp f = j₀` using `RingHom.ext fun a => Subtype.ext ((hjf a).trans (hj₀ a).symm)`.

Rewrite using `[← Category.assoc, ← spMap_comp_eq, hjf', hy₀]`. Establish `hc : jK T.V ≫ spMap f = spMap fK ≫ jK V₀` using `by show spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap f = spMap fK ≫ spMap (algebraMap V₀ (FractionRing V₀))`. Rewrite using `[← spMap_comp_eq, ← spMap_comp_eq]`. Use `congr 1`. Conclude with `RingHom.ext fun a => (hfK a).symm`.

Rewrite using `[hTy, Category.assoc (spMap fK), hyK]`. Simplify using `only [gen₀, ← Category.assoc]`. Rewrite using `[hc]`.
-/
theorem exists_uTrait_of_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i → ∃ (T : UTrait Xo c) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C X₁ Y πY p _ y hy
  haveI : Algebra.FiniteType ℤ X₁.o₁ := X₁.ar.ft
  haveI := Y.lft
  haveI hSpecZ : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ X₁.o₁)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨K, hK, hKall⟩ := padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI : FiniteDimensional ℚ_[p] K := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := hKall K le_rfl
  let V₀ := integralClosure ℤ_[p] K
  haveI hdvr : IsDiscreteValuationRing V₀ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K
  haveI : Module.Finite ℤ_[p] V₀ := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsAdicComplete (maximalIdeal V₀) V₀ := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] _
  haveI : CharZero V₀ := inferInstance
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

  have hj₀i : Function.Injective ((OO p).subtype.comp j₀) := by
    intro a b h
    have h' : ((a : K) : PadicAlgCl p) = ((b : K) : PadicAlgCl p) := by
      rw [← hj₀, ← hj₀]; exact h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨e₀, he₀'⟩ : ∃ e₀ : FractionRing V₀ →+* PadicAlgCl p,
      ∀ a, e₀ (algebraMap V₀ (FractionRing V₀) a) = ((OO p).subtype.comp j₀) a :=
    ⟨IsFractionRing.lift hj₀i, fun a => IsFractionRing.lift_algebraMap hj₀i a⟩
  have he₀ : e₀.comp (algebraMap V₀ (FractionRing V₀)) = (OO p).subtype.comp j₀ := RingHom.ext he₀'
  have hgy : gPt p ≫ y = spMap e₀ ≫ jK V₀ ≫ y₀ := by
    rw [← hy₀, ← Category.assoc, ← Category.assoc]
    congr 1
    show spMap (OO p).subtype ≫ spMap j₀ = spMap e₀ ≫ spMap (algebraMap V₀ (FractionRing V₀))
    rw [← spMap_comp_eq, ← spMap_comp_eq, he₀]
  let gen₀ : Sp (FractionRing V₀) ⟶ C.Z := jK V₀ ≫ y₀ ≫ πY ≫ X₁.π
  have hgen : Set.range gen₀ ⊆ Set.range C.i := by
    rintro _ ⟨w, rfl⟩
    let q : Sp (PadicAlgCl p) := ⟨⊥, Ideal.isPrime_bot⟩
    have hw : w = (spMap e₀) q := Subsingleton.elim _ _
    apply hy
    refine ⟨q, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply]
    congr 1
    rw [← Category.assoc, hgy]
    simp only [gen₀, Category.assoc]
  obtain ⟨yK, hyK⟩ := exists_lift_i C (FractionRing V₀) gen₀ hgen
  obtain ⟨T, f, fK, -, -, hfin, hfK, hTy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V₀ hB hdvr yK
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨ι, j, hball, hj, hloc, hjf⟩ := exists_embed_padicAlgCl p K T.V f fK hfin hfK
  refine ⟨T, ι, j, spMap f ≫ y₀, hball, hj, hloc, ?_, ?_⟩
  · have hjf' : j.comp f = j₀ := RingHom.ext fun a => Subtype.ext ((hjf a).trans (hj₀ a).symm)
    rw [← Category.assoc, ← spMap_comp_eq, hjf', hy₀]
  · have hc : jK T.V ≫ spMap f = spMap fK ≫ jK V₀ := by
      show spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap f = spMap fK ≫ spMap (algebraMap V₀ (FractionRing V₀))
      rw [← spMap_comp_eq, ← spMap_comp_eq]
      congr 1
      exact RingHom.ext fun a => (hfK a).symm
    rw [hTy, Category.assoc (spMap fK), hyK]
    simp only [gen₀, ← Category.assoc]
    rw [hc]

end GlobalTheory.UTraitPt
