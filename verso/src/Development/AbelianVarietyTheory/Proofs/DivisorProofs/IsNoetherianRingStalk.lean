import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TraitCen

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]

/- English proof (translation)
Establish `: IsDedekindDomain o'` using `ArithBase.ded (Ω := Ω)`. Use `M.lft` as an intermediate fact. Establish `: IsLocallyNoetherian M.Z` using `LocallyOfFiniteType.isLocallyNoetherian M.s`. Use `infer_instance`.
-/
theorem isNoetherianRing_stalk (M : RatModel o' Ω) (x : M.Z) : IsNoetherianRing (M.Z.presheaf.stalk x) := by
  have : IsDedekindDomain o' := ArithBase.ded (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  infer_instance

/- English proof (translation)
The claim follows from `(M.stalkHom_injective x).isDomain _`.
-/
theorem isDomain_stalk (M : RatModel o' Ω) (x : M.Z) : IsDomain (M.Z.presheaf.stalk x) :=
  (M.stalkHom_injective x).isDomain _

/- English proof (translation)
Establish `: CharZero Ω` using `ArithBase.char (o := o')`. Conclude with `⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩`.
-/
theorem charZero_stalk (M : RatModel o' Ω) (x : M.Z) : CharZero (M.Z.presheaf.stalk x) := by
  have : CharZero Ω := ArithBase.char (o := o')
  exact ⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩

/- English proof (translation)
Set `O` to `M.Z.presheaf.stalk x`. Establish `: IsNoetherianRing O` using `isNoetherianRing_stalk M x`. Establish `: IsDomain O` using `isDomain_stalk M x`. Establish `: CharZero O` using `charZero_stalk M x`. Establish `hη : genericPoint M.Z ∈ U₀`.

Take `⟨z, hz⟩` from `hU`. Conclude with `(genericPoint_specializes z).mem_open U₀.isOpen hz`. Establish `h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `genericPoint_specializes x`.

Take `⟨q, hq⟩` from `h1`. Take `⟨_, ⟨f₀, rfl⟩, hqf, hf⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη) (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)`. Establish `hf₀ : f₀ ≠ 0` using `fun h => hqf (by simp [h])`. Set `κ` to `ResidueField (PowerSeries O)`. Set `p` to `ringChar κ`.

Set `c : PowerSeries O` to `if p = 0 then 1 else (p : PowerSeries O)`. Establish `hc0 : c ≠ 0`. Distinguish the cases in `hp : p = 0`. Simplify using `[c, hp]`. Simplify using `only [c, hp, if_false]`.

Rewrite using `[← map_natCast (PowerSeries.C (R := O))]`. Conclude with `(map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)`. Set `f : PowerSeries O` to `PowerSeries.X * PowerSeries.C f₀ * c`. Establish `hfm : f ∈ maximalIdeal (PowerSeries O)`. Use `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Establish `hf0 : f ∉ (⊥ : Ideal (PowerSeries O))`. Rewrite using `[Ideal.mem_bot]`. Conclude with `mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0`.

Set `φ : PowerSeries O →+* AlgebraicClosure κ` to `(algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))`. Take `⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩` from `GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ`. Set `ψ' : O →+* W` to `ψ.comp PowerSeries.C`. Establish `hψloc : IsLocalHom ψ` using `⟨fun a ha => isUnit_of_map_unit φ a (by`. Establish `h` using `(ha.map (residue W)).map ιk`.

Rewrite using `[← hψ]`. Conclude with `h)⟩`. Establish `hCloc : IsLocalHom (PowerSeries.C (R` using `O)) := ⟨fun a ha => by`. Simplify using `using ha.map (PowerSeries.constantCoeff (R := O))⟩`. Establish `hψ'loc : IsLocalHom ψ'` using `RingHom.isLocalHom_comp ψ _`.

Establish `hψ'f₀ : ψ' f₀ ≠ 0` using `fun h => hψf (by`. Simplify using `only [f, map_mul]`. Rewrite using `[show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])`. Establish `hcz : CharZero W`. Take `⟨q, hq⟩` from `CharP.exists W`.

Break down `CharP.char_is_prime_or_zero W q with hqp | hq0` into its components or cases. It suffices to derive a contradiction. Establish `hqW : (q : W) = 0` using `CharP.cast_eq_zero W q`. Establish `hqκ : (q : κ) = 0`. Establish `h` using `congrArg (ιk.comp (residue W)) hqW`.

Rewrite `h` using `[map_natCast, map_zero]`. Use `(map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_` and prove the remaining obligations. Rewrite using `[map_natCast]`. Conclude with `h`. Establish `: CharP κ q` using `(CharP.charP_iff_prime_eq_zero hqp).2 hqκ`.

Establish `hpq : p = q` using `ringChar.eq κ q`. Establish `hp : p ≠ 0` using `hpq ▸ hqp.ne_zero`. Apply `hψf` to reduce the goal to its premises. Establish `hc : c = (q : PowerSeries O)` using `by simp only [c, if_neg hp, hpq]`. Use `show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0`.

Rewrite using `[hc, map_mul, map_natCast, hqW, mul_zero]`. Substitute `hq0` using the available equality. Conclude with `CharP.charP_to_charZero W`. Set `a : Sp W ⟶ M.Z` to `Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x`. Use `⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩` and prove the remaining obligations.

Establish `h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O` using `IsLocalRing.comap_closedPoint ψ' show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x`. Rewrite using `[h, Scheme.fromSpecStalk_closedPoint]`. Establish `ht : (jK W) t = (⊥ : PrimeSpectrum W)`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥`.

Rewrite using `[@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)`. Establish `hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O))` using `by show f₀ ∉ Ideal.comap ψ' ⊥`. Rewrite using `[Ideal.mem_comap, Ideal.mem_bot]`. Conclude with `hψ'f₀`.

Use `hf hm` as an intermediate fact. Simplify using `only [a, Scheme.Hom.comp_apply, ht]`. Conclude with `this`.
-/
theorem exists_cdvr (M : RatModel o' Ω) (U₀ : M.Z.Opens) (hU : (U₀ : Set M.Z).Nonempty) (x : M.Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ M.Z),
      a (closedPoint W) = x ∧ ∀ t, (jK W ≫ a) t ∈ U₀ := by
  let O := M.Z.presheaf.stalk x
  have : IsNoetherianRing O := isNoetherianRing_stalk M x
  have : IsDomain O := isDomain_stalk M x
  have : CharZero O := charZero_stalk M x

  have hη : genericPoint M.Z ∈ U₀ := by
    obtain ⟨z, hz⟩ := hU
    exact (genericPoint_specializes z).mem_open U₀.isOpen hz
  have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨q, hq⟩ := h1
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη)
    (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)
  have hf₀ : f₀ ≠ 0 := fun h => hqf (by simp [h])

  let κ := ResidueField (PowerSeries O)
  let p := ringChar κ
  let c : PowerSeries O := if p = 0 then 1 else (p : PowerSeries O)
  have hc0 : c ≠ 0 := by
    by_cases hp : p = 0
    · simp [c, hp]
    · simp only [c, hp, if_false]
      rw [← map_natCast (PowerSeries.C (R := O))]
      exact (map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)
  let f : PowerSeries O := PowerSeries.X * PowerSeries.C f₀ * c
  have hfm : f ∈ maximalIdeal (PowerSeries O) := by
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hf0 : f ∉ (⊥ : Ideal (PowerSeries O)) := by
    rw [Ideal.mem_bot]
    exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0
  let φ : PowerSeries O →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))
  obtain ⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩ :=
    GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ
  let ψ' : O →+* W := ψ.comp PowerSeries.C
  have hψloc : IsLocalHom ψ := ⟨fun a ha => isUnit_of_map_unit φ a (by
    have h := (ha.map (residue W)).map ιk
    rw [← hψ]
    exact h)⟩
  have hCloc : IsLocalHom (PowerSeries.C (R := O)) := ⟨fun a ha => by
    simpa using ha.map (PowerSeries.constantCoeff (R := O))⟩
  have hψ'loc : IsLocalHom ψ' := RingHom.isLocalHom_comp ψ _
  have hψ'f₀ : ψ' f₀ ≠ 0 := fun h => hψf (by
    simp only [f, map_mul]
    rw [show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])
  have hcz : CharZero W := by
    obtain ⟨q, hq⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W q with hqp | hq0
    · exfalso
      have hqW : (q : W) = 0 := CharP.cast_eq_zero W q
      have hqκ : (q : κ) = 0 := by
        have h := congrArg (ιk.comp (residue W)) hqW
        rw [map_natCast, map_zero] at h
        refine (map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_
        rw [map_natCast]
        exact h
      have : CharP κ q := (CharP.charP_iff_prime_eq_zero hqp).2 hqκ
      have hpq : p = q := ringChar.eq κ q
      have hp : p ≠ 0 := hpq ▸ hqp.ne_zero
      apply hψf
      have hc : c = (q : PowerSeries O) := by simp only [c, if_neg hp, hpq]
      show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0
      rw [hc, map_mul, map_natCast, hqW, mul_zero]
    · subst hq0
      exact CharP.charP_to_charZero W
  let a : Sp W ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩
  · have h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O := IsLocalRing.comap_closedPoint ψ'
    show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · have ht : (jK W) t = (⊥ : PrimeSpectrum W) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    have hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O)) := by
      show f₀ ∉ Ideal.comap ψ' ⊥
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact hψ'f₀
    have := hf hm
    simp only [a, Scheme.Hom.comp_apply, ht]
    exact this

/- English proof (translation)
Introduce `g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _`. Take `⟨W, _, _, _, _, hc, a, ha, hg⟩` from `exists_cdvr M U₀ hU x`. Establish `hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨t, rfl⟩`.

Conclude with `hg t`. Set `ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme` to `IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr`. Establish `hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hB : GlobalTheory.Mum.Base W` using `⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩`. Take `⟨T, f, fK, -, hloc, -, hcomp, hy⟩` from `GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)`.

Use `⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `r`. Conclude with `hcomp r`. Rewrite using `[hy, Category.assoc]`. Establish `h : (spMap f) (closedPoint T.V) = closedPoint W` using `IsLocalRing.comap_closedPoint f show a ((spMap f) (closedPoint T.V)) = x`. Rewrite using `[h, ha]`.
-/
theorem exists_trait_cen : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o']
    [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty →
    ∀ (X : Scheme.{0}) (u₀ : U₀.toScheme ⟶ X) (u : X ⟶ F.X) (x : M.Z), IsClosed ({x} : Set M.Z) →
      ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ u T ξ ∧ ξ (IsLocalRing.closedPoint T.V) = x := by
  intro g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [hy, Category.assoc]
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.Poinc.TraitCen
