import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProperOfAbelianFibres
open IsLocalRing

/- English proof (translation)
Take `⟨x', hx', hfx'⟩` from `Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))`. Use `(Specializes.antisymm ?_ ?_).eq` and prove the remaining obligations. Rewrite using `[← hfx']`. Conclude with `(genericPoint_specializes x').map f.continuous`. Conclude with `genericPoint_specializes _`.
-/
theorem apply_genericPoint_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x', hx', hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  refine (Specializes.antisymm ?_ ?_).eq
  · rw [← hfx']
    exact (genericPoint_specializes x').map f.continuous
  · exact genericPoint_specializes _

/- English proof (translation)
Use `haveI := hW.1`. Use `haveI := hW.2.2`. Take `⟨l₁, l₂, -⟩` from `GlobalTheory.firstFiveLaws`. Establish `ht : ∀ z, z ∈ abLocus t.G` using `fun z => hab ▸ Set.mem_univ z`. Take `⟨P, -⟩` from `GlobalTheory.LN.uDvrSt_holds E H V hW t hP (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)`.

Establish `hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`. Use `infer_instance`. Establish `hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1))` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax`. Establish `p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))`.

Use `letI := hF.toField`. Conclude with `(default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))`. Set `g` to `P.U.gt 0`. Establish `: Mono g.i` using `⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩`. Establish `hs` using `GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick V (maximalIdeal V) 0) p (ht _) P.D.toPre.X g.i g.i_hom`.

Conclude with `(GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hW.2.1 P.D P.A t.G t.semi P.U hs).proper`.
-/
theorem isProper_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (hW : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V)) (hP : GlobalTheory.LN.PolAt t (jK V))
    (hab : abLocus t.G = Set.univ) : IsProper t.G.hom := by
  haveI := hW.1
  haveI := hW.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H V hW t hP (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick V (maximalIdeal V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hW.2.1 P.D P.A t.G t.semi P.U hs).proper

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ _ t hP hab`. Use `haveI : IsSemiAbelian t.G := t.semi`. Use `haveI := t.semi.separated`. Use `haveI := t.semi.quasiCompact`. Use `haveI := t.semi.smooth`.

Use `haveI : IsIntegral t.G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian t.G`. Use `GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R t.G.left t.G.hom ?_` and prove the remaining obligations. Introduce `V K _ _ _ _ _ _ _ x y hx hxy`. Take `⟨φ, rfl⟩ : ∃ φ : R →+* V, spMap φ = y` from `⟨(Spec.preimage y).hom, by simp [spMap]⟩`. Set `p₀ : Sp K` to `(⊥ : PrimeSpectrum K)`.

Establish `h₁ : x p₀ = genericPoint t.G.left` using `hx ⟨p₀, rfl⟩`. Establish `h₂ : (x ≫ t.G.hom) p₀ = (⊥ : PrimeSpectrum R)`. Rewrite using `[Scheme.Hom.comp_apply, h₁, apply_genericPoint_of_flat]`. Conclude with `genericPoint_eq_bot_of_affine (CommRingCat.of R)`. Rewrite `h₂` using `[hxy]`.

Establish `h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥` using `congrArg PrimeSpectrum.asIdeal h₂`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `: a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K))` using `by simp [ha]`.

Rewrite `this` using `[h₃]`. Simplify using `using this`. Use `haveI : CharZero V := charZero_of_injective_ringHom hinj`. Take `⟨tV, ⟨m⟩⟩` from `exists_sab (spMap φ) t`. Establish `hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ)` using `(IsFractionRing.injective V (FractionRing V)).comp hinj`.

Set `ψ : FractionRing R →+* FractionRing V` to `IsFractionRing.lift hinj'`. Establish `hg : spMap ψ ≫ jK R = jK V ≫ spMap φ`. Simplify using `only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`.

Simplify using `[ψ, IsFractionRing.lift_algebraMap]`. Establish `hPV : GlobalTheory.LN.PolAt tV (jK V)` using `GlobalTheory.DatUniq.polAt_pull m hP (jK V) (spMap ψ) hg`. Establish `habV : abLocus tV.G = Set.univ` using `Set.eq_univ_of_forall fun z => (abLocus_pullback abLocusOne t.semi m.cart.1 z).1 (hab ▸ Set.mem_univ _)`. Establish `hpV : IsProper tV.G.hom` using `isProper_dvr V ⟨inferInstance, inferInstance, inferInstance⟩ tV hPV habV`. Set `xV : Sp K ⟶ tV.G.left` to `m.cart.1.lift x (spMap (algebraMap V K)) hxy`.

Establish `hE : ValuativeCriterion.Existence tV.G.hom`. Establish `h : UniversallyClosed tV.G.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`. Set `S : ValuativeCommSq tV.G.hom` to `{ R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by simp [xV, spMap]⟩ }`.

Take `⟨l⟩` from `(hE S).exists_lift`. Use `⟨l.l ≫ m.cm.F, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc]`. Use `l.fac_left` as an intermediate fact. Express the relevant statement in the definitionally equal form `spMap (algebraMap V K) ≫ l.l = xV at this`.

Rewrite using `[this]`. Conclude with `m.cart.1.lift_fst _ _ _`.
-/
theorem isProper_of_polAt_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    abLocus t.G = Set.univ → IsProper t.G.hom := by
  intro E _ _ _ H R _ _ _ _ t hP hab
  haveI : IsSemiAbelian t.G := t.semi
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  haveI := t.semi.smooth
  haveI : IsIntegral t.G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian t.G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R t.G.left t.G.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* V, spMap φ = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint t.G.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ t.G.hom) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [hxy] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj

  obtain ⟨tV, ⟨m⟩⟩ := exists_sab (spMap φ) t
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hinj
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  have hPV : GlobalTheory.LN.PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull m hP (jK V) (spMap ψ) hg
  have habV : abLocus tV.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi m.cart.1 z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper tV.G.hom := isProper_dvr V ⟨inferInstance, inferInstance, inferInstance⟩ tV hPV habV

  let xV : Sp K ⟶ tV.G.left := m.cart.1.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence tV.G.hom := by
    have h : UniversallyClosed tV.G.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq tV.G.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by simp [xV, spMap]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ m.cm.F, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact m.cart.1.lift_fst _ _ _

end GlobalTheory.ProperOfAbelianFibres
