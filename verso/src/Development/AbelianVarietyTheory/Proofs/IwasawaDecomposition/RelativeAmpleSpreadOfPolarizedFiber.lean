import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolNearAmple

/- English proof (translation)
Introduce `E _ _ _ H R _ _ t hprop C _ g hpol`. Establish `: Smooth t.G.hom` using `t.semi.smooth`. Establish `: Flat t.G.hom` using `inferInstance`. Establish `hL` using `t.PP.isLB`. Set `p : Ideal R` to `RingHom.ker g`.

Use `haveI : p.IsPrime := RingHom.ker_isPrime g`. Set `g₀` to `algebraMap R p.ResidueField`. Establish `hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g` using `fun x hx => show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)`. Set `i : p.ResidueField →+* C` to `Ideal.ResidueField.lift p g le_rfl hf₂`. Establish `hcomp : i.comp g₀ = g` using `RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r`.

Establish `hsp : spMap i ≫ spMap g₀ = spMap g`. Rewrite using `[← hcomp]`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom (spMap i ≫ spMap g₀)`.

Rewrite using `[hsp]`. Conclude with `IsPullback.of_hasPullback _ _`. Establish `hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀)))` using `FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂ (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1`. Take `⟨s, hs, hAs⟩` from `ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁`. Use `⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩` and prove the remaining obligations.

Introduce `R' _ h hu t' m`. Set `D : (Sp R).Opens` to `PrimeSpectrum.basicOpen s`. Establish `: IsAffine D.toScheme` using `IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s`. Establish `hrange : Set.range (spMap h) ⊆ Set.range D.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Use `show s ∉ Ideal.comap h y.asIdeal`. Conclude with `fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)`. Set `u : Sp R' ⟶ D.toScheme` to `IsOpenImmersion.lift D.ι (spMap h) hrange`. Establish `hu' : u ≫ D.ι = spMap h` using `IsOpenImmersion.lift_fac _ _ _`.

Take `⟨φ, hφ, Hp⟩` from `FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'`. Establish `e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F)`. Take `⟨w, hw, -⟩` from `(isPullCubical_iff m.cm t.cub t'.cub).1 m.lin`. Conclude with `⟨w, (isGen_iff w).2 hw⟩`. Take `⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ)` from `LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀ (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))`.

Conclude with `relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs`.
-/
theorem relAmple_near_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ t hprop C _ g hpol
  have : Smooth t.G.hom := t.semi.smooth
  have : Flat t.G.hom := inferInstance
  have hL := t.PP.isLB
  let p : Ideal R := RingHom.ker g
  haveI : p.IsPrime := RingHom.ker_isPrime g
  let g₀ := algebraMap R p.ResidueField
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g := fun x hx =>
    show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)
  let i : p.ResidueField →+* C := Ideal.ResidueField.lift p g le_rfl hf₂
  have hcomp : i.comp g₀ = g := RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r
  have hsp : spMap i ≫ spMap g₀ = spMap g := by
    rw [← hcomp]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom
      (spMap i ≫ spMap g₀) := by
    rw [hsp]; exact IsPullback.of_hasPullback _ _
  have hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀))) :=
    FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂
      (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1
  obtain ⟨s, hs, hAs⟩ := ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁
  refine ⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩
  intro R' _ h hu t' m
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen s
  have : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s
  have hrange : Set.range (spMap h) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show s ∉ Ideal.comap h y.asIdeal
    exact fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)
  let u : Sp R' ⟶ D.toScheme := IsOpenImmersion.lift D.ι (spMap h) hrange
  have hu' : u ≫ D.ι = spMap h := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, Hp⟩ := FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'
  have e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact ⟨w, (isGen_iff w).2 hw⟩
  obtain ⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ) :=
    LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀
      (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))
  exact relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs

end GlobalTheory.PolNearAmple
