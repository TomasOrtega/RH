import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h`. Use `letI := Ideal.Quotient.field (RingHom.ker φ)`. Use `haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int`. Use `haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _`.

Use `haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance`. Conclude with `Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ) (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))`.
-/
theorem ker_eq_bot_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K]
    [CharZero K] (φ : o →+* K) : RingHom.ker φ = ⊥ := by
  by_contra h
  haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h
  letI := Ideal.Quotient.field (RingHom.ker φ)
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ)
    (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))

/- English proof (translation)
Use `haveI := C.ded`. Use `haveI := C.ft`. Take `⟨φ, rfl⟩` from `Spec.map_surjective x`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations.

Use `show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal`. Rewrite using `[Subsingleton.elim w (⊥ : PrimeSpectrum K)]`. Conclude with `((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm`.
-/
theorem UCompact.range_subset_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) {K : Type} [Field K] [CharZero K]
    (x : Sp K ⟶ Sp C.o) : Set.range x ⊆ Set.range (spMap C.b) := by
  haveI := C.ded
  haveI := C.ft
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  rintro _ ⟨w, rfl⟩
  refine ⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩
  show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal
  rw [Subsingleton.elim w (⊥ : PrimeSpectrum K)]
  exact ((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c C`. Use `letI := C.b.toAlgebra`. Use `haveI := C.isFractionRing`. Use `haveI := C.iF_open`. Use `haveI := C.ded`.

Use `haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)`. Establish `hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :)` using `(pullback.fst C.z (spMap C.b)).isEmbedding`. Take `⟨U, hU, hUe⟩` from `hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range`. Use `⟨⟨U, hU⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `: C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U` using `hUe ▸ ⟨x, rfl⟩`. Conclude with `this`. Introduce `p _ y hy`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :)`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩`. Take `⟨t, ht⟩` from `h1`. Establish `h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U` using `by show _ ∈ U`. Rewrite using `[ht]`.

Conclude with `hy ⟨w, rfl⟩`. Rewrite `h2` using `[hUe]`. Take `⟨x, rfl⟩` from `h2`. Conclude with `⟨x, ht⟩`.
-/
theorem exists_open_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  intro E _ _ _ H Dw l Xo c C
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨U, hU, hUe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := hUe ▸ ⟨x, rfl⟩
    exact this
  · intro p _ y hy
    rintro _ ⟨w, rfl⟩
    have h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :) := by
      rw [Scheme.Pullback.range_fst]
      exact C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := h1
    have h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := by
      show _ ∈ U
      rw [ht]
      exact hy ⟨w, rfl⟩
    rw [hUe] at h2
    obtain ⟨x, rfl⟩ := h2
    exact ⟨x, ht⟩

end GlobalTheory.UPoinc
