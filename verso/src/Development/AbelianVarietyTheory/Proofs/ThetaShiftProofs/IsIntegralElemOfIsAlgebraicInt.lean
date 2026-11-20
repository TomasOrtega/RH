import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.ArcConst

def AlgZ {A : Type} [CommRing A] (s : A) : Prop := IsAlgebraic ℤ s

/- English proof (translation)
Take `rfl : inst = Ring.toIntAlgebra A` from `Subsingleton.elim _ _`. Conclude with `h`.
-/
theorem algZ_of {A : Type} [CommRing A] [inst : Algebra ℤ A] {s : A} (h : IsAlgebraic ℤ s) : AlgZ s := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact h

/- English proof (translation)
The claim follows from `IsAlgebraic.algHom f.toIntAlgHom h`.
-/
theorem AlgZ.map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {s : A} (h : AlgZ s) : AlgZ (f s) :=
  IsAlgebraic.algHom f.toIntAlgHom h

/- English proof (translation)
The claim follows from `IsAlgebraic.sub (R := ℤ) h h'`.
-/
theorem AlgZ.sub {A : Type} [CommRing A] {s t : A} (h : AlgZ s) (h' : AlgZ t) : AlgZ (s - t) :=
  IsAlgebraic.sub (R := ℤ) h h'

/- English proof (translation)
Set `` to `f.toAlgebra`. Establish `h : IsAlgebraic K s` using `IsAlgebraic.extendScalars (R := ℤ) (A_alg := hs) (RingHom.injective_int (algebraMap ℤ K))`. Conclude with `h.isIntegral`.
-/
theorem isIntegralElem_of_isAlgebraic_int {K A : Type} [Field K] [CharZero K] [CommRing A] (f : K →+* A)
    {s : A} (hs : AlgZ s) : f.IsIntegralElem s := by
  let := f.toAlgebra
  have h : IsAlgebraic K s := IsAlgebraic.extendScalars (R := ℤ) (A_alg := hs) (RingHom.injective_int (algebraMap ℤ K))
  exact h.isIntegral

/- English proof (translation)
Set `` to `f.toAlgebra`. Conclude with `IsIntegral.isUnit (R := K) hs h0`.
-/
theorem isUnit_of_isIntegralElem {K A : Type} [Field K] [CommRing A] [IsDomain A] (f : K →+* A)
    {s : A} (hs : f.IsIntegralElem s) (h0 : s ≠ 0) : IsUnit s := by
  let := f.toAlgebra
  exact IsIntegral.isUnit (R := K) hs h0

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R S)` using `IsLocalization.injective S hM`. Establish `h1 : ((algebraMap R S).comp f).IsIntegralElem s` using `isIntegralElem_of_isAlgebraic_int _ hs`. Establish `h2 : IsIntegral R s`. Take `⟨p, hp, hp0⟩` from `h1`. Conclude with `⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hp0⟩`.

Set `g : S →ₐ[R] FractionRing R` to `IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R (FractionRing R)) (fun y => IsLocalization.map_units (M := nonZeroDivisors R) (FractionRing R) ⟨y.1, hM y.2⟩)`. Establish `hg : Function.Injective g`. Set `: Algebra S (FractionRing R)` to `g.toRingHom.toAlgebra`. Establish `: IsScalarTower R S (FractionRing R)` using `IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm`. Establish `: IsFractionRing S (FractionRing R)` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S (FractionRing R)`.

Conclude with `IsFractionRing.injective S (FractionRing R)`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (h2.map g)`. Establish `hrs : algebraMap R S r = s` using `hg (by rw [g.commutes]; exact hr)`. Use `⟨r, hrs, ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[← hrs]`.

Conclude with `(isAlgebraic_algHom_iff (algebraMap R S).toIntAlgHom hinj).1 hs`.
-/
theorem exists_of_localization {K R S : Type} [Field K] [CharZero K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (f : K →+* R)
    {s : S} (hs : AlgZ s) : ∃ r : R, algebraMap R S r = s ∧ AlgZ r := by
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have h1 : ((algebraMap R S).comp f).IsIntegralElem s := isIntegralElem_of_isAlgebraic_int _ hs
  have h2 : IsIntegral R s := by
    obtain ⟨p, hp, hp0⟩ := h1
    exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hp0⟩
  let g : S →ₐ[R] FractionRing R := IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R (FractionRing R))
    (fun y => IsLocalization.map_units (M := nonZeroDivisors R) (FractionRing R) ⟨y.1, hM y.2⟩)
  have hg : Function.Injective g := by
    let : Algebra S (FractionRing R) := g.toRingHom.toAlgebra
    have : IsScalarTower R S (FractionRing R) := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
    have : IsFractionRing S (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S (FractionRing R)
    exact IsFractionRing.injective S (FractionRing R)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h2.map g)
  have hrs : algebraMap R S r = s := hg (by rw [g.commutes]; exact hr)
  refine ⟨r, hrs, ?_⟩
  rw [← hrs] at hs
  exact (isAlgebraic_algHom_iff (algebraMap R S).toIntAlgHom hinj).1 hs

/- English proof (translation)
Use `⟨PowerSeries.constantCoeff p, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h1 : AlgZ (PowerSeries.C (R` using `K) (PowerSeries.constantCoeff p)) := (hp.map (PowerSeries.constantCoeff (R := K))).map (PowerSeries.C (R := K))`. Establish `h2` using `isUnit_of_isIntegralElem _ (isIntegralElem_of_isAlgebraic_int (PowerSeries.C (R := K)) (hp.sub h1)) (sub_ne_zero.2 hne)`. Establish `h3` using `h2.map (PowerSeries.constantCoeff (R := K))`.

Simplify using `at h3`.
-/
theorem powerSeries_const {K : Type} [Field K] [CharZero K] {p : PowerSeries K} (hp : AlgZ p) :
    ∃ x : K, p = PowerSeries.C (R := K) x := by
  refine ⟨PowerSeries.constantCoeff p, ?_⟩
  by_contra hne
  have h1 : AlgZ (PowerSeries.C (R := K) (PowerSeries.constantCoeff p)) :=
    (hp.map (PowerSeries.constantCoeff (R := K))).map (PowerSeries.C (R := K))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (PowerSeries.C (R := K)) (hp.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (PowerSeries.constantCoeff (R := K))
  simp at h3

/- English proof (translation)
Use `⟨MvPolynomial.constantCoeff P, ?_, hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h1 : AlgZ (MvPolynomial.C (σ` using `σ) (MvPolynomial.constantCoeff P)) := (hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))).map (MvPolynomial.C (σ := σ) (R := L))`. Establish `h2` using `isUnit_of_isIntegralElem _ (isIntegralElem_of_isAlgebraic_int (MvPolynomial.C (σ := σ) (R := L)) (hP.sub h1)) (sub_ne_zero.2 hne)`. Establish `h3` using `h2.map (MvPolynomial.constantCoeff (R := L) (σ := σ))`.

Simplify using `at h3`.
-/
theorem mvPolynomial_const {σ L : Type} [Field L] [CharZero L] {P : MvPolynomial σ L} (hP : AlgZ P) :
    ∃ y : L, P = MvPolynomial.C y ∧ AlgZ y := by
  refine ⟨MvPolynomial.constantCoeff P, ?_, hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))⟩
  by_contra hne
  have h1 : AlgZ (MvPolynomial.C (σ := σ) (MvPolynomial.constantCoeff P)) :=
    (hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))).map (MvPolynomial.C (σ := σ) (R := L))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (MvPolynomial.C (σ := σ) (R := L)) (hP.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (MvPolynomial.constantCoeff (R := L) (σ := σ))
  simp at h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Introduce `h0`. Establish `h` using `congrArg (MvPolynomial.eval (fun t : ArcLt Dw => if t.2.1 = t.2.2 then (1 : LaurentSeries K) else 0)) h0`. Rewrite `h` using `[arcDet, map_prod, map_zero, Finset.prod_eq_one]`. Conclude with `one_ne_zero h`. Introduce `τ _`.

Rewrite using `[RingHom.map_det]`. Use `Matrix.det_one (n := Fin (Dw.mult τ)) (R := LaurentSeries K)` and compare the differences between its conclusion and the goal. Use `ext1 i k`. Simplify using `[Matrix.one_apply]`.
-/
theorem arcDet_ne_zero (Dw : Datum H) (K : Type) [Field K] : arcDet Dw K ≠ 0 := by
  classical
  intro h0
  have h := congrArg (MvPolynomial.eval (fun t : ArcLt Dw => if t.2.1 = t.2.2 then (1 : LaurentSeries K) else 0)) h0
  rw [arcDet, map_prod, map_zero, Finset.prod_eq_one] at h
  · exact one_ne_zero h
  · intro τ _
    rw [RingHom.map_det]
    convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := LaurentSeries K)
    ext1 i k
    simp [Matrix.one_apply]

/- English proof (translation)
The claim follows from `IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) (S := ArcS Dw K) (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))`.
-/
theorem algebraMap_injective (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
  IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) (S := ArcS Dw K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))

/- English proof (translation)
The claim follows from `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))`.
-/
theorem isDomain (Dw : Datum H) (K : Type) [Field K] : IsDomain (ArcS Dw K) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))

/- English proof (translation)
The claim follows from `have := isDomain Dw K RingHom.injective _`.
-/
theorem arcι_C_injective (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective ((arcι Dw K).comp (PowerSeries.C (R := K))) :=
  have := isDomain Dw K
  RingHom.injective _

/- English proof (translation)
Establish `: CharZero (LaurentSeries K)` using `(HahnSeries.C : K →+* LaurentSeries K).charZero_iff (RingHom.injective _) |>.1 ‹_›`. Establish `: IsIntegrallyClosed (MvPolynomial (ArcLt Dw) (LaurentSeries K))` using `inferInstance`. Take `⟨P, hP, hPa⟩` from `exists_of_localization (K := LaurentSeries K) (R := MvPolynomial (ArcLt Dw) (LaurentSeries K)) (S := ArcS Dw K) (Submonoid.powers (arcDet Dw K)) (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K)) MvPolynomial.C hs`. Take `⟨y, rfl, hy⟩` from `mvPolynomial_const hPa`. Take `⟨p, hp, hpa⟩` from `exists_of_localization (K := K) (R := PowerSeries K) (nonZeroDivisors _) le_rfl (PowerSeries.C (R := K)) hy`.

Take `⟨x, rfl⟩` from `powerSeries_const hpa`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hP, ← hp]`. Both sides reduce to the same expression.
-/
theorem exists_const (Dw : Datum H) (K : Type) [Field K] [CharZero K] (s : ArcS Dw K) (hs : AlgZ s) :
    ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x) := by
  have : CharZero (LaurentSeries K) := (HahnSeries.C : K →+* LaurentSeries K).charZero_iff (RingHom.injective _) |>.1 ‹_›
  have : IsIntegrallyClosed (MvPolynomial (ArcLt Dw) (LaurentSeries K)) := inferInstance
  obtain ⟨P, hP, hPa⟩ := exists_of_localization (K := LaurentSeries K) (R := MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (S := ArcS Dw K) (Submonoid.powers (arcDet Dw K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K)) MvPolynomial.C hs
  obtain ⟨y, rfl, hy⟩ := mvPolynomial_const hPa
  obtain ⟨p, hp, hpa⟩ := exists_of_localization (K := K) (R := PowerSeries K) (nonZeroDivisors _) le_rfl
    (PowerSeries.C (R := K)) hy
  obtain ⟨x, rfl⟩ := powerSeries_const hpa
  refine ⟨x, ?_⟩
  rw [← hP, ← hp]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw K _ _`. Use `⟨isDomain Dw K, algebraMap_injective Dw K, fun s hs => exists_const Dw K s (algZ_of hs), fun F _ _ f => ?_⟩` and prove the remaining obligations. Establish `hinj` using `arcι_C_injective Dw K`. Establish `hex : ∀ a : F, ∃ x : K, ((arcι Dw K).comp (PowerSeries.C (R` using `K))) x = f a := fun a => by`. Establish `ha : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)`.

Take `⟨x, hx⟩` from `exists_const Dw K (f a) ((algZ_of ha).map f)`. Conclude with `⟨x, hx.symm⟩`. Use `choose g hg using hex`. Use `⟨{ toFun := g, map_one' := hinj ?_, map_mul' := fun a b => hinj ?_, map_zero' := hinj ?_, map_add' := fun a b => hinj ?_ }, RingHom.ext fun a => (hg a).symm⟩` and prove the remaining obligations. Rewrite using `[hg, map_one, map_one]`.

Rewrite using `[hg, map_mul, map_mul, hg, hg]`. Rewrite using `[hg, map_zero, map_zero]`. Rewrite using `[hg, map_add, map_add, hg, hg]`.
-/
theorem algebraic_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] [CharZero K], IsDomain (ArcS Dw K) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) ∧ (∀ s : ArcS Dw K, IsAlgebraic ℤ s → ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x)) ∧ ∀ (F : Type) [Field F] [NumberField F] (f : F →+* ArcS Dw K), ∃ f₀ : F →+* K, f = ((arcι Dw K).comp (PowerSeries.C (R := K))).comp f₀ := by
  intro E _ _ _ H Dw K _ _
  refine ⟨isDomain Dw K, algebraMap_injective Dw K, fun s hs => exists_const Dw K s (algZ_of hs), fun F _ _ f => ?_⟩
  have hinj := arcι_C_injective Dw K
  have hex : ∀ a : F, ∃ x : K, ((arcι Dw K).comp (PowerSeries.C (R := K))) x = f a := fun a => by
    have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨x, hx⟩ := exists_const Dw K (f a) ((algZ_of ha).map f)
    exact ⟨x, hx.symm⟩
  choose g hg using hex
  refine ⟨{ toFun := g, map_one' := hinj ?_, map_mul' := fun a b => hinj ?_, map_zero' := hinj ?_,
            map_add' := fun a b => hinj ?_ }, RingHom.ext fun a => (hg a).symm⟩
  · rw [hg, map_one, map_one]
  · rw [hg, map_mul, map_mul, hg, hg]
  · rw [hg, map_zero, map_zero]
  · rw [hg, map_add, map_add, hg, hg]

end GlobalTheory.ArcConst
