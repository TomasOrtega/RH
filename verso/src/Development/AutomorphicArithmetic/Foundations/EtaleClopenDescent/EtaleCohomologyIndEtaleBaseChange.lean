import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalAffineIndEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsingStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHoldOfSheafAxi
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace UpperTheory.Cb.C3

section Neg

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : H R E F n, x = 0`. Introduce `x`. Take `⟨x, rfl⟩` from `x.mk_surjective`. Establish `hx : x = 0`.

Apply `CochainComplex.HomComplex.Cocycle.ext` to reduce the goal to its premises. Apply `CochainComplex.HomComplex.Cochain.ext` to reduce the goal to its premises. Introduce `p q' hpq`. Distinguish the cases in `hp : 0 < p`. Use `IsZero.eq_of_src ?_ _ _` and prove the remaining obligations.

Use `HomologicalComplex.isZero_extend_X _ _ _ ?_` and prove the remaining obligations. Introduce `j hj`. Simplify using `at hj`. Use linear arithmetic over natural numbers and integers. Use `IsZero.eq_of_tgt ?_ _ _` and prove the remaining obligations.

Use `HomologicalComplex.isZero_extend_X _ _ _ ?_` and prove the remaining obligations. Introduce `j hj`. Simplify using `at hj`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hx]`.

Conclude with `CochainComplex.HomComplex.CohomologyClass.mk_zero _ _ _`. Rewrite using `[key x, key y]`.
-/
theorem h_neg (R : Type) [CommRing R] (E : Spc) (F : Shv R) (n : ℤ) (hn : n < 0) :
    Subsingleton (H R E F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ x : H R E F n, x = 0 := by
    intro x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    have hx : x = 0 := by
      apply CochainComplex.HomComplex.Cocycle.ext
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q' hpq
      by_cases hp : 0 < p
      · refine IsZero.eq_of_src ?_ _ _
        refine HomologicalComplex.isZero_extend_X _ _ _ ?_
        intro j hj
        simp at hj
        omega
      · refine IsZero.eq_of_tgt ?_ _ _
        refine HomologicalComplex.isZero_extend_X _ _ _ ?_
        intro j hj
        simp at hj
        omega
    rw [hx]
    exact CochainComplex.HomComplex.CohomologyClass.mk_zero _ _ _
  rw [key x, key y]

end Neg

section Alg

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing T)]`. Introduce `x hx`. Take `⟨p, hp, hpx⟩` from `hx`. Proceed by induction on `hn : p.natDegree using Nat.strong_induction_on generalizing p with`. Consider the case `_ n ih`.

Distinguish the cases in `h0 : 0 < p.natDegree`. Take `⟨a, ha⟩` from `hT p hp h0`. Take `⟨r, hr⟩` from `Polynomial.dvd_iff_isRoot.2 ha`. Establish `hrm : r.Monic`. Use `hp` as an intermediate fact.

Rewrite `this` using `[hr]`. Conclude with `(Polynomial.monic_X_sub_C a).of_mul_monic_left this`. Establish `hdeg : p.natDegree = 1 + r.natDegree`. Rewrite using `[hr, (Polynomial.monic_X_sub_C a).natDegree_mul hrm, Polynomial.natDegree_X_sub_C]`. Rewrite `hpx` using `[hr, Polynomial.eval₂_mul]`.

Break down `mul_eq_zero.1 hpx with h | h` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h' : x - algebraMap T (FractionRing T) a = 0` using `by simpa using h`. Conclude with `(sub_eq_zero.1 h').symm`. Conclude with `ih r.natDegree (by omega) r hrm h rfl`.

Establish `: p = 1`. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0)]`. Use `hp.coeff_natDegree` as an intermediate fact. Rewrite `this` using `[show p.natDegree = 0 by omega]`. Rewrite using `[this, map_one]`.

Rewrite `hpx` using `[this]`. Simplify using `at hpx`.
-/
theorem aic_intClosed (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : 0 < p.natDegree
    · obtain ⟨a, ha⟩ := hT p hp h0
      obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.2 ha
      have hrm : r.Monic := by
        have := hp
        rw [hr] at this
        exact (Polynomial.monic_X_sub_C a).of_mul_monic_left this
      have hdeg : p.natDegree = 1 + r.natDegree := by
        rw [hr, (Polynomial.monic_X_sub_C a).natDegree_mul hrm, Polynomial.natDegree_X_sub_C]
      rw [hr, Polynomial.eval₂_mul] at hpx
      rcases mul_eq_zero.1 hpx with h | h
      · refine ⟨a, ?_⟩
        have h' : x - algebraMap T (FractionRing T) a = 0 := by simpa using h
        exact (sub_eq_zero.1 h').symm
      · exact ih r.natDegree (by omega) r hrm h rfl
    · have : p = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0)]
        have := hp.coeff_natDegree
        rw [show p.natDegree = 0 by omega] at this
        rw [this, map_one]
      rw [this] at hpx
      simp at hpx

/- English proof (translation)
Use `haveI : NeZero (q : T) := ⟨hq.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by`. Rewrite using `[Polynomial.natDegree_cyclotomic]`. Conclude with `Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))`. Conclude with `⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩`.
-/
theorem aic_root (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) (hq : IsUnit (q : T)) :
    ∃ ζ : T, IsPrimitiveRoot ζ q := by
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by
    rw [Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

/- English proof (translation)
Use `haveI : NeZero (q : T) := ⟨hqT.ne_zero⟩`. Use `haveI : NeZero (q : A) := ⟨hq.ne_zero⟩`. Establish `h0 : (Polynomial.cyclotomic q T).IsRoot ζ` using `Polynomial.isRoot_cyclotomic_iff.2 hζ`. Establish `h1` using `h0.map (f := f)`. Rewrite `h1` using `[Polynomial.map_cyclotomic]`.

Conclude with `Polynomial.isRoot_cyclotomic_iff.1 h1`.
-/
theorem root_map (q : ℕ) [NeZero q] {T A : Type} [CommRing T] [IsDomain T] [CommRing A] [IsDomain A] (f : T →+* A)
    (hqT : IsUnit (q : T)) (hq : IsUnit (q : A)) {ζ : T} (hζ : IsPrimitiveRoot ζ q) : IsPrimitiveRoot (f ζ) q := by
  haveI : NeZero (q : T) := ⟨hqT.ne_zero⟩
  haveI : NeZero (q : A) := ⟨hq.ne_zero⟩
  have h0 : (Polynomial.cyclotomic q T).IsRoot ζ := Polynomial.isRoot_cyclotomic_iff.2 hζ
  have h1 := h0.map (f := f)
  rw [Polynomial.map_cyclotomic] at h1
  exact Polynomial.isRoot_cyclotomic_iff.1 h1

section Ind

variable {T B A : Type} [CommRing T] [CommRing B] [CommRing A] [Algebra T B] [Algebra B A]

/- English proof (translation)
Take `⟨J, _, _, D, t, s, hs, hj⟩` from `h`. Establish `key : ∀ (l : J) (x y : D.obj l), x * y = 0 → (s.app l).hom x = 0 ∨ (s.app l).hom y = 0`. Introduce `l x y hxy`. Use `letI : Algebra B (D.obj l) := (t.app l).hom.toAlgebra`. Use `haveI : Algebra.Etale B (D.obj l) := (hj l).1`.

Use `letI : Algebra T (D.obj l) := ((algebraMap B (D.obj l)).comp (algebraMap T B)).toAlgebra`. Use `haveI : IsScalarTower T B (D.obj l) := .of_algebraMap_eq' rfl`. Use `haveI : Algebra.Smooth T (D.obj l) := Algebra.Smooth.comp T B (D.obj l)`. Set `p : Ideal (D.obj l)` to `(IsLocalRing.maximalIdeal A).comap (s.app l).hom`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`.

Use `haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth T p (Localization.AtPrime p)).1`. Establish `hz : ∀ z : D.obj l, algebraMap (D.obj l) (Localization.AtPrime p) z = 0 → (s.app l).hom z = 0`. Introduce `z hz`. Take `⟨u, hu⟩` from `(IsLocalization.map_eq_zero_iff p.primeCompl _ z).1 hz`. Establish `hu1 : IsUnit ((s.app l).hom (u : D.obj l))`.

Assume the negation of the conclusion as `hc`. Conclude with `u.2 ((IsLocalRing.mem_maximalIdeal _).2 hc)`. Use `congrArg (s.app l).hom hu` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero]`. Conclude with `(hu1.mul_right_eq_zero).1 this`.

Establish `h0 : algebraMap (D.obj l) (Localization.AtPrime p) x * algebraMap (D.obj l) (Localization.AtPrime p) y = 0`. Rewrite using `[← map_mul, hxy, map_zero]`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `Or.inl (hz _ h)`. Conclude with `Or.inr (hz _ h)`.

Establish `hnat : ∀ {i k : J} (f : i ⟶ k) (x : D.obj i), (s.app k).hom ((D.map f).hom x) = (s.app i).hom x`. Introduce `i k f x`. Use `s.naturality f` as an intermediate fact. Simplify using `only [Functor.const_obj_map, Category.comp_id] at this`. Conclude with `congrArg (fun g => g.hom x) this`.

Use `haveI : NoZeroDivisors A := ⟨by`. Introduce `a b hab`. Take `⟨i, x, hx⟩` from `Concrete.isColimit_exists_rep D hs a`. Take `⟨i', y, hy⟩` from `Concrete.isColimit_exists_rep D hs b`. Set `x'` to `(D.map (IsFiltered.leftToMax i i')).hom x`.

Set `y'` to `(D.map (IsFiltered.rightToMax i i')).hom y`. Establish `hx' : (s.app _).hom x' = a` using `(hnat (IsFiltered.leftToMax i i') x).trans hx`. Establish `hy' : (s.app _).hom y' = b` using `(hnat (IsFiltered.rightToMax i i') y).trans hy`. Establish `h0 : (s.app (IsFiltered.max i i')).hom (x' * y') = (s.app (IsFiltered.max i i')).hom 0`. Rewrite using `[map_mul, hx', hy', hab, map_zero]`.

Take `⟨l, f, g, hfg⟩` from `Concrete.isColimit_exists_of_rep_eq D hs _ _ h0`. Establish `hfg' : (D.map f).hom x' * (D.map f).hom y' = 0`. Rewrite using `[← map_mul]`. Use `(show _ = (D.map g).hom 0 from hfg).trans (map_zero _)` and prove the remaining obligations. Break down `key l _ _ hfg' with h | h` into its components or cases.

Conclude with `Or.inl (by rw [← hx', ← hnat f]; exact h)`. Conclude with `Or.inr (by rw [← hy', ← hnat f]; exact h)⟩`. Conclude with `NoZeroDivisors.to_isDomain A`.
-/
theorem indEt_isDomain [IsDomain T] [IsIntegrallyClosed T] [Algebra.Smooth T B] [IsLocalRing A] (h : IndEt B A) :
    IsDomain A := by
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  have key : ∀ (l : J) (x y : D.obj l), x * y = 0 → (s.app l).hom x = 0 ∨ (s.app l).hom y = 0 := by
    intro l x y hxy
    letI : Algebra B (D.obj l) := (t.app l).hom.toAlgebra
    haveI : Algebra.Etale B (D.obj l) := (hj l).1
    letI : Algebra T (D.obj l) := ((algebraMap B (D.obj l)).comp (algebraMap T B)).toAlgebra
    haveI : IsScalarTower T B (D.obj l) := .of_algebraMap_eq' rfl
    haveI : Algebra.Smooth T (D.obj l) := Algebra.Smooth.comp T B (D.obj l)
    let p : Ideal (D.obj l) := (IsLocalRing.maximalIdeal A).comap (s.app l).hom
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth T p (Localization.AtPrime p)).1
    have hz : ∀ z : D.obj l, algebraMap (D.obj l) (Localization.AtPrime p) z = 0 → (s.app l).hom z = 0 := by
      intro z hz
      obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ z).1 hz
      have hu1 : IsUnit ((s.app l).hom (u : D.obj l)) := by
        by_contra hc
        exact u.2 ((IsLocalRing.mem_maximalIdeal _).2 hc)
      have := congrArg (s.app l).hom hu
      rw [map_mul, map_zero] at this
      exact (hu1.mul_right_eq_zero).1 this
    have h0 : algebraMap (D.obj l) (Localization.AtPrime p) x * algebraMap (D.obj l) (Localization.AtPrime p) y = 0 := by
      rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (hz _ h)
    · exact Or.inr (hz _ h)
  have hnat : ∀ {i k : J} (f : i ⟶ k) (x : D.obj i), (s.app k).hom ((D.map f).hom x) = (s.app i).hom x := by
    intro i k f x
    have := s.naturality f
    simp only [Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g => g.hom x) this
  haveI : NoZeroDivisors A := ⟨by
    intro a b hab
    obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep D hs a
    obtain ⟨i', y, hy⟩ := Concrete.isColimit_exists_rep D hs b
    let x' := (D.map (IsFiltered.leftToMax i i')).hom x
    let y' := (D.map (IsFiltered.rightToMax i i')).hom y
    have hx' : (s.app _).hom x' = a := (hnat (IsFiltered.leftToMax i i') x).trans hx
    have hy' : (s.app _).hom y' = b := (hnat (IsFiltered.rightToMax i i') y).trans hy
    have h0 : (s.app (IsFiltered.max i i')).hom (x' * y') = (s.app (IsFiltered.max i i')).hom 0 := by
      rw [map_mul, hx', hy', hab, map_zero]
    obtain ⟨l, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hs _ _ h0
    have hfg' : (D.map f).hom x' * (D.map f).hom y' = 0 := by
      rw [← map_mul]
      refine (show _ = (D.map g).hom 0 from hfg).trans (map_zero _)
    rcases key l _ _ hfg' with h | h
    · exact Or.inl (by rw [← hx', ← hnat f]; exact h)
    · exact Or.inr (by rw [← hy', ← hnat f]; exact h)⟩
  exact NoZeroDivisors.to_isDomain A

/- English proof (translation)
Take `⟨J, i1, i2, D, t, s, hs, hj⟩` from `h`. Use `⟨J, i1, i2, D, (Functor.const J).map (CommRingCat.ofHom (algebraMap P B)) ≫ t, s, hs, fun j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `letI : Algebra B (D.obj j) := (t.app j).hom.toAlgebra haveI : Algebra.Etale B (D.obj j) := (hj j).1`. Use `letI : Algebra P (D.obj j) := ((algebraMap B (D.obj j)).comp (algebraMap P B)).toAlgebra`. Use `haveI : IsScalarTower P B (D.obj j) := .of_algebraMap_eq' rfl`.

Establish `: Algebra.Etale P (D.obj j)` using `Algebra.Etale.comp P B (D.obj j)`. Conclude with `this`. Establish `h2` using `(hj j).2`. Rewrite using `[NatTrans.comp_app, Category.assoc, h2]`. Use extensionality with `x`.

Conclude with `(IsScalarTower.algebraMap_apply P B A x).symm`.
-/
theorem indEt_comp {P : Type} [CommRing P] [Algebra P B] [Algebra.Etale P B] [Algebra P A] [IsScalarTower P B A]
    (h : IndEt B A) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap P A) := by
  obtain ⟨J, i1, i2, D, t, s, hs, hj⟩ := h
  refine ⟨J, i1, i2, D, (Functor.const J).map (CommRingCat.ofHom (algebraMap P B)) ≫ t, s, hs, fun j => ⟨?_, ?_⟩⟩
  · letI : Algebra B (D.obj j) := (t.app j).hom.toAlgebra
    haveI : Algebra.Etale B (D.obj j) := (hj j).1
    letI : Algebra P (D.obj j) := ((algebraMap B (D.obj j)).comp (algebraMap P B)).toAlgebra
    haveI : IsScalarTower P B (D.obj j) := .of_algebraMap_eq' rfl
    have : Algebra.Etale P (D.obj j) := Algebra.Etale.comp P B (D.obj j)
    exact this
  · have h2 := (hj j).2
    rw [NatTrans.comp_app, Category.assoc, h2]
    ext x
    exact (IsScalarTower.algebraMap_apply P B A x).symm

end Ind

end Alg

section Ind2

variable {T B A : Type} [CommRing T] [CommRing B] [CommRing A] [Algebra T B] [Algebra B A]

/- English proof (translation)
Use `haveI : Module.Flat B A := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h`. Use `haveI : Module.Flat T A := Module.Flat.trans T B A`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Assume the negation of the conclusion as `h0`.

Establish `hreg : IsSMulRegular A t` using `Module.Flat.isSMulRegular_of_isRegular (isRegular_of_ne_zero h0)`. Establish `h3 : (1 : A) = 0`. Apply `hreg` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `t • (1 : A) = t • (0 : A)`. Rewrite using `[Algebra.smul_def, ht, smul_zero, mul_one]`.

Conclude with `one_ne_zero h3`.
-/
theorem indEt_inj [IsDomain T] [Algebra.Smooth T B] [Algebra T A] [IsScalarTower T B A] [Nontrivial A]
    (h : IndEt B A) : Function.Injective (algebraMap T A) := by
  haveI : Module.Flat B A := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  haveI : Module.Flat T A := Module.Flat.trans T B A
  rw [injective_iff_map_eq_zero]
  intro t ht
  by_contra h0
  have hreg : IsSMulRegular A t := Module.Flat.isSMulRegular_of_isRegular (isRegular_of_ne_zero h0)
  have h3 : (1 : A) = 0 := by
    apply hreg
    change t • (1 : A) = t • (0 : A)
    rw [Algebra.smul_def, ht, smul_zero, mul_one]
  exact one_ne_zero h3

/- English proof (translation)
Take `⟨J, _, _, D, t, s, hs, hj⟩` from `indEt_comp (P := P) h`. Take `⟨j, x, hx⟩` from `Concrete.isColimit_exists_rep D hs a`. Use `letI : Algebra P (D.obj j) := (t.app j).hom.toAlgebra`. Use `haveI : Algebra.Etale P (D.obj j) := (hj j).1`. Establish `hc : ∀ r : P, (s.app j).hom (algebraMap P (D.obj j) r) = algebraMap P A r` using `fun r => congrArg (fun g => g.hom r) (hj j).2`.

Conclude with `⟨D.obj j, inferInstance, inferInstance, inferInstance, { (s.app j).hom with commutes' := hc }, ⟨x, hx⟩⟩`.
-/
theorem indEt_elem {P : Type} [CommRing P] [Algebra P B] [Algebra.Etale P B] [Algebra P A] [IsScalarTower P B A]
    (h : IndEt B A) (a : A) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra P E) (_ : Algebra.Etale P E) (φ : E →ₐ[P] A), a ∈ φ.range := by
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := indEt_comp (P := P) h
  obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep D hs a
  letI : Algebra P (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale P (D.obj j) := (hj j).1
  have hc : ∀ r : P, (s.app j).hom (algebraMap P (D.obj j) r) = algebraMap P A r := fun r =>
    congrArg (fun g => g.hom r) (hj j).2
  exact ⟨D.obj j, inferInstance, inferInstance, inferInstance,
    { (s.app j).hom with commutes' := hc }, ⟨x, hx⟩⟩

end Ind2

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, e.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, e.hom_inv_id, pull_id]`.
-/
theorem pull_iso_bij {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem bij_of_subsingleton {X Y : Type*} [Zero X] [Subsingleton X] [Subsingleton Y] (f : X → Y) :
    Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

open Polynomial in
/- English proof (translation)
Establish `hqA : IsUnit (q : A)` using `by simpa using hq.map (algebraMap T A)`. Use `letI : Algebra A (FractionRing T ⊗[T] A) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) (FractionRing T ⊗[T] A) := IsLocalization.tensorRight (FractionRing T) (nonZeroDivisors T)`. Establish `hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors T) ≤ nonZeroDivisors A`. Introduce and unpack `_ ⟨t, ht, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero (fun h => nonZeroDivisors.ne_zero ht (hinj (by rw [map_zero]; exact h)))`. Use `haveI hdK : IsDomain (FractionRing T ⊗[T] A) := IsLocalization.isDomain_of_le_nonZeroDivisors (FractionRing T ⊗[T] A) hle`. Introduce `n`. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Use `haveI := h_neg (ZMod q) (sp A) (tw q i) n hn haveI := h_neg (ZMod q) (sp (FractionRing T ⊗[T] A)) (tw q i) n hn`.

Conclude with `bij_of_subsingleton _`. Take `⟨ζ, hζ⟩` from `aic_root q T hT hq`. Use `GlobalTheory.T.h_zero_pullback_twist_bijective q A (FractionRing T ⊗[T] A) _ hqA ⟨algebraMap T A ζ, ?_⟩ hdK.toNontrivial (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i` and prove the remaining obligations. Establish `h1` using `root_map q (algebraMap T A) hq hqA hζ`. Use `haveI : NeZero (q : A) := ⟨hqA.ne_zero⟩`.

Establish `h2` using `Polynomial.isRoot_cyclotomic_iff.2 h1`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `h2`. Use `haveI := UpperTheory.etaleCohomology_functorialityAxioms_hold_of_sheafAxioms (ZMod q) A hSH (tw q i) n hn haveI : Subsingleton (Ht q (sp (FractionRing T ⊗[T] A)) n i) := by`. Break down `eq_or_lt_of_le (show 1 ≤ n by omega) with rfl | h2` into its components or cases.

Conclude with `GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq A hSH hel i`. Conclude with `GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq A hSH hind n i (by omega)`. Conclude with `bij_of_subsingleton _`.
-/
theorem local_eqv (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hT : AIC T)
    (hq : IsUnit (q : T)) (A : Type) [CommRing A] [IsDomain A] [Algebra (Polynomial T) A] [Algebra T A]
    [IsScalarTower T (Polynomial T) A] (hSH : SH A)
    (hel : ∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (φ : E →ₐ[Polynomial T] A), a ∈ φ.range)
    (hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A))
    (hinj : Function.Injective (algebraMap T A)) (i : ℤ) :
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := A)).toRingHom) (tw q i) := by
  have hqA : IsUnit (q : A) := by simpa using hq.map (algebraMap T A)
  letI : Algebra A (FractionRing T ⊗[T] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) (FractionRing T ⊗[T] A) :=
    IsLocalization.tensorRight (FractionRing T) (nonZeroDivisors T)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors T) ≤ nonZeroDivisors A := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero ht (hinj (by rw [map_zero]; exact h)))
  haveI hdK : IsDomain (FractionRing T ⊗[T] A) := IsLocalization.isDomain_of_le_nonZeroDivisors (FractionRing T ⊗[T] A) hle
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := h_neg (ZMod q) (sp A) (tw q i) n hn
    haveI := h_neg (ZMod q) (sp (FractionRing T ⊗[T] A)) (tw q i) n hn
    exact bij_of_subsingleton _
  · obtain ⟨ζ, hζ⟩ := aic_root q T hT hq
    refine GlobalTheory.T.h_zero_pullback_twist_bijective q A (FractionRing T ⊗[T] A) _ hqA ⟨algebraMap T A ζ, ?_⟩
      hdK.toNontrivial (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he)
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
    have h1 := root_map q (algebraMap T A) hq hqA hζ
    haveI : NeZero (q : A) := ⟨hqA.ne_zero⟩
    have h2 := Polynomial.isRoot_cyclotomic_iff.2 h1
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact h2
  · haveI := UpperTheory.etaleCohomology_functorialityAxioms_hold_of_sheafAxioms (ZMod q) A hSH (tw q i) n hn
    haveI : Subsingleton (Ht q (sp (FractionRing T ⊗[T] A)) n i) := by
      rcases eq_or_lt_of_le (show 1 ≤ n by omega) with rfl | h2
      · exact GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq A hSH hel i
      · exact GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq A hSH hind n i (by omega)
    exact bij_of_subsingleton _

/- English proof (translation)
Establish `P1` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct T (FractionRing T) B)`. Establish `P2` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct T (FractionRing T) A)`. Use `IsPullback.of_right ?_ ?_ P1` and prove the remaining obligations. Use `P2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `x`. Conclude with `(IsScalarTower.algebraMap_apply T B A x).symm`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.
-/
theorem pullback_square (T B A : Type) [CommRing T] [CommRing B] [CommRing A] [Algebra T B] [Algebra B A] [Algebra T A]
    [IsScalarTower T B A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id T (FractionRing T)) (IsScalarTower.toAlgHom T B A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by
  have P1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct T (FractionRing T) B)
  have P2 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct T (FractionRing T) A)
  refine IsPullback.of_right ?_ ?_ P1
  · convert P2 using 1
    · rw [← Spec.map_comp]
      congr 1
      ext x
      simp
    · rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply T B A x).symm
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
end UpperTheory.Cb.C3

open UpperTheory.Cb.C3 in
/- English proof (translation)
Introduce `q _ T _ _ _ hT hq B _ _ _ _ _ i`. Use `haveI := aic_intClosed T hT`. Use `haveI : Algebra.FormallySmooth T (Polynomial T) := Algebra.FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv.{0, 0} T)`. Use `haveI : Algebra.Smooth T (Polynomial T) := ⟨inferInstance, inferInstance⟩`. Use `haveI : Algebra.Smooth T B := Algebra.Smooth.comp T (Polynomial T) B`.

Establish `hqB : IsUnit (q : B)` using `by simpa using hq.map (algebraMap T B)`. Use `GlobalTheory.T.etaleCohomology_local_to_global_affine_indEtale q B (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom)) hqB i ?_` and prove the remaining obligations. Introduce `A _ _ hSH hInd`. Use `letI : Algebra T A := ((algebraMap B A).comp (algebraMap T B)).toAlgebra`. Use `haveI : IsScalarTower T B A := .of_algebraMap_eq' rfl`.

Use `letI : Algebra (Polynomial T) A := ((algebraMap B A).comp (algebraMap (Polynomial T) B)).toAlgebra`. Use `haveI : IsScalarTower (Polynomial T) B A := .of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower T (Polynomial T) A := .of_algebraMap_eq' (by`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `algebraMap B A (algebraMap T B x) = algebraMap B A (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))`.

Conclude with `congrArg (algebraMap B A) (IsScalarTower.algebraMap_apply T (Polynomial T) B x))`. Take `⟨hH, hS⟩` from `id hSH`. Use `haveI : IsLocalRing A := hH.toIsLocalRing`. Use `haveI := indEt_isDomain (T := T) hInd`. Establish `L` using `local_eqv q T hT hq A hSH (indEt_elem (P := Polynomial T) hInd) (indEt_comp (P := Polynomial T) hInd) (indEt_inj (T := T) hInd) i`.

Establish `PB` using `pullback_square T B A`. Introduce `n`. Establish `h1` using `L n`. Establish `h2 : spMap (Algebra.TensorProduct.includeRight (R` using `T) (A := FractionRing T) (B := A)).toRingHom = sch.map PB.isoPullback.hom ≫ sch.map (pullback.snd _ _) := by`. Rewrite using `[← sch.map_comp, PB.isoPullback_hom_snd]`.

Establish `h3 : pull _ (spMap (Algebra.TensorProduct.includeRight (R` using `T) (A := FractionRing T) (B := A)).toRingHom) (tw q i) n = (pull _ (sch.map PB.isoPullback.hom) (tw q i) n).comp (pull _ (sch.map (pullback.snd _ _)) (tw q i) n) := by`. Use extensionality with `x`. Rewrite using `[h2, pull_comp]`. Both sides reduce to the same expression. Rewrite `h1` using `[h3]`.

Establish `h4` using `pull_iso_bij (sch.mapIso PB.isoPullback) (tw q i) n`. Conclude with `(Function.Bijective.of_comp_iff' h4 _).1 h1`.
-/
theorem UpperTheory.Cb.etale_cohomology_ind_etale_base_change : GlobalTheory.EtC.C3 := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i
  haveI := aic_intClosed T hT
  haveI : Algebra.FormallySmooth T (Polynomial T) := Algebra.FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv.{0, 0} T)
  haveI : Algebra.Smooth T (Polynomial T) := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth T B := Algebra.Smooth.comp T (Polynomial T) B
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap T B)
  refine GlobalTheory.T.etaleCohomology_local_to_global_affine_indEtale q B (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom)) hqB i ?_
  intro A _ _ hSH hInd
  letI : Algebra T A := ((algebraMap B A).comp (algebraMap T B)).toAlgebra
  haveI : IsScalarTower T B A := .of_algebraMap_eq' rfl
  letI : Algebra (Polynomial T) A := ((algebraMap B A).comp (algebraMap (Polynomial T) B)).toAlgebra
  haveI : IsScalarTower (Polynomial T) B A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower T (Polynomial T) A := .of_algebraMap_eq' (by
    ext x
    change algebraMap B A (algebraMap T B x) = algebraMap B A (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))
    exact congrArg (algebraMap B A) (IsScalarTower.algebraMap_apply T (Polynomial T) B x))
  obtain ⟨hH, hS⟩ := id hSH
  haveI : IsLocalRing A := hH.toIsLocalRing
  haveI := indEt_isDomain (T := T) hInd
  have L := local_eqv q T hT hq A hSH (indEt_elem (P := Polynomial T) hInd) (indEt_comp (P := Polynomial T) hInd)
    (indEt_inj (T := T) hInd) i
  have PB := pullback_square T B A
  intro n
  have h1 := L n
  have h2 : spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := A)).toRingHom =
      sch.map PB.isoPullback.hom ≫ sch.map (pullback.snd _ _) := by
    rw [← sch.map_comp, PB.isoPullback_hom_snd]
  have h3 : pull _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := A)).toRingHom) (tw q i) n =
      (pull _ (sch.map PB.isoPullback.hom) (tw q i) n).comp (pull _ (sch.map (pullback.snd _ _)) (tw q i) n) := by
    ext x
    rw [h2, pull_comp]
    rfl
  rw [h3] at h1
  have h4 := pull_iso_bij (sch.mapIso PB.isoPullback) (tw q i) n
  exact (Function.Bijective.of_comp_iff' h4 _).1 h1
