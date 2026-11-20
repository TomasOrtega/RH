import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionTwistTsumNormGe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsComplexCmAbelianObject
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ToricData GlobalTheory.HostModel GlobalTheory.HostModel.ConjDual GlobalTheory.Ex.ValInh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex

section Valued

/- English proof (translation)
Take `⟨p, hp, h⟩` from `hx`. Establish `: IsIntegral S x` using `⟨p.map (j.codRestrict S.toSubring hj), hp.map _, by rw [Polynomial.eval₂_map]; exact h⟩`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 this`. Conclude with `y.2`.
-/
theorem mem_of_isIntegralElem {R C : Type} [CommRing R] [Field C] (S : ValuationSubring C) (j : R →+* C) (hj : ∀ r, j r ∈ S)
    {x : C} (hx : j.IsIntegralElem x) : x ∈ S := by
  obtain ⟨p, hp, h⟩ := hx
  have : IsIntegral S x := ⟨p.map (j.codRestrict S.toSubring hj), hp.map _, by rw [Polynomial.eval₂_map]; exact h⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

variable {O' : Type} [CommRing O'] [IsDomain O'] {R₁ : Type} [CommRing R₁] (g : PowerSeries O' →+* R₁) {K : Type} [Field K]
  (i : R₁ →+* K)

/- English proof (translation)
Introduce `h`. Set `V` to `PowerSeries (FractionRing O')`. Take `⟨C, _, _, _, _, _, h1, h2⟩` from `GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V (FractionRing V) (a := PowerSeries.X) PowerSeries.X_ne_zero (fun e => not_isUnit_zero (PowerSeries.constantCoeff_X (R := FractionRing O') ▸ e.map PowerSeries.constantCoeff)) (r := 1 / 2) (by norm_num) (by norm_ …`. Set `j₀ : V →+* C` to `(algebraMap (FractionRing V) C).comp (algebraMap V _)`. Set `j : PowerSeries O' →+* C` to `j₀.comp (PowerSeries.map (algebraMap O' (FractionRing O')))`.

Establish `hj : Function.Injective j` using `((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _)).comp (PowerSeries.map_injective _ (IsFractionRing.injective O' _))`. Use `letI : Algebra (PowerSeries O') K := (i.comp g).toAlgebra`. Use `letI : Algebra (PowerSeries O') C := j.toAlgebra`. Use `haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 hi`. Use `haveI : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hj`.

Use `haveI : Algebra.IsAlgebraic (PowerSeries O') K := ⟨halg⟩`. Set `gam : K →ₐ[PowerSeries O'] C` to `IsAlgClosed.lift`. Establish `hc : ∀ f, gam.toRingHom (i (g f)) = j f` using `fun f => gam.commutes f`. Use `letI : Algebra (FractionRing O') C := (j₀.comp PowerSeries.C).toAlgebra`. Establish `hX : j PowerSeries.X = j₀ PowerSeries.X` using `congrArg j₀ (PowerSeries.map_X _)`.

Use `h C gam.toRingHom (Units.mk0 (j PowerSeries.X) fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm))) (fun x => (congrArg j₀ (PowerSeries.map_C _ x).symm).trans (hc _).symm) (fun r => ?_) (hc _).symm ?_` and prove the remaining obligations. Use `mem_normIntegers_iff.1 (mem_of_isIntegralElem _ j (fun f => mem_normIntegers_iff.2 ((h1 _).2 ⟨_, rfl⟩)) ?_)` and prove the remaining obligations. Take `⟨p, hp, e⟩` from `hg r`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `congrArg (gam.toRingHom.comp i) e` as an intermediate fact.

Rewrite `this` using `[map_zero, Polynomial.hom_eval₂, show (gam.toRingHom.comp i).comp g = j from RingHom.ext hc]`. Then use the resulting hypothesis. Rewrite using `[Units.val_mk0, hX]`. Conclude with `h2.trans_lt (by norm_num)`.
-/
theorem not_allC_false (hi : Function.Injective (i.comp g))
    (halg : ∀ x : K, ∃ p : Polynomial (PowerSeries O'), p ≠ 0 ∧ p.eval₂ (i.comp g) x = 0) (hg : g.IsIntegral) :
    ¬ AllC g i fun _ _ => False := by
  intro h
  let V := PowerSeries (FractionRing O')
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V (FractionRing V)
    (a := PowerSeries.X) PowerSeries.X_ne_zero (fun e => not_isUnit_zero (PowerSeries.constantCoeff_X (R := FractionRing O') ▸ e.map PowerSeries.constantCoeff))
    (r := 1 / 2) (by norm_num) (by norm_num)
  let j₀ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  let j : PowerSeries O' →+* C := j₀.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hj : Function.Injective j := ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _)).comp
    (PowerSeries.map_injective _ (IsFractionRing.injective O' _))
  letI : Algebra (PowerSeries O') K := (i.comp g).toAlgebra
  letI : Algebra (PowerSeries O') C := j.toAlgebra
  haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  haveI : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  haveI : Algebra.IsAlgebraic (PowerSeries O') K := ⟨halg⟩
  let gam : K →ₐ[PowerSeries O'] C := IsAlgClosed.lift
  have hc : ∀ f, gam.toRingHom (i (g f)) = j f := fun f => gam.commutes f
  letI : Algebra (FractionRing O') C := (j₀.comp PowerSeries.C).toAlgebra
  have hX : j PowerSeries.X = j₀ PowerSeries.X := congrArg j₀ (PowerSeries.map_X _)
  refine h C gam.toRingHom (Units.mk0 (j PowerSeries.X) fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm)))
    (fun x => (congrArg j₀ (PowerSeries.map_C _ x).symm).trans (hc _).symm) (fun r => ?_) (hc _).symm ?_
  · refine mem_normIntegers_iff.1 (mem_of_isIntegralElem _ j (fun f => mem_normIntegers_iff.2 ((h1 _).2 ⟨_, rfl⟩)) ?_)
    obtain ⟨p, hp, e⟩ := hg r
    refine ⟨p, hp, ?_⟩
    have := congrArg (gam.toRingHom.comp i) e
    rwa [map_zero, Polynomial.hom_eval₂, show (gam.toRingHom.comp i).comp g = j from RingHom.ext hc] at this
  · rw [Units.val_mk0, hX]
    exact h2.trans_lt (by norm_num)

/- English proof (translation)
The claim follows from `GlobalTheory.Ex.not_allC_false (RingHom.id _) i hi.inj hi.alg (RingHom.isIntegral_of_surjective _ Function.surjective_id)`.
-/
theorem SerBase.not_allC_false {K : Type} [Field K] [Algebra (FractionRing O') K] {i : PowerSeries O' →+* K} (hi : SerBase i) :
    ¬ AllC (RingHom.id _) i fun _ _ => False :=
  GlobalTheory.Ex.not_allC_false (RingHom.id _) i hi.inj hi.alg (RingHom.isIntegral_of_surjective _ Function.surjective_id)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {b : O →+* O'} {Y : Model Xo c β} [IsDomain R₁] {g}
  {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}

/- English proof (translation)
Use `letI := g.toAlgebra`. Use `haveI : Module.Finite (PowerSeries O') R₁ := h.2.1`. Use `haveI : FaithfulSMul (PowerSeries O') R₁ := (faithfulSMul_iff_algebraMap_injective _ _).2 h.1`. Use `haveI := IsLocalization.isAlgebraic (FractionRing R₁) (nonZeroDivisors R₁)`. Use `haveI := Algebra.IsAlgebraic.trans (PowerSeries O') R₁ (FractionRing R₁)`.

Conclude with `GlobalTheory.Ex.not_allC_false g _ ((IsFractionRing.injective R₁ _).comp h.1) (fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x) h.2.1.to_isIntegral`.
-/
theorem ArcPt.not_allC_false (h : ArcPt Y b g y₁) : ¬ AllC g (algebraMap R₁ (FractionRing R₁)) fun _ _ => False := by
  letI := g.toAlgebra
  haveI : Module.Finite (PowerSeries O') R₁ := h.2.1
  haveI : FaithfulSMul (PowerSeries O') R₁ := (faithfulSMul_iff_algebraMap_injective _ _).2 h.1
  haveI := IsLocalization.isAlgebraic (FractionRing R₁) (nonZeroDivisors R₁)
  haveI := Algebra.IsAlgebraic.trans (PowerSeries O') R₁ (FractionRing R₁)
  exact GlobalTheory.Ex.not_allC_false g _ ((IsFractionRing.injective R₁ _).comp h.1)
    (fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x) h.2.1.to_isIntegral

/- English proof (translation)
Introduce `h` and use `PowerSeries.X_ne_zero (h.1.1 (PowerSeries.constantCoeff_X.trans (map_zero _).symm))`.
-/
example {a : ArcIn D l β O' b} (y : Sp (FractionRing O') ⟶ Xo.XF c) : ¬ RealAt Y a (PowerSeries.constantCoeff (R := O')) y :=
  fun h => PowerSeries.X_ne_zero (h.1.1 (PowerSeries.constantCoeff_X.trans (map_zero _).symm))
end Valued

namespace StepInh
section Series
variable {k K X : Type} [CommRing k] [Field K] (i : PowerSeries k →+* K)

/- English proof (translation)
Set `T : X → K` to `fun z => ω z * R ^ (e z % n)`. Establish `hT : (Set.range T).Finite`. Use `((((Polynomial.nthRoots N (1 : K)).finite_toSet).prod (Set.finite_Iio n)).image fun p : K × ℕ => p.1 * R ^ p.2).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨(ω z, e z % n), ⟨(Polynomial.mem_nthRoots hN).2 (hω z), Nat.mod_lt _ hn⟩, rfl⟩`.

Establish `hd : ∀ t, {z | e z / n = t}.Finite` using `fun t => (he ((t + 1) * n)).subset fun z hz => ((Nat.div_lt_iff_lt_mul hn).1 (Nat.lt_succ_of_le (le_of_eq hz))).le`. Establish `hp : ∀ (S : ValuationSubring K) (x : K) (m : ℕ), 0 < m → x ^ m ∈ S → x ∈ S` using `fun S x m hm h => by`. Rewrite `h`, the goal using `[← S.valuation_le_one_iff]`. Rewrite `h` using `[map_pow, pow_le_one_iff hm.ne']`. Then use the resulting hypothesis. Use `⟨∑ t ∈ hT.toFinset, t * i (PowerSeries.mk fun m => ∑ᶠ (z : X) (_ : e z / n = m), if T z = t then 1 else 0), fun S hS => sum_mem fun t ht => mul_mem ?_ (hS _), fun C _ _ _ gam h1 h2 => ?_⟩` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `hT.mem_toFinset.1 ht`. Conclude with `mul_mem (hp S _ N hN (hω z ▸ S.one_mem)) (pow_mem (hp S _ n hn (hR ▸ hS _)) _)`. Use `hasSum_sum fun t (_ : t ∈ hT.toFinset) => (hasSum_map_powerSeries_mk_finsum k C X (gam.comp i) h1 h2 (fun z => e z / n) hd fun z => if T z = t then 1 else 0).mul_left (gam t)` as an intermediate fact. Rewrite using `[map_sum]`. Simplify using `only [map_mul]`.

Use `(congrArg (HasSum · _) (funext fun z => ?_)).mp this` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (T z) (fun t _ ht => by simp [ht.symm]) fun h => (h (hT.mem_toFinset.2 ⟨z, rfl⟩)).elim]`. Simplify using `only [if_true, map_one, _root_.one_mul, RingHom.comp_apply, ← hR, T, map_mul, map_pow, ← pow_mul, _root_.mul_assoc, ← pow_add, Nat.mod_add_div]`.
-/
theorem exists_sum (R : K) {n : ℕ} (hn : 0 < n) (hR : R ^ n = i PowerSeries.X) {N : ℕ} (hN : 0 < N) (ω : X → K)
    (hω : ∀ z, ω z ^ N = 1) (e : X → ℕ) (he : ∀ t, {z | e z ≤ t}.Finite) :
    ∃ v : K, (∀ S : ValuationSubring K, (∀ r, i r ∈ S) → v ∈ S) ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
        (∀ f, ‖gam (i f)‖ ≤ 1) → ‖gam (i PowerSeries.X)‖ < 1 → HasSum (fun z => gam (ω z) * gam R ^ e z) (gam v) := by
  classical
  let T : X → K := fun z => ω z * R ^ (e z % n)
  have hT : (Set.range T).Finite := by
    refine ((((Polynomial.nthRoots N (1 : K)).finite_toSet).prod (Set.finite_Iio n)).image
      fun p : K × ℕ => p.1 * R ^ p.2).subset ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨(ω z, e z % n), ⟨(Polynomial.mem_nthRoots hN).2 (hω z), Nat.mod_lt _ hn⟩, rfl⟩
  have hd : ∀ t, {z | e z / n = t}.Finite := fun t => (he ((t + 1) * n)).subset fun z hz =>
    ((Nat.div_lt_iff_lt_mul hn).1 (Nat.lt_succ_of_le (le_of_eq hz))).le
  have hp : ∀ (S : ValuationSubring K) (x : K) (m : ℕ), 0 < m → x ^ m ∈ S → x ∈ S := fun S x m hm h => by
    rw [← S.valuation_le_one_iff] at h ⊢
    rwa [map_pow, pow_le_one_iff hm.ne'] at h
  refine ⟨∑ t ∈ hT.toFinset, t * i (PowerSeries.mk fun m => ∑ᶠ (z : X) (_ : e z / n = m), if T z = t then 1 else 0),
    fun S hS => sum_mem fun t ht => mul_mem ?_ (hS _), fun C _ _ _ gam h1 h2 => ?_⟩
  · obtain ⟨z, rfl⟩ := hT.mem_toFinset.1 ht
    exact mul_mem (hp S _ N hN (hω z ▸ S.one_mem)) (pow_mem (hp S _ n hn (hR ▸ hS _)) _)
  · have := hasSum_sum fun t (_ : t ∈ hT.toFinset) => (hasSum_map_powerSeries_mk_finsum k C X (gam.comp i) h1 h2
      (fun z => e z / n) hd fun z => if T z = t then 1 else 0).mul_left (gam t)
    rw [map_sum]
    simp only [map_mul]
    refine (congrArg (HasSum · _) (funext fun z => ?_)).mp this
    rw [Finset.sum_eq_single (T z) (fun t _ ht => by simp [ht.symm]) fun h => (h (hT.mem_toFinset.2 ⟨z, rfl⟩)).elim]
    simp only [if_true, map_one, _root_.one_mul, RingHom.comp_apply, ← hR, T, map_mul, map_pow, ← pow_mul,
      _root_.mul_assoc, ← pow_add, Nat.mod_add_div]
end Series

section Terms
variable {F : Type} [Field F]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Geo.Tor.Level H)

def halfSq (y : 𝓞 E) : ℤ := arcForm l y y / 2

def splitBe (k : Type) [CommRing k] [IsDomain k] (F : Type) [Field F] [Algebra (FractionRing k) F] :
    (splitNum (E := E) k F).Form l.M' where
  be := arcForm l
  symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩

/- English proof (translation)
The claim follows from `(Int.mul_ediv_cancel' ((dvd_mul_right 2 (l.M' : ℤ)).trans ⟨trForm H y y, rfl⟩)).symm`.
-/
theorem two_halfSq (y : 𝓞 E) : arcForm l y y = 2 * halfSq l y :=
  (Int.mul_ediv_cancel' ((dvd_mul_right 2 (l.M' : ℤ)).trans ⟨trForm H y y, rfl⟩)).symm

/- English proof (translation)
The claim follows from `congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)`.
-/
theorem arcForm_symm (y z : 𝓞 E) : arcForm l y z = arcForm l z y := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)

/- English proof (translation)
Establish `h` using `two_halfSq l (y + m • z)`. Simplify using `only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, arcForm_symm l z y, two_halfSq l y, two_halfSq l z] at h`. Simplify using `only [nsmul_eq_mul (α := ℤ)] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem halfSq_add (y z : 𝓞 E) (m : ℕ) :
    halfSq l (y + m • z) = halfSq l y + m * arcForm l y z + m ^ 2 * halfSq l z := by
  have h := two_halfSq l (y + m • z)
  simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, arcForm_symm l z y,
    two_halfSq l y, two_halfSq l z] at h
  simp only [nsmul_eq_mul (α := ℤ)] at h
  linarith

/- English proof (translation)
Establish `h : 0 < arcForm l y y` using `mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)`. Rewrite `h` using `[two_halfSq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem halfSq_pos {y : 𝓞 E} (hy : y ≠ 0) : 0 < halfSq l y := by
  have h : 0 < arcForm l y y := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  rw [two_halfSq] at h
  omega

/- English proof (translation)
Simplify using `[halfSq]`.
-/
theorem halfSq_zero : halfSq l 0 = 0 := by simp [halfSq]

/- English proof (translation)
The claim follows from `(eq_or_ne y 0).elim (fun e => by rw [e, halfSq_zero]) fun h => (halfSq_pos l h).le`.
-/
theorem halfSq_nonneg (y : 𝓞 E) : 0 ≤ halfSq l y :=
  (eq_or_ne y 0).elim (fun e => by rw [e, halfSq_zero]) fun h => (halfSq_pos l h).le

/- English proof (translation)
Use `((finite_form_le (arcForm l) (arcForm_symm l) (fun z hz => ?_) (2 * t)).preimage (f := fun χ => y + m • χ) fun a _ b _ e => nsmul_right_injective hm.ne' (add_left_cancel e)).subset fun χ h => ?_` and prove the remaining obligations. Rewrite using `[two_halfSq]`. Conclude with `mul_pos two_pos (halfSq_pos l hz)`. Conclude with `(two_halfSq l _).trans_le (mul_le_mul_of_nonneg_left h zero_le_two)`.
-/
theorem finite_halfSq (y : 𝓞 E) {m : ℕ} (hm : 0 < m) (t : ℤ) : {χ : 𝓞 E | halfSq l (y + m • χ) ≤ t}.Finite := by
  refine ((finite_form_le (arcForm l) (arcForm_symm l) (fun z hz => ?_) (2 * t)).preimage (f := fun χ => y + m • χ)
    fun a _ b _ e => nsmul_right_injective hm.ne' (add_left_cancel e)).subset fun χ h => ?_
  · rw [two_halfSq]; exact mul_pos two_pos (halfSq_pos l hz)
  · exact (two_halfSq l _).trans_le (mul_le_mul_of_nonneg_left h zero_le_two)

variable (k : Type) [CommRing k] [IsDomain k] [Algebra (FractionRing k) F]

end Terms

section ToricLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}
  (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k) {O : Type} [CommRing O] (β : O →+* c.F)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing k) F] (ζ : ℕ → Fˣ)
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
  (hζ : ∀ n, 0 < n → ∀ z : c.F, (z : ℂ) = zeta n → (ζ n : F) = algebraMap (FractionRing k) F (algebraMap k _ (bF z)))

def toricLift : Lift ((arcIn c k bF).restrict β) F :=
  letI := H.starRing
  have hρ : algebraMap (FractionRing k) F (algebraMap k _ (bF ⟨_, sqrtNegDisc_mem_coeffField c⟩)) ^ 2 = -(H.d : F) := by
    have : (⟨_, sqrtNegDisc_mem_coeffField c⟩ : c.F) ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
    rw [← map_pow, ← map_pow, ← map_pow, this, map_neg, map_neg, map_neg, map_natCast, map_natCast, map_natCast]
  have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
      QkExt (algebraMap _ F) (qkPt k (arcRoot c k bF h) (isPrimitiveRoot_arcRoot c k bF h).pow_eq_one a) q →
        QkPt.Equiv _ F q ((tateIsoQ H k ζ hp hc).ev n a) := fun {n} h a q hq => by
    rw [qkExt_qkPt k _ (algebraMap (FractionRing k) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
      ((hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl).trans rfl)] at hq
    subst hq
    exact equiv_refl_split k F _
  { ρ := _, ρ_sq := hρ, det := (hypArc H k _ hρ ζ hp hc).det, I := tateIsoQ H k ζ hp hc, N := splitNum (E := E) k F
    ν := toricNumOf _ _ _ F
    q := fun n a => splitQ k a.1 (rootChar (ζ n) (toDual H a.2)) (rootChar_pow_eq_one (pow_eq_one_of_prim hp n) _)
    hq := (hypArc H k _ hρ ζ hp hc).hq, be := splitBe l k F, be_eq := fun _ _ => rfl
    ρ_eq := fun r hr => congrArg (fun z => algebraMap (FractionRing k) F (algebraMap k _ (bF z))) (Subtype.ext hr.symm)
    ζ_eq := fun z hz => hζ l.A l.A_pos (β z) hz
    levA := key _, levM := fun v _ => key _ v, closed := ‹_› }
omit ζ hp hc hζ in
variable (F) in

/- English proof (translation)
Use `haveI := c.fin`. Take `⟨ζ, hp, hc, hζ⟩` from `exists_roots c.F F (((algebraMap (FractionRing k) F).comp (algebraMap k _)).comp bF)`. Conclude with `⟨toricLift c k bF β ζ hp hc hζ, inferInstanceAs (Nontrivial (𝓞 E))⟩`.
-/
theorem exists_lift : ∃ A : Lift ((arcIn c k bF).restrict β) F, Nontrivial A.N.X := by
  haveI := c.fin
  obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F (((algebraMap (FractionRing k) F).comp (algebraMap k _)).comp bF)
  exact ⟨toricLift c k bF β ζ hp hc hζ, inferInstanceAs (Nontrivial (𝓞 E))⟩

end ToricLift

section ToricSer
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}
  {k : Type} [Field k] {K : Type} [Field K] (i : PowerSeries k →+* K) {ζ r : ℕ → Kˣ}
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hr : ∀ n, 0 < n → (r n : K) ^ n = i PowerSeries.X)

variable (l) in

def thTerm {F : Type} [Field F] (ζ r : Fˣ) (m : ℕ) (x : HypLattice H) (χ : 𝓞 E) : Fˣ :=
  ζ ^ (m * toDual H x.2 χ - ((m ^ 2 - 1) / 2 : ℕ) * toDual H x.2 x.1) * r ^ halfSq l (x.1 + m • χ)

include hp hr in

/- English proof (translation)
Break down `m.eq_zero_or_pos with rfl | hm` into its components or cases. Conclude with `⟨0, fun h => absurd h (lt_irrefl _)⟩`. Establish `hm2` using `pow_pos hm 2`. Take `⟨v, h₁, h₂⟩` from `exists_sum i (r (m ^ 2)) hm2 (hr _ hm2) hm2 (fun χ : 𝓞 E => (ζ (m ^ 2) ^ (m * toDual H x.2 χ - ((m ^ 2 - 1) / 2 : ℕ) * toDual H x.2 x.1) : Kˣ)) (fun χ => by rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, (hp _ hm2).pow_eq_one, one_zp …`. Use `⟨v, fun _ => ⟨h₁, fun C _ _ _ gam a b => (congrArg (HasSum · _) (funext fun χ => ?_)).mp (h₂ C gam a b)⟩⟩` and prove the remaining obligations.

Rewrite using `[thTerm, ← map_zpow, Units.val_mul, ← Int.toNat_of_nonneg (halfSq_nonneg l (x.1 + m • χ)), zpow_natCast, Int.toNat_natCast, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression.
-/
theorem exists_theta (m : ℕ) (x : HypLattice H) : ∃ v : K, 0 < m →
    (∀ S : ValuationSubring K, (∀ r, i r ∈ S) → v ∈ S) ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
        (∀ f, ‖gam (i f)‖ ≤ 1) → ‖gam (i PowerSeries.X)‖ < 1 → HasSum (fun χ => (thTerm l (Units.map gam.toMonoidHom (ζ (m ^ 2)))
          (Units.map gam.toMonoidHom (r (m ^ 2))) m x χ : C)) (gam v) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · exact ⟨0, fun h => absurd h (lt_irrefl _)⟩
  have hm2 := pow_pos hm 2
  obtain ⟨v, h₁, h₂⟩ := exists_sum i (r (m ^ 2)) hm2 (hr _ hm2) hm2
    (fun χ : 𝓞 E => (ζ (m ^ 2) ^ (m * toDual H x.2 χ - ((m ^ 2 - 1) / 2 : ℕ) * toDual H x.2 x.1) : Kˣ))
    (fun χ => by rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      (hp _ hm2).pow_eq_one, one_zpow, Units.val_one])
    (fun χ => (halfSq l (x.1 + m • χ)).toNat) fun t => (finite_halfSq l x.1 hm t).subset fun χ h => Int.toNat_le.1 h
  refine ⟨v, fun _ => ⟨h₁, fun C _ _ _ gam a b => (congrArg (HasSum · _) (funext fun χ => ?_)).mp (h₂ C gam a b)⟩⟩
  rw [thTerm, ← map_zpow, Units.val_mul, ← Int.toNat_of_nonneg (halfSq_nonneg l (x.1 + m • χ)), zpow_natCast,
    Int.toNat_natCast, Units.val_pow_eq_pow_val]
  rfl

include hp hr in

/- English proof (translation)
Distinguish the cases in `h : 0 < m ∧ 0 < j`. Use `swap`. Conclude with `⟨0, fun a b => absurd ⟨a, b⟩ h⟩`. Take `⟨hm, hj⟩` from `h`. Establish `hm2` using `pow_pos hm 2`.

Set `e : 𝓞 E → ℤ` to `fun χ => halfSq l (m ^ 2 • z.1) + m ^ 2 * arcForm l z.1 (x.1 + m • χ) + j * halfSq l (x.1 + m • χ)`. Establish `he : ∀ χ, halfSq l (x.1 + m ^ 2 • z.1 + m • χ) ≤ e χ` using `fun χ => by`. Establish `a` using `halfSq_add l (x.1 + m • χ) z.1 (m ^ 2)`. Establish `b` using `halfSq_add l 0 z.1 (m ^ 2)`. Rewrite `b` using `[zero_add, halfSq_zero, map_zero, LinearMap.zero_apply]`.

Rewrite using `[add_right_comm, a, arcForm_symm l (x.1 + m • χ)]`. Establish `c` using `mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ j by exact_mod_cast hj) (halfSq_nonneg l (x.1 + m • χ))`. Simplify using `only [e, b]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨w, -, h₂⟩` from `exists_sum i (r (m ^ 2 * j)) (mul_pos hm2 hj) (hr _ (mul_pos hm2 hj)) (mul_pos hm2 hj) (fun χ : 𝓞 E => (ζ j ^ (toDual H z.2 x.1 + m * toDual H z.2 χ) * ζ (m ^ 2) ^ (m * toDual H x.2 χ - ((m ^ 2 - 1) / 2 : ℕ) * toDual H x.2 x.1) : Kˣ)) (fun χ => by`. Establish `a : ∀ {t : Kˣ} {n : ℕ} (_ : t ^ n = 1) (s : ℤ), (t ^ s) ^ n = 1` using `fun {t n} h s => by`. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]`. Rewrite using `[← Units.val_pow_eq_pow_val, mul_pow, pow_mul', pow_mul, a (hp _ hj).pow_eq_one, a (hp _ hm2).pow_eq_one]`. Use the proof step `simp)`.

Use the proof step `(fun χ => (e χ).toNat) fun t => (finite_halfSq l _ hm t).subset fun χ h => (he χ).trans (Int.toNat_le.1 h)`. Use `⟨w, fun _ _ C _ _ _ gam a b => (congrArg (HasSum · _) (funext fun χ => ?_)).mp (h₂ C gam a b)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Units.map gam.toMonoidHom _ : Cˣ).val * (Units.map gam.toMonoidHom (r (m ^ 2 * j)) : Cˣ).val ^ _ = _`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, Int.toNat_of_nonneg ((halfSq_nonneg l _).trans (he χ)), thTerm, ← hc _ j hm2 hj, ← hc j _ hj hm2, mul_comm j]`. Use `congr 1`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [map_mul, map_zpow, map_pow, ofMul_mul, ofMul_pow, ofMul_zpow, e, map_add, map_nsmul]`. Simplify using `only [nsmul_eq_mul (α := ℤ)]`. Apply the tactic sequence `match_scalars <;> ring`.
-/
theorem exists_coord (hc : ∀ n m, 0 < n → 0 < m → r (n * m) ^ m = r n) (m j : ℕ) (z x : HypLattice H) : ∃ w : K,
    0 < m → 0 < j → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
      (∀ f, ‖gam (i f)‖ ≤ 1) → ‖gam (i PowerSeries.X)‖ < 1 → HasSum (fun χ : 𝓞 E =>
        (Units.map gam.toMonoidHom (r (m ^ 2 * j)) ^ halfSq l (m ^ 2 • z.1) *
          (Units.map gam.toMonoidHom (ζ j) ^ toDual H z.2 x.1 * Units.map gam.toMonoidHom (r j) ^ arcForm l z.1 x.1 *
          (Units.map gam.toMonoidHom (ζ j) ^ toDual H z.2 χ * Units.map gam.toMonoidHom (r j) ^ arcForm l z.1 χ) ^ m *
          thTerm l (Units.map gam.toMonoidHom (ζ (m ^ 2))) (Units.map gam.toMonoidHom (r (m ^ 2))) m x χ) : Cˣ).val) (gam w) := by
  by_cases h : 0 < m ∧ 0 < j
  swap
  · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
  obtain ⟨hm, hj⟩ := h
  have hm2 := pow_pos hm 2
  let e : 𝓞 E → ℤ := fun χ => halfSq l (m ^ 2 • z.1) + m ^ 2 * arcForm l z.1 (x.1 + m • χ) + j * halfSq l (x.1 + m • χ)
  have he : ∀ χ, halfSq l (x.1 + m ^ 2 • z.1 + m • χ) ≤ e χ := fun χ => by
    have a := halfSq_add l (x.1 + m • χ) z.1 (m ^ 2)
    have b := halfSq_add l 0 z.1 (m ^ 2)
    rw [zero_add, halfSq_zero, map_zero, LinearMap.zero_apply] at b
    rw [add_right_comm, a, arcForm_symm l (x.1 + m • χ)]
    have c := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ j by exact_mod_cast hj) (halfSq_nonneg l (x.1 + m • χ))
    simp only [e, b]
    push_cast
    linarith
  obtain ⟨w, -, h₂⟩ := exists_sum i (r (m ^ 2 * j)) (mul_pos hm2 hj) (hr _ (mul_pos hm2 hj)) (mul_pos hm2 hj)
    (fun χ : 𝓞 E => (ζ j ^ (toDual H z.2 x.1 + m * toDual H z.2 χ) *
      ζ (m ^ 2) ^ (m * toDual H x.2 χ - ((m ^ 2 - 1) / 2 : ℕ) * toDual H x.2 x.1) : Kˣ))
    (fun χ => by
      have a : ∀ {t : Kˣ} {n : ℕ} (_ : t ^ n = 1) (s : ℤ), (t ^ s) ^ n = 1 := fun {t n} h s => by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
      rw [← Units.val_pow_eq_pow_val, mul_pow, pow_mul', pow_mul, a (hp _ hj).pow_eq_one, a (hp _ hm2).pow_eq_one]
      simp)
    (fun χ => (e χ).toNat) fun t => (finite_halfSq l _ hm t).subset fun χ h => (he χ).trans (Int.toNat_le.1 h)
  refine ⟨w, fun _ _ C _ _ _ gam a b => (congrArg (HasSum · _) (funext fun χ => ?_)).mp (h₂ C gam a b)⟩
  change (Units.map gam.toMonoidHom _ : Cˣ).val * (Units.map gam.toMonoidHom (r (m ^ 2 * j)) : Cˣ).val ^ _ = _
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, Int.toNat_of_nonneg ((halfSq_nonneg l _).trans (he χ)),
    thTerm, ← hc _ j hm2 hj, ← hc j _ hj hm2, mul_comm j]
  congr 1
  apply Additive.ofMul.injective
  simp only [map_mul, map_zpow, map_pow, ofMul_mul, ofMul_pow, ofMul_zpow, e, map_add, map_nsmul]
  simp only [nsmul_eq_mul (α := ℤ)]
  match_scalars <;> ring

end ToricSer

section SerInh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}

end SerInh

section Settings
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨_, _, _⟩` from `h`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Take `⟨C, _, _, _, _, _, h1, h2⟩` from `GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hp.ne_zero (hp.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p) (r := 1 / 2) (by norm_num) (by norm_num)`. Use `⟨C, _, ‹_›, ‹_›, ‹_›, charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective, _, fun r => (h1 _).2 ⟨r, rfl⟩, fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton.1 (hp.maximalIdeal_eq ▸ hr)`.

Use `(h1 _).2 ⟨s, rfl⟩` as an intermediate fact. Rewrite using `[map_mul, map_mul, norm_mul, h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_cExt (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (h : CDV W) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C)
      (_ : CharZero C) (_ : Algebra (FractionRing W) C), CExt W (IsLocalRing.maximalIdeal W) C := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W)
    hp.ne_zero (hp.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p) (r := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, _, ‹_›, ‹_›, ‹_›, charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective, _,
    fun r => (h1 _).2 ⟨r, rfl⟩, fun r hr => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 (hp.maximalIdeal_eq ▸ hr)
  have := (h1 _).2 ⟨s, rfl⟩
  rw [map_mul, map_mul, norm_mul, h2]
  linarith

def zeroMdl (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (h : CDV W) {C : Type} [NormedField C] [IsAlgClosed C]
    [Algebra (FractionRing W) C] (hC : CExt W (IsLocalRing.maximalIdeal W) C) (ρ : C) (hρ) (ζ : ℕ → Cˣ) (hp) (hc) :
    Mdl (zeroFull H ρ hρ ζ hp hc) :=
  haveI := h.2.1
  { W := W, cdv := h, ext := hC, t := _, P := GlobalTheory.LN.PelModel.zeroP H W _, φ := jFK (R := W) C
    cart := baseMap_pb (X := PUnit) (fun _ => 1) (algebraMap (FractionRing W) C) fun _ => 1
    lb := lbIso_of_g_one (fun _ _ => rfl) (Inh.linComb_triv_g _ _)
    act := fun _ => end_baseMap (X := PUnit) (fun _ => 1) (algebraMap (FractionRing W) C) (fun _ => 1) _ _ }

section Tate
variable {R : Type} [CommRing R] [IsDomain R] (q : (FractionRing R)ˣ) (F : Type) [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Simplify using `only [polar, ← zpow_neg, ← zpow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polar_sq (a a' b : ℤ) : polar (fun n : ℤ => q ^ n ^ 2) (a + a') b =
    polar (fun n : ℤ => q ^ n ^ 2) a b * polar (fun n : ℤ => q ^ n ^ 2) a' b := by
  simp only [polar, ← zpow_neg, ← zpow_add]
  congr 1
  ring

def tateNumOf : NumOf (toricPre R ℤ fun n => q ^ n ^ 2) F (tate (Units.map (algebraMap (FractionRing R) F).toMonoidHom q)) :=
  let ν := toricNumOf (fun n : ℤ => q ^ n ^ 2) (fun n => by rw [neg_sq]) (polar_sq q) F
  { J := ν.J, good := ν.good, th := ν.th, th_gen := ν.th_gen, eA := ν.eA, eX := ν.eX, c_eq := ν.c_eq, θ_eq := ν.θ_eq
    σ_eq := ν.σ_eq, th_eq := ν.th_eq
    ψ_eq := fun (n : ℤ) => (congrArg Units.val (map_zpow _ q (n ^ 2)).symm).trans (ν.ψ_eq n) }

end Tate

end Settings

section GoodMdl
open UnifModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

end GoodMdl

end StepInh
end GlobalTheory.Ex
end
