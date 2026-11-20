import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IntOfPrimeMulSq

namespace GlobalTheory.BaseRing

section
open Polynomial

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap A L)`. Rewrite using `[IsScalarTower.algebraMap_eq A K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective A K)`. Establish `: Module.IsTorsionFree A L`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`.

Conclude with `hinj`. Establish `h1 : z ∈ (Algebra.traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin A {x}))`. Introduce `y hy`. Establish `hy' : IsIntegral A y` using `(show Algebra.adjoin A {x} ≤ integralClosure A L from Algebra.adjoin_le (Set.singleton_subset_iff.mpr hAx)) hy`. Use `Algebra.isIntegral_trace (L := K) (hz.mul hy')` as an intermediate fact.

Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp this`. Rewrite using `[Algebra.traceForm_apply, ← ha]`. Conclude with `Submodule.mem_one.mpr ⟨a, rfl⟩`. Rewrite `h1` using `[traceForm_dualSubmodule_adjoin A K hx hAx]`. Establish `hne : aeval x (derivative (minpoly K x)) ≠ 0` using `(Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)`.

Rewrite `h1` using `[Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hne), inv_inv, minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, derivative_map, aeval_map_algebraMap]`. Take `⟨g, hg⟩` from `minpoly.isIntegrallyClosed_dvd hAx hf`. Establish `: aeval x (derivative f) * z = aeval x g * (aeval x (derivative (minpoly A x)) * z)`. Rewrite using `[hg, derivative_mul]`. Simplify using `only [map_add, map_mul, minpoly.aeval]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Subalgebra.mul_mem _ (aeval_mem_adjoin_singleton _ _) h1`.
-/
theorem aeval_derivative_mul_mem_adjoin (A K : Type*) {L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K]
    [IsIntegrallyClosed A] [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
    (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) (f : A[X]) (hf : aeval x f = 0)
    {z : L} (hz : IsIntegral A z) : aeval x (derivative f) * z ∈ Algebra.adjoin A {x} := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  have h1 : z ∈ (Algebra.traceForm K L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
    intro y hy
    have hy' : IsIntegral A y :=
      (show Algebra.adjoin A {x} ≤ integralClosure A L from
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hAx)) hy
    have := Algebra.isIntegral_trace (L := K) (hz.mul hy')
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    rw [Algebra.traceForm_apply, ← ha]
    exact Submodule.mem_one.mpr ⟨a, rfl⟩
  rw [traceForm_dualSubmodule_adjoin A K hx hAx] at h1
  have hne : aeval x (derivative (minpoly K x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hne), inv_inv,
    minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, derivative_map,
    aeval_map_algebraMap] at h1
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hAx hf
  have : aeval x (derivative f) * z = aeval x g * (aeval x (derivative (minpoly A x)) * z) := by
    rw [hg, derivative_mul]
    simp only [map_add, map_mul, minpoly.aeval]
    ring
  rw [this]
  exact Subalgebra.mul_mem _ (aeval_mem_adjoin_singleton _ _) h1

open IntermediateField in

/- English proof (translation)
Establish `: NumberField K` using `{}`. Set `A` to `integralClosure ℤ K`. Establish `: IsFractionRing A K` using `integralClosure.isFractionRing_of_finite_extension ℚ K`. Establish `: IsIntegrallyClosed A` using `integralClosure.isIntegrallyClosedOfFiniteExtension ℚ`. Establish `hζi : IsIntegral ℤ ζ` using `IsIntegral.of_pow hn (hζ ▸ isIntegral_one)`.

Establish `hζK : IsIntegral K ζ` using `hζi.tower_top`. Establish `: FiniteDimensional K K⟮ζ⟯` using `adjoin.finiteDimensional hζK`. Set `x : K⟮ζ⟯` to `AdjoinSimple.gen K ζ`. Establish `hx : Algebra.adjoin K {x} = ⊤` using `(adjoin.powerBasis hζK).adjoin_gen_eq_top`. Establish `hint : ∀ y : K⟮ζ⟯, IsIntegral ℤ (y : ℂ) → IsIntegral A y` using `fun y hy => ((isIntegral_algHom_iff (K⟮ζ⟯.val.restrictScalars ℤ) Subtype.val_injective).mp hy).tower_top`.

Establish `hxn : x ^ n = 1` using `Subtype.ext hζ`. Establish `h` using `aeval_derivative_mul_mem_adjoin A K hx (hint x hζi) (X ^ n - 1) (by simp [hxn]) (hint ⟨z, hzK⟩ hz)`. Establish `hsub : ∀ y ∈ Algebra.adjoin A {x}, (y : ℂ) ∈ T`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem y hy => rw [Set.mem_singleton_iff.mp hy]`. Conclude with `hζT`. Consider the case `algebraMap a`. Conclude with `hT _ a.1.2 ((isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mpr a.2)`. Consider the case `add a b _ _ ha hb => exact T.add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => exact T.mul_mem ha hb`. Establish `h2` using `T.mul_mem hζT (hsub _ h)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `hxc : (x : ℂ) = ζ` using `rfl`.

Simplify using `[derivative_X_pow, hxc]`. Take the linear combination `(-(m + 1 : ℂ) * z) * hζ`.
-/
theorem natCast_mul_mem_of_isIntegral (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (T : Subring ℂ) (hT : ∀ w ∈ K, IsIntegral ℤ w → w ∈ T) {ζ : ℂ} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ n = 1) (hζT : ζ ∈ T) {z : ℂ} (hzK : z ∈ K⟮ζ⟯) (hz : IsIntegral ℤ z) :
    (n : ℂ) * z ∈ T := by
  have : NumberField K := {}
  let A := integralClosure ℤ K
  have : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension ℚ K
  have : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension ℚ
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (hζ ▸ isIntegral_one)
  have hζK : IsIntegral K ζ := hζi.tower_top
  have : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hζK
  let x : K⟮ζ⟯ := AdjoinSimple.gen K ζ
  have hx : Algebra.adjoin K {x} = ⊤ := (adjoin.powerBasis hζK).adjoin_gen_eq_top
  have hint : ∀ y : K⟮ζ⟯, IsIntegral ℤ (y : ℂ) → IsIntegral A y := fun y hy =>
    ((isIntegral_algHom_iff (K⟮ζ⟯.val.restrictScalars ℤ) Subtype.val_injective).mp hy).tower_top
  have hxn : x ^ n = 1 := Subtype.ext hζ
  have h := aeval_derivative_mul_mem_adjoin A K hx (hint x hζi) (X ^ n - 1) (by simp [hxn])
    (hint ⟨z, hzK⟩ hz)
  have hsub : ∀ y ∈ Algebra.adjoin A {x}, (y : ℂ) ∈ T := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hζT
    | algebraMap a =>
      exact hT _ a.1.2 ((isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mpr a.2)
    | add a b _ _ ha hb => exact T.add_mem ha hb
    | mul a b _ _ ha hb => exact T.mul_mem ha hb
  have h2 := T.mul_mem hζT (hsub _ h)
  convert h2 using 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hxc : (x : ℂ) = ζ := rfl
  simp [derivative_X_pow, hxc]
  linear_combination (-(m + 1 : ℂ) * z) * hζ

open IntermediateField in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RationalIntegralCoordinates.main`. Consider the case `exact _root_.GlobalTheory.RationalIntegralCoordinates.main`. Consider the case `(apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RationalIntegralCoordinates.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RationalIntegralCoordinates.main ..)`.
-/
theorem mem_of_isIntegral_quadratic {d : ℕ} (hd : d.Prime) (hd4 : d % 4 = 3) {r : ℂ}
    (hr : r ^ 2 = -(d : ℂ)) (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ} (hzK : z ∈ ℚ⟮r⟯)
    (hz : IsIntegral ℤ z) : z ∈ T := by
  first
  | exact @_root_.GlobalTheory.RationalIntegralCoordinates.main
  | exact _root_.GlobalTheory.RationalIntegralCoordinates.main
  | (apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RationalIntegralCoordinates.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RationalIntegralCoordinates.main ..)

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `(Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one`.
-/
theorem zeta_pow_self {n : ℕ} (hn : 0 < n) : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one

/- English proof (translation)
The claim follows from `IsIntegral.of_pow two_pos (H.sqrt_neg_disc_sq ▸ (isIntegral_natCast H.d).neg)`.
-/
theorem isIntegral_sqrt_discriminant (H : Host E) : IsIntegral ℤ H.rt0 :=
  IsIntegral.of_pow two_pos (H.sqrt_neg_disc_sq ▸ (isIntegral_natCast H.d).neg)

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c : ℕ, H.d + 1 = 4 * c` from `⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩`. Establish `hc' : (H.d : ℂ) + 1 = 4 * c` using `by exact_mod_cast hc`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Take the linear combination `(1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hc'`.
-/
theorem isIntegral_half_one_add_sqrt (H : Host E) : IsIntegral ℤ ((1 + H.rt0) / 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, H.d + 1 = 4 * c := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hc' : (H.d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
  simp
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hc'

/- English proof (translation)
Use `IntermediateField.finiteDimensional_adjoin fun x hx => ?_` and prove the remaining obligations. Break down `hx with rfl | rfl` into its components or cases. Conclude with `(isIntegral_sqrt_discriminant H).tower_top`. Conclude with `IsIntegral.of_pow l.A_pos (zeta_pow_self l.A_pos ▸ isIntegral_one)`.
-/
theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · exact (isIntegral_sqrt_discriminant H).tower_top
  · exact IsIntegral.of_pow l.A_pos (zeta_pow_self l.A_pos ▸ isIntegral_one)

/- English proof (translation)
Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Establish `h1 : H.rt0 ∈ KA l` using `IntermediateField.subset_adjoin _ _ (by simp)`. Introduce and unpack `x (rfl | rfl | rfl)`. Conclude with `show _ ∈ KA l from div_mem (add_mem (one_mem (KA l)) h1) (ofNat_mem (KA l) 2)`. Conclude with `show _ ∈ KA l from inv_mem (natCast_mem (KA l) S)`.

Conclude with `IntermediateField.subset_adjoin ℚ {H.rt0, zeta l.A} (by simp)`.
-/
theorem RZ_le_KA (l : Level H) (S : ℕ) : RZ H S l.A ≤ (KA l).toSubalgebra.toSubring := by
  refine Subring.closure_le.mpr ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  rintro x (rfl | rfl | rfl)
  · exact show _ ∈ KA l from div_mem (add_mem (one_mem (KA l)) h1) (ofNat_mem (KA l) 2)
  · exact show _ ∈ KA l from inv_mem (natCast_mem (KA l) S)
  · exact IntermediateField.subset_adjoin ℚ {H.rt0, zeta l.A} (by simp)

open IntermediateField in

/- English proof (translation)
Establish `: FiniteDimensional ℚ ℚ⟮H.rt0⟯` using `adjoin.finiteDimensional (isIntegral_sqrt_discriminant H).tower_top`. Establish `h` using `natCast_mul_mem_of_isIntegral ℚ⟮H.rt0⟯ (RZ H S l.A) (fun w hw hw' => mem_of_isIntegral_quadratic H.d_prime (by have := H.d_mod; omega) H.sqrt_neg_disc_sq _ (Subring.subset_closure (by simp)) hw hw') l.A_pos (zeta_pow_self l.A_pos) (Subring.subset_closure (by simp)) (z := z) ((mem …`. Take `⟨c, hc⟩` from `hA`. Establish `hc' : (S : ℂ) ^ e = l.A * c` using `by exact_mod_cast hc`. Establish `hS' : (S : ℂ) ≠ 0` using `by exact_mod_cast hS.ne'`.

Establish `hi : (S : ℂ)⁻¹ ∈ RZ H S l.A` using `Subring.subset_closure (by simp)`. Establish `: z = (S : ℂ)⁻¹ ^ e * (c * (l.A * z))`. Establish `h1 : (S : ℂ)⁻¹ ^ e * S ^ e = 1` using `by rw [← mul_pow, inv_mul_cancel₀ hS', one_pow]`. Rewrite `h1` using `[hc']`. Take the linear combination `(-z) * h1`.

Rewrite using `[this]`. Conclude with `mul_mem (pow_mem hi e) (mul_mem (natCast_mem _ c) h)`.
-/
theorem mem_RZ_of_isIntegral (l : Level H) {S e : ℕ} (hS : 0 < S) (hA : l.A ∣ S ^ e) {z : ℂ}
    (hzK : z ∈ KA l) (hz : IsIntegral ℤ z) : z ∈ RZ H S l.A := by
  have : FiniteDimensional ℚ ℚ⟮H.rt0⟯ := adjoin.finiteDimensional (isIntegral_sqrt_discriminant H).tower_top
  have h := natCast_mul_mem_of_isIntegral ℚ⟮H.rt0⟯ (RZ H S l.A)
    (fun w hw hw' => mem_of_isIntegral_quadratic H.d_prime (by have := H.d_mod; omega) H.sqrt_neg_disc_sq _
      (Subring.subset_closure (by simp)) hw hw') l.A_pos (zeta_pow_self l.A_pos)
    (Subring.subset_closure (by simp)) (z := z)
    ((mem_restrictScalars ℚ).mp ((adjoin_simple_adjoin_simple ℚ H.rt0 (zeta l.A)).ge hzK)) hz
  obtain ⟨c, hc⟩ := hA
  have hc' : (S : ℂ) ^ e = l.A * c := by exact_mod_cast hc
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hi : (S : ℂ)⁻¹ ∈ RZ H S l.A := Subring.subset_closure (by simp)
  have : z = (S : ℂ)⁻¹ ^ e * (c * (l.A * z)) := by
    have h1 : (S : ℂ)⁻¹ ^ e * S ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ hS', one_pow]
    rw [hc'] at h1
    linear_combination (-z) * h1
  rw [this]
  exact mul_mem (pow_mem hi e) (mul_mem (natCast_mem _ c) h)

/- English proof (translation)
Establish `hS' : (S : ℂ) ≠ 0` using `by exact_mod_cast hS.ne'`. Establish `hp : ∀ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k)` using `fun k => (isIntegral_natCast S).pow k`. Proceed by induction on `hz using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl | rfl` into its components or cases.

Conclude with `⟨0, by simpa using isIntegral_half_one_add_sqrt H⟩`. Conclude with `⟨1, by simpa [hS'] using isIntegral_one⟩`. Conclude with `⟨0, by simpa using IsIntegral.of_pow hA (zeta_pow_self hA ▸ isIntegral_one)⟩`. Consider the case `zero => exact ⟨0, by simpa using isIntegral_zero⟩`. Consider the case `one => exact ⟨0, by simpa using isIntegral_one⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Establish `e : (S : ℂ) ^ (a + b) * (x + y) = S ^ b * (S ^ a * x) + S ^ a * (S ^ b * y)` using `by ring`. Conclude with `⟨a + b, e ▸ ((hp b).mul ha).add ((hp a).mul hb)⟩`.

Consider the case `neg x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨a, by simpa using ha.neg⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Establish `e : (S : ℂ) ^ (a + b) * (x * y) = (S ^ a * x) * (S ^ b * y)` using `by ring`. Conclude with `⟨a + b, e ▸ ha.mul hb⟩`.
-/
theorem exists_pow_mul_isIntegral (H : Host E) {S A : ℕ} (hS : 0 < S) (hA : 0 < A) {z : ℂ}
    (hz : z ∈ RZ H S A) : ∃ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k * z) := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hp : ∀ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k) := fun k => (isIntegral_natCast S).pow k
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simpa using isIntegral_half_one_add_sqrt H⟩
    · exact ⟨1, by simpa [hS'] using isIntegral_one⟩
    · exact ⟨0, by simpa using IsIntegral.of_pow hA (zeta_pow_self hA ▸ isIntegral_one)⟩
  | zero => exact ⟨0, by simpa using isIntegral_zero⟩
  | one => exact ⟨0, by simpa using isIntegral_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x + y) = S ^ b * (S ^ a * x) + S ^ a * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ((hp b).mul ha).add ((hp a).mul hb)⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simpa using ha.neg⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x * y) = (S ^ a * x) * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ha.mul hb⟩

/- English proof (translation)
Establish `h : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).FG` using `Subalgebra.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩`. Establish `h2` using `(Subalgebra.fg_iff_finiteType _).mp h`. Establish `h3 : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).toSubring = RZ H S A`. Rewrite using `[Algebra.adjoin_int]`. Both sides reduce to the same expression.

Conclude with `h2.equiv (RingEquiv.subringCongr h3).toIntAlgEquiv`.
-/
theorem finiteType_RZ (H : Host E) (S A : ℕ) : Algebra.FiniteType ℤ (RZ H S A) := by
  classical
  have h : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩
  have h2 := (Subalgebra.fg_iff_finiteType _).mp h
  have h3 : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).toSubring = RZ H S A := by
    rw [Algebra.adjoin_int]; rfl
  exact h2.equiv (RingEquiv.subringCongr h3).toIntAlgEquiv

/- English proof (translation)
Use `finiteDimensional_KA l` as an intermediate fact. Establish `: NumberField (KA l)` using `{}`. Establish `hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y` using `fun y => isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective`. Set `φ : 𝓞 (KA l) →+* RZ H S l.A` to `((KA l).val.toRingHom.comp (algebraMap (𝓞 (KA l)) (KA l))).codRestrict _ fun a => mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)`. Establish `hφ : ∀ a, (φ a : ℂ) = ((a : KA l) : ℂ)` using `fun _ => rfl`.

Use `letI : Algebra (𝓞 (KA l)) (RZ H S l.A) := φ.toAlgebra`. Establish `hS' : (S : ℂ) ≠ 0` using `by exact_mod_cast hS.ne'`. Establish `hi : (S : ℂ)⁻¹ ∈ RZ H S l.A` using `Subring.subset_closure (by simp)`. Establish `: IsLocalization (Submonoid.powers (S : 𝓞 (KA l))) (RZ H S l.A)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨_, k, rfl⟩`. Simplify using `only [map_pow, map_natCast]`. Use `IsUnit.pow k (IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext ?_))` and prove the remaining obligations. Simplify using `[hS']`. Introduce `z`.

Take `⟨k, hk⟩` from `exists_pow_mul_isIntegral H hS l.A_pos z.2`. Establish `hm : (S : ℂ) ^ k * z ∈ KA l` using `mul_mem (pow_mem (natCast_mem _ S) k) (RZ_le_KA l S z.2)`. Use `⟨(⟨⟨_, hm⟩, (hint _).mp hk⟩, ⟨_, k, rfl⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [map_pow, map_natCast]`. Use `push_cast`.

Conclude with `mul_comm _ _`. Introduce `x y h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: x = y` using `RingOfIntegers.ext (Subtype.ext (by`. Rewrite using `[← hφ, ← hφ]`.

Conclude with `congrArg Subtype.val h))`. Rewrite using `[this]`. Conclude with `IsLocalization.isDedekindDomain (𝓞 (KA l)) (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hS.ne' : (S : 𝓞 (KA l)) ≠ 0)) _`.
-/
theorem isDedekindDomain_RZ (l : Level H) {S e : ℕ} (hS : 0 < S) (hA : l.A ∣ S ^ e) :
    IsDedekindDomain (RZ H S l.A) := by
  have := finiteDimensional_KA l
  have : NumberField (KA l) := {}
  have hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y := fun y =>
    isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective
  let φ : 𝓞 (KA l) →+* RZ H S l.A :=
    ((KA l).val.toRingHom.comp (algebraMap (𝓞 (KA l)) (KA l))).codRestrict _ fun a =>
      mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)
  have hφ : ∀ a, (φ a : ℂ) = ((a : KA l) : ℂ) := fun _ => rfl
  letI : Algebra (𝓞 (KA l)) (RZ H S l.A) := φ.toAlgebra
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hi : (S : ℂ)⁻¹ ∈ RZ H S l.A := Subring.subset_closure (by simp)
  have : IsLocalization (Submonoid.powers (S : 𝓞 (KA l))) (RZ H S l.A) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      simp only [map_pow, map_natCast]
      refine IsUnit.pow k (IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext ?_))
      simp [hS']
    · intro z
      obtain ⟨k, hk⟩ := exists_pow_mul_isIntegral H hS l.A_pos z.2
      have hm : (S : ℂ) ^ k * z ∈ KA l :=
        mul_mem (pow_mem (natCast_mem _ S) k) (RZ_le_KA l S z.2)
      refine ⟨(⟨⟨_, hm⟩, (hint _).mp hk⟩, ⟨_, k, rfl⟩), Subtype.ext ?_⟩
      simp only [map_pow, map_natCast]
      push_cast
      exact mul_comm _ _
    · intro x y h
      refine ⟨1, ?_⟩
      have : x = y := RingOfIntegers.ext (Subtype.ext (by
        rw [← hφ, ← hφ]; exact congrArg Subtype.val h))
      rw [this]
  exact IsLocalization.isDedekindDomain (𝓞 (KA l))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hS.ne' : (S : 𝓞 (KA l)) ≠ 0)) _

/- English proof (translation)
Introduce `E _ _ _ H l S e hS hA`. Use `⟨⟨Subring.inclusion (RZ_le_KA l S), fun _ => rfl⟩, finiteType_RZ H S l.A, fun β hβ => ?_⟩` and prove the remaining obligations. Use `⟨⟨inferInstance, isDedekindDomain_RZ l hS hA⟩, inferInstance, ?_⟩` and prove the remaining obligations. Use `letI := β.toAlgebra`. Establish `hβ' : ∀ x, ((algebraMap (RZ H S l.A) (KA l) x : KA l) : ℂ) = x` using `hβ`.

Establish `hinj : Function.Injective (algebraMap (RZ H S l.A) (KA l))` using `fun x y h => Subtype.ext (by rw [← hβ' x, ← hβ' y, h])`. Use `finiteDimensional_KA l` as an intermediate fact. Establish `: NumberField (KA l)` using `{}`. Establish `hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y` using `fun y => isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective`. Establish `hmem : ∀ a : 𝓞 (KA l), ((a : KA l) : ℂ) ∈ RZ H S l.A` using `fun a => mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)`.

Establish `: FaithfulSMul (RZ H S l.A) (KA l)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Use `IsFractionRing.of_field _ _ fun z => ?_` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 (KA l)) z`. Use `⟨⟨_, hmem a⟩, ⟨_, hmem b⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `congr 1 <;> exact Subtype.ext (by rw [hβ'])`.
-/
theorem isDedFrac_RZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (S e : ℕ), 0 < S → l.A ∣ S ^ e → (∃ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S l.A) ∧ ∀ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  intro E _ _ _ H l S e hS hA
  refine ⟨⟨Subring.inclusion (RZ_le_KA l S), fun _ => rfl⟩, finiteType_RZ H S l.A, fun β hβ => ?_⟩
  refine ⟨⟨inferInstance, isDedekindDomain_RZ l hS hA⟩, inferInstance, ?_⟩
  letI := β.toAlgebra
  have hβ' : ∀ x, ((algebraMap (RZ H S l.A) (KA l) x : KA l) : ℂ) = x := hβ
  have hinj : Function.Injective (algebraMap (RZ H S l.A) (KA l)) := fun x y h =>
    Subtype.ext (by rw [← hβ' x, ← hβ' y, h])
  have := finiteDimensional_KA l
  have : NumberField (KA l) := {}
  have hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y := fun y =>
    isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective
  have hmem : ∀ a : 𝓞 (KA l), ((a : KA l) : ℂ) ∈ RZ H S l.A := fun a =>
    mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)
  have : FaithfulSMul (RZ H S l.A) (KA l) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 (KA l)) z
  refine ⟨⟨_, hmem a⟩, ⟨_, hmem b⟩, ?_⟩
  congr 1 <;> exact Subtype.ext (by rw [hβ'])

end GlobalTheory.BaseRing
