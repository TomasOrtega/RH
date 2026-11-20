import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA`. Use `letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra`. Establish `hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x)` using `fun _ => rfl`. Set `e0 : FractionRing R →+* L` to `IsFractionRing.lift he`. Establish `he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a` using `fun a => IsFractionRing.lift_algebraMap he a`.

Establish `hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x` using `fun x => by`. Rewrite using `[hΩ, he0, hce]`. Set `e' : FractionRing R →ₐ[Ω] L` to `{ e0 with commutes' := hcom }`. Set `s0 : G → FractionRing R ≃+* FractionRing R` to `fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)`. Establish `hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a)` using `fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a`.

Set `sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R` to `fun g => AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])`. Set `ga' : S → FractionRing R ≃+* FractionRing R` to `fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)`. Establish `hunit : ∀ y : nonZeroDivisors R, IsUnit (A y)` using `fun y => hA y (nonZeroDivisors.ne_zero y.2)`. Set `A' : FractionRing R →+* M` to `IsLocalization.lift (M := nonZeroDivisors R) hunit`. Use `⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A', IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `f`. Take `⟨x, y, hy, hxy⟩` from `IsFractionRing.div_surjective R f`. Use `⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩` and prove the remaining obligations. Establish `hy' : algebraMap R (FractionRing R) y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Rewrite using `[← hxy, div_mul_cancel₀ _ hy']`.

Introduce `g a`. Conclude with `hs0 g a`. Introduce `s a`. Conclude with `IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a`. Introduce `a`.

Conclude with `IsLocalization.lift_eq hunit a`.
-/
theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
