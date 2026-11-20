import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Take `⟨y, hy⟩` from `hx.exists_right_inv`. Take `⟨y', rfl⟩` from `hs y`. Establish `h1 : x * y' - 1 ∈ RingHom.ker π` using `by simp [RingHom.mem_ker, hy]`. Establish `h2 : (x * y' - 1) ^ 2 = 0`. Use `Ideal.pow_mem_pow h1 2` as an intermediate fact.

Rewrite `this` using `[hk, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `h3 : IsUnit (x * y' - 1 + 1)` using `IsNilpotent.isUnit_add_one ⟨2, h2⟩`. Rewrite `h3` using `[sub_add_cancel]`. Conclude with `isUnit_of_mul_isUnit_left h3`.
-/
private theorem isUnit_of_isUnit_map_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (x : R') (hx : IsUnit (π x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := hs y
  have h1 : x * y' - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hy]
  have h2 : (x * y' - 1) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  have h3 : IsUnit (x * y' - 1 + 1) := IsNilpotent.isUnit_add_one ⟨2, h2⟩
  rw [sub_add_cancel] at h3
  exact isUnit_of_mul_isUnit_left h3

/- English proof (translation)
The claim follows from `(Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm`.
-/
private theorem ringHom_aeval_eq_aeval_apply {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

/- English proof (translation)
Take `⟨z₀, rfl⟩` from `hs z`. Establish `hu : IsUnit (Polynomial.aeval z₀ (derivative f))` using `isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ (by rwa [ringHom_aeval_eq_aeval_apply])`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Establish `h0 : π (Polynomial.aeval z₀ f) = 0` using `by rwa [ringHom_aeval_eq_aeval_apply]`. Establish `h1 : -(v * Polynomial.aeval z₀ f) ∈ RingHom.ker π`.

Rewrite using `[RingHom.mem_ker, map_neg, map_mul, h0, mul_zero, neg_zero]`. Establish `h2 : (-(v * Polynomial.aeval z₀ f)) ^ 2 = 0`. Use `Ideal.pow_mem_pow h1 2` as an intermediate fact. Rewrite `this` using `[hk, Ideal.mem_bot]`. Then use the resulting hypothesis. Use `⟨z₀ + -(v * Polynomial.aeval z₀ f), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, RingHom.mem_ker.mp h1, add_zero]`. Rewrite using `[Polynomial.aeval_add_of_sq_eq_zero _ _ _ h2, mul_neg, ← _root_.mul_assoc, hv, _root_.one_mul, add_neg_cancel]`.
-/
private theorem exists_root_lift_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (f : ℤ[X]) (z : R)
    (hz : Polynomial.aeval z f = 0) (hd : IsUnit (Polynomial.aeval z (derivative f))) :
    ∃ z' : R', π z' = z ∧ Polynomial.aeval z' f = 0 := by
  obtain ⟨z₀, rfl⟩ := hs z
  have hu : IsUnit (Polynomial.aeval z₀ (derivative f)) :=
    isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ (by rwa [ringHom_aeval_eq_aeval_apply])
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h0 : π (Polynomial.aeval z₀ f) = 0 := by rwa [ringHom_aeval_eq_aeval_apply]
  have h1 : -(v * Polynomial.aeval z₀ f) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_neg, map_mul, h0, mul_zero, neg_zero]
  have h2 : (-(v * Polynomial.aeval z₀ f)) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  refine ⟨z₀ + -(v * Polynomial.aeval z₀ f), ?_, ?_⟩
  · rw [map_add, RingHom.mem_ker.mp h1, add_zero]
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ h2, mul_neg, ← _root_.mul_assoc, hv, _root_.one_mul,
      add_neg_cancel]

/- English proof (translation)
Take `⟨g, hg⟩` from `cyclotomic.dvd_X_pow_sub_one M ℤ`. Establish `h1 : z ^ M = 1`. Use `congrArg (Polynomial.aeval z) hg` as an intermediate fact. Rewrite `this` using `[map_mul, hz, zero_mul]`. Simplify `this` using `[sub_eq_zero]`.

Establish `hzu : IsUnit z` using `IsUnit.of_pow_eq_one h1 hM`. Establish `h2` using `congrArg (fun q => Polynomial.aeval z (derivative q)) hg`. Simplify using `only [derivative_mul, map_add, map_mul, hz, zero_mul, add_zero, derivative_sub, derivative_one, sub_zero, derivative_X_pow, map_natCast, map_pow, aeval_X] at h2`. Establish `h3 : IsUnit ((M : R) * z ^ (M - 1))` using `hu.mul (hzu.pow _)`. Rewrite `h3` using `[h2]`.

Conclude with `isUnit_of_mul_isUnit_left h3`.
-/
private theorem isUnit_aeval_derivative_cyclotomic {R : Type} [CommRing R] (M : ℕ) (hM : M ≠ 0) (hu : IsUnit (M : R))
    (z : R) (hz : Polynomial.aeval z (cyclotomic M ℤ) = 0) :
    IsUnit (Polynomial.aeval z (derivative (cyclotomic M ℤ))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one M ℤ
  have h1 : z ^ M = 1 := by
    have := congrArg (Polynomial.aeval z) hg
    rw [map_mul, hz, zero_mul] at this
    simpa [sub_eq_zero] using this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one h1 hM
  have h2 := congrArg (fun q => Polynomial.aeval z (derivative q)) hg
  simp only [derivative_mul, map_add, map_mul, hz, zero_mul, add_zero, derivative_sub,
    derivative_one, sub_zero, derivative_X_pow, map_natCast, map_pow, aeval_X] at h2
  have h3 : IsUnit ((M : R) * z ^ (M - 1)) := hu.mul (hzu.pow _)
  rw [h2] at h3
  exact isUnit_of_mul_isUnit_left h3

/- English proof (translation)
Set `φ : AdjoinRoot f →+* B` to `AdjoinRoot.lift (algebraMap ℤ B) ζ h0`. Set `α : AdjoinRoot f →+* R'` to `AdjoinRoot.lift (algebraMap ℤ R') z' hz'`. Establish `hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g` using `fun g => AdjoinRoot.lift_mk _ _`. Establish `hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z' g` using `fun g => AdjoinRoot.lift_mk _ _`. Use `letI : Algebra (AdjoinRoot f) B := φ.toAlgebra`.

Establish `halg : algebraMap (AdjoinRoot f) B = φ` using `rfl`. Set `S' : Submonoid (AdjoinRoot f)` to `S.map (Nat.castRingHom (AdjoinRoot f))`. Use `haveI : IsLocalization S' B := by`. Use `(isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨_, n, hn, rfl⟩`.

Simplify using `using hS n hn`. Take `⟨n, hn, g, hg⟩` from `hsurj b`. Use `⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [halg, hφ]`. Simplify using `using hg`.

Take `⟨a, rfl⟩` from `AdjoinRoot.mk_surjective a`. Take `⟨c, rfl⟩` from `AdjoinRoot.mk_surjective c`. Rewrite `h` using `[halg, hφ, hφ, ← sub_eq_zero, ← map_sub]`. Rewrite using `[AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]`. Establish `hu : ∀ y : S', IsUnit (α y)`.

Introduce and unpack `⟨_, n, hn, rfl⟩`. Use `isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ ?_` and prove the remaining obligations. Simplify using `using (hS n hn).map β`. Use `⟨IsLocalization.lift hu, IsLocalization.ringHom_ext S' ?_⟩` and prove the remaining obligations. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `AdjoinRoot.mk_surjective a`. Simplify using `only [RingHom.comp_apply, IsLocalization.lift_eq]`. Rewrite using `[halg, hφ, hα, ringHom_aeval_eq_aeval_apply, ringHom_aeval_eq_aeval_apply, hz]`.
-/
private theorem lift_squareZero_general {B R' R : Type} [CommRing B] [CommRing R'] [CommRing R]
    (π : R' →+* R) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (β : B →+* R) (z' : R') (hz : π z' = β ζ) (hz' : Polynomial.aeval z' f = 0) :
    ∃ β' : B →+* R', π.comp β' = β := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R' := AdjoinRoot.lift (algebraMap ℤ R') z' hz'
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z' g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ ?_
    simpa using (hS n hn).map β
  refine ⟨IsLocalization.lift hu, IsLocalization.ringHom_ext S' ?_⟩
  refine RingHom.ext fun a => ?_
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  rw [halg, hφ, hα, ringHom_aeval_eq_aeval_apply, ringHom_aeval_eq_aeval_apply, hz]

private def liftZP_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

/- English proof (translation)
Establish `hmem : (n : ℂ)⁻¹ ∈ ZP p M` using `Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)`. Use `IsUnit.of_mul_eq_one (⟨_, hmem⟩ : ZP p M) (Subtype.ext ?_)` and prove the remaining obligations. Establish `: (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hn.1`. Simplify using `[this]`.
-/
private theorem isUnit_natCast_of_mem_denominators (p M n : ℕ) (hn : n ∈ liftZP_S p) : IsUnit (n : ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

/- English proof (translation)
Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with hx | ⟨n, hn, rfl⟩` into its components or cases. Conclude with `⟨1, one_mem _, Polynomial.X, by simpa using hx⟩`. Distinguish the cases in `h : n = 0`.

Conclude with `⟨1, one_mem _, 0, by simp [h]⟩`. Establish `: (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr h`. Conclude with `⟨n, ⟨h, hn⟩, 1, by simp [this]⟩`. Consider the case `zero => exact ⟨1, one_mem _, 0, by simp⟩`. Consider the case `one => exact ⟨1, one_mem _, 1, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨n, hn, g, hg⟩` from `hx`. Take `⟨m, hm, k, hk⟩` from `hy`. Use `⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`. Take `⟨n, hn, g, hg⟩` from `hx`. Conclude with `⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨n, hn, g, hg⟩` from `hx`. Take `⟨m, hm, k, hk⟩` from `hy`. Use `⟨n * m, mul_mem hn hm, g * k, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Nat.cast_mul, ← hg, ← hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_mul_eq_aeval_zeta_of_mem (p M : ℕ) (x : ℂ) (hx : x ∈ ZP p M) :
    ∃ n ∈ liftZP_S p, ∃ g : ℤ[X], x * (n : ℂ) = Polynomial.aeval (zeta M) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

/- English proof (translation)
Introduce `p M R' R _ _ π hs hk hMp hM β`. Establish `hprim : IsPrimitiveRoot (zeta M) M` using `Complex.isPrimitiveRoot_exp M hM`. Establish `hmin : cyclotomic M ℤ = minpoly ℤ (zeta M)` using `cyclotomic_eq_minpoly hprim (Nat.pos_of_ne_zero hM)`. Establish `hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (zetaZP p M) g : ZP p M) : ℂ) = Polynomial.aeval (zeta M) g` using `fun g => ringHom_aeval_eq_aeval_apply (ZP p M).subtype g _`. Establish `h0 : Polynomial.aeval (zetaZP p M) (cyclotomic M ℤ) = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcoe, hmin]`. Conclude with `minpoly.aeval _ _`. Establish `hβ0 : Polynomial.aeval (β (zetaZP p M)) (cyclotomic M ℤ) = 0`. Rewrite using `[← ringHom_aeval_eq_aeval_apply, h0, map_zero]`.

Establish `hMu : IsUnit (M : R)` using `by simpa using (isUnit_natCast_of_mem_denominators p M M ⟨hM, hMp⟩).map β`. Take `⟨z', hz, hz'⟩` from `exists_root_lift_of_ker_sq_eq_bot π hs hk _ _ hβ0 (isUnit_aeval_derivative_cyclotomic M hM hMu _ hβ0)`. Use `lift_squareZero_general π hs hk (cyclotomic M ℤ) (zetaZP p M) (liftZP_S p) h0 ?_ (isUnit_natCast_of_mem_denominators p M) ?_ β z' hz hz'` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[hmin]`.

Use `minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (Nat.pos_of_ne_zero hM)) ?_` and prove the remaining obligations. Rewrite using `[← hcoe, hg]`. Both sides reduce to the same expression. Introduce `b`. Take `⟨n, hn, g, hg⟩` from `exists_mul_eq_aeval_zeta_of_mem p M b b.2`.

Conclude with `⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩`.
-/
theorem zp_lift_sqZero :
  (∀ (p M : ℕ) (R' R : Type) [CommRing R'] [CommRing R] (π : R' →+* R), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → M.Coprime p → M ≠ 0 →
    ∀ β : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R, ∃ β' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R', π.comp β' = β) := by
  intro p M R' R _ _ π hs hk hMp hM β
  have hprim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have hmin : cyclotomic M ℤ = minpoly ℤ (zeta M) :=
    cyclotomic_eq_minpoly hprim (Nat.pos_of_ne_zero hM)
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (zetaZP p M) g : ZP p M) : ℂ)
      = Polynomial.aeval (zeta M) g := fun g => ringHom_aeval_eq_aeval_apply (ZP p M).subtype g _
  have h0 : Polynomial.aeval (zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  have hβ0 : Polynomial.aeval (β (zetaZP p M)) (cyclotomic M ℤ) = 0 := by
    rw [← ringHom_aeval_eq_aeval_apply, h0, map_zero]
  have hMu : IsUnit (M : R) := by simpa using (isUnit_natCast_of_mem_denominators p M M ⟨hM, hMp⟩).map β
  obtain ⟨z', hz, hz'⟩ := exists_root_lift_of_ker_sq_eq_bot π hs hk _ _ hβ0 (isUnit_aeval_derivative_cyclotomic M hM hMu _ hβ0)
  refine lift_squareZero_general π hs hk (cyclotomic M ℤ) (zetaZP p M) (liftZP_S p) h0 ?_
    (isUnit_natCast_of_mem_denominators p M) ?_ β z' hz hz'
  · intro g hg
    rw [hmin]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (Nat.pos_of_ne_zero hM)) ?_
    rw [← hcoe, hg]
    rfl
  · intro b
    obtain ⟨n, hn, g, hg⟩ := exists_mul_eq_aeval_zeta_of_mem p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩

end GlobalTheory
