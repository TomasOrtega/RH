import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil

/- English proof (translation)
Use `choose k x hk hx using hs`. Establish `hkq : ∀ u, (k u : ℚ) ≠ 0` using `fun u => Nat.cast_ne_zero.mpr (hk u)`. Set `B0 : V → V → ℚ` to `fun u v => ((form (x u) (x v) : ℤ) : ℚ) / ((k u : ℚ) * (k v : ℚ))`. Establish `key : ∀ (u v : V) (m n : ℕ) (p q : Λ), m ≠ 0 → n ≠ 0 → e p = m • u → e q = n • v → B0 u v = ((form p q : ℤ) : ℚ) / ((m : ℚ) * (n : ℚ))`. Introduce `u v m n p q hm hn hp hq`.

Establish `h1 : (k u) • p = m • x u` using `he (by`. Rewrite using `[map_nsmul, map_nsmul, hp, hx, smul_comm])`. Establish `h2 : (k v) • q = n • x v` using `he (by`. Rewrite using `[map_nsmul, map_nsmul, hq, hx, smul_comm])`. Establish `h3 : form ((k u) • p) ((k v) • q) = form (m • x u) (n • x v)` using `by rw [h1, h2]`.

Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3`. Establish `h4 : (k v : ℚ) * ((k u : ℚ) * ((form p q : ℤ) : ℚ)) = (n : ℚ) * ((m : ℚ) * ((form (x u) (x v) : ℤ) : ℚ))`. Conclude with `h3` after adjusting the coercions. Establish `hm' : (m : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hm`. Establish `hn' : (n : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hn`.

Establish `hu` using `hkq u`. Establish `hv` using `hkq v`. Simplify using `only [B0]`. Rewrite using `[div_eq_div_iff (mul_ne_zero hu hv) (mul_ne_zero hm' hn')]`. Take the linear combination `(-1 : ℚ) * h4`.

Establish `hsm : ∀ (c : ℚ) (u : V), e (c.num • x u) = (c.den * k u) • (c • u)`. Introduce `c u`. Rewrite using `[map_zsmul, hx, ← Nat.cast_smul_eq_nsmul ℚ (k u) u, ← Nat.cast_smul_eq_nsmul ℚ (c.den * k u), ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]`. Use `congr 1`. Use `Rat.mul_den_eq_num c` as an intermediate fact.

Use `push_cast`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Set `B : LinearMap.BilinForm ℚ V` to `LinearMap.mk₂ ℚ B0 (by`. Introduce `u u' v`.

Use `key (u + u') v (k u * k u') (k v) ((k u') • x u + (k u) • x u') (x v) (mul_ne_zero (hk u) (hk u')) (hk v) (by rw [map_add, map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul, mul_comm (k u') (k u)]) (hx v)` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, B0, nsmul_eq_mul]`. Establish `hu` using `hkq u`. Establish `hu'` using `hkq u'`.

Establish `hv` using `hkq v`. Use `push_cast`. Use the proof step `field_simp)`. Use the proof step `(by`. Introduce `c u v`.

Use `key (c • u) v (c.den * k u) (k v) (c.num • x u) (x v) (mul_ne_zero c.den_nz (hk u)) (hk v) (hsm c u) (hx v)` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [map_zsmul, LinearMap.smul_apply, B0, zsmul_eq_mul, smul_eq_mul]`. Establish `hu` using `hkq u`. Establish `hv` using `hkq v`.

Establish `hd : (c.den : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr c.den_nz`. Establish `hc : c = (c.num : ℚ) / (c.den : ℚ)` using `(Rat.num_div_den c).symm`. Use `push_cast`. Use `conv_rhs => rw [hc]`. Use the proof step `field_simp)`.

Use the proof step `(by`. Introduce `u v v'`. Use `key u (v + v') (k u) (k v * k v') (x u) ((k v') • x v + (k v) • x v') (hk u) (mul_ne_zero (hk v) (hk v')) (hx u) (by rw [map_add, map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul, mul_comm (k v') (k v)])` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [map_add, map_nsmul, B0, nsmul_eq_mul]`.

Establish `hu` using `hkq u`. Establish `hv` using `hkq v`. Establish `hv'` using `hkq v'`. Use `push_cast`. Use the proof step `field_simp)`.

Use the proof step `(by`. Introduce `c u v`. Use `key u (c • v) (k u) (c.den * k v) (x u) (c.num • x v) (hk u) (mul_ne_zero c.den_nz (hk v)) (hx u) (hsm c v)` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [map_zsmul, B0, zsmul_eq_mul, smul_eq_mul]`.

Establish `hu` using `hkq u`. Establish `hv` using `hkq v`. Establish `hd : (c.den : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr c.den_nz`. Establish `hc : c = (c.num : ℚ) / (c.den : ℚ)` using `(Rat.num_div_den c).symm`. Use `push_cast`.

Use `conv_rhs => rw [hc]`. Use the proof step `field_simp)`. Use `⟨B, fun p q => ?_⟩` and prove the remaining obligations. Use `key (e p) (e q) 1 1 p q one_ne_zero one_ne_zero (one_smul _ _).symm (one_smul _ _).symm` as an intermediate fact. Simplify `this` using `[B, LinearMap.mk₂_apply]`.
-/
theorem exists_bilin_ext {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] [Module ℚ V]
    (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ v : V, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ) := by
  classical
  choose k x hk hx using hs
  have hkq : ∀ u, (k u : ℚ) ≠ 0 := fun u => Nat.cast_ne_zero.mpr (hk u)
  let B0 : V → V → ℚ := fun u v => ((form (x u) (x v) : ℤ) : ℚ) / ((k u : ℚ) * (k v : ℚ))
  have key : ∀ (u v : V) (m n : ℕ) (p q : Λ), m ≠ 0 → n ≠ 0 → e p = m • u → e q = n • v →
      B0 u v = ((form p q : ℤ) : ℚ) / ((m : ℚ) * (n : ℚ)) := by
    intro u v m n p q hm hn hp hq
    have h1 : (k u) • p = m • x u := he (by
      rw [map_nsmul, map_nsmul, hp, hx, smul_comm])
    have h2 : (k v) • q = n • x v := he (by
      rw [map_nsmul, map_nsmul, hq, hx, smul_comm])
    have h3 : form ((k u) • p) ((k v) • q) = form (m • x u) (n • x v) := by rw [h1, h2]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
    have h4 : (k v : ℚ) * ((k u : ℚ) * ((form p q : ℤ) : ℚ))
        = (n : ℚ) * ((m : ℚ) * ((form (x u) (x v) : ℤ) : ℚ)) := by
      exact_mod_cast h3
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hu := hkq u
    have hv := hkq v
    simp only [B0]
    rw [div_eq_div_iff (mul_ne_zero hu hv) (mul_ne_zero hm' hn')]
    linear_combination (-1 : ℚ) * h4
  have hsm : ∀ (c : ℚ) (u : V), e (c.num • x u) = (c.den * k u) • (c • u) := by
    intro c u
    rw [map_zsmul, hx, ← Nat.cast_smul_eq_nsmul ℚ (k u) u, ← Nat.cast_smul_eq_nsmul ℚ (c.den * k u),
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    have := Rat.mul_den_eq_num c
    push_cast
    rw [← this]; ring
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ B0
    (by
      intro u u' v
      have := key (u + u') v (k u * k u') (k v) ((k u') • x u + (k u) • x u') (x v)
        (mul_ne_zero (hk u) (hk u')) (hk v)
        (by rw [map_add, map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k u') (k u)])
        (hx v)
      rw [this]
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, B0, nsmul_eq_mul]
      have hu := hkq u
      have hu' := hkq u'
      have hv := hkq v
      push_cast
      field_simp)
    (by
      intro c u v
      have := key (c • u) v (c.den * k u) (k v) (c.num • x u) (x v)
        (mul_ne_zero c.den_nz (hk u)) (hk v) (hsm c u) (hx v)
      rw [this]
      simp only [map_zsmul, LinearMap.smul_apply, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
    (by
      intro u v v'
      have := key u (v + v') (k u) (k v * k v') (x u) ((k v') • x v + (k v) • x v')
        (hk u) (mul_ne_zero (hk v) (hk v')) (hx u)
        (by rw [map_add, map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k v') (k v)])
      rw [this]
      simp only [map_add, map_nsmul, B0, nsmul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hv' := hkq v'
      push_cast
      field_simp)
    (by
      intro c u v
      have := key u (c • v) (k u) (c.den * k v) (x u) (c.num • x v)
        (hk u) (mul_ne_zero c.den_nz (hk v)) (hx u) (hsm c v)
      rw [this]
      simp only [map_zsmul, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
  refine ⟨B, fun p q => ?_⟩
  have := key (e p) (e q) 1 1 p q one_ne_zero one_ne_zero (one_smul _ _).symm (one_smul _ _).symm
  simpa [B, LinearMap.mk₂_apply] using this

/- English proof (translation)
Introduce `E _ _ _ Λ _ _ _ _ N e he hlin hs form alt hbij adj`. Take `⟨B, hB⟩` from `exists_bilin_ext e he hs form`. Establish `hskew : ∀ x y, form x y = - form y x`. Introduce `x y`. Use `alt (x + y)` as an intermediate fact.

Simplify using `only [map_add, LinearMap.add_apply, alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `halt : ∀ u, B u u = 0`. Introduce `u`. Take `⟨k, x, hk, hx⟩` from `hs u`.

Establish `h` using `hB x x`. Rewrite `h` using `[alt, hx, ← Nat.cast_smul_eq_nsmul ℚ k u]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h`. Establish `hk' : (k : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hk`. Simplify `h` using `[hk']`.

Use `⟨B, hB, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a u v`. Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨n, hn, hint⟩` from `halg.exists_integral_multiple`. Take `⟨a₀, ha₀⟩ : ∃ a₀ : 𝓞 E, (a₀ : E) = n • a` from `⟨⟨n • a, hint⟩, rfl⟩`.

Take `⟨a₀', ha₀'⟩ : ∃ a₀' : 𝓞 E, (a₀' : E) = IsCMField.complexConj E (a₀ : E)` from `⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a₀, rfl⟩`. Take `⟨k, x, hk, hx⟩` from `hs u`. Take `⟨l, y, hl, hy⟩` from `hs v`. Establish `h2 : B (e (a₀ • x)) (e y) = B (e x) (e (a₀' • y))`. Rewrite using `[hB, hB, adj a₀ a₀' ha₀' x y]`.

Rewrite `h2` using `[hlin, hlin, hx, hy]`. Establish `h3 : (a₀ : E) • (k • u) = ((n : ℚ) * (k : ℚ)) • (a • u)`. Use extensionality with `i`. Simplify using `[ha₀, Rat.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4 : (a₀' : E) • (l • v) = ((n : ℚ) * (l : ℚ)) • (IsCMField.complexConj E a • v)`. Use extensionality with `i`. Simplify using `[ha₀', ha₀, Rat.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : k • u = (k : ℚ) • u` using `(Nat.cast_smul_eq_nsmul ℚ k u).symm`.

Establish `h6 : l • v = (l : ℚ) • v` using `(Nat.cast_smul_eq_nsmul ℚ l v).symm`. Rewrite `h2` using `[h3, h4, h5, h6]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2`. Establish `hn' : (n : ℚ) ≠ 0` using `Int.cast_ne_zero.mpr hn`. Establish `hk' : (k : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hk`.

Establish `hl' : (l : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hl`. Conclude with `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hn' hk') hl') (by linear_combination h2)`. Introduce `u v`. Conclude with `(LinearMap.IsAlt.neg (B := B) halt v u).symm`. Introduce `u hu`.

Take `⟨k, y, hk, hy⟩` from `hs u`. Establish `hf : ∀ x, form x y = 0`. Introduce `x`. Establish `h : B (e x) (e y) = 0` using `by rw [hy, map_nsmul, hu (e x), smul_zero]`. Rewrite `h` using `[hB]`.

Conclude with `h` after adjusting the coercions. Establish `h0 : form y = 0` using `LinearMap.ext fun x => by`. Rewrite using `[hskew, hf]`. Simplify using the standard rewrite rules. Establish `y0 : y = 0` using `hbij.1 (by rw [h0, map_zero])`.

Rewrite `hy` using `[y0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ]`. Conclude with `(smul_eq_zero.mp hy.symm).resolve_left (Nat.cast_ne_zero.mpr hk)`.
-/
theorem exists_rat_bilin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x, form x x = 0) → Function.Bijective form → (∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)) → ∃ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) ∧ (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) ∧ (∀ u v, B u v = - B v u) ∧ ∀ u, (∀ v, B v u = 0) → u = 0 := by
  intro E _ _ _ Λ _ _ _ _ N e he hlin hs form alt hbij adj
  obtain ⟨B, hB⟩ := exists_bilin_ext e he hs form
  have hskew : ∀ x y, form x y = - form y x := by
    intro x y
    have := alt (x + y)
    simp only [map_add, LinearMap.add_apply, alt] at this
    linarith
  have halt : ∀ u, B u u = 0 := by
    intro u
    obtain ⟨k, x, hk, hx⟩ := hs u
    have h := hB x x
    rw [alt, hx, ← Nat.cast_smul_eq_nsmul ℚ k u] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    simpa [hk'] using h
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro a u v
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝓞 E, (a₀ : E) = n • a := ⟨⟨n • a, hint⟩, rfl⟩
    obtain ⟨a₀', ha₀'⟩ : ∃ a₀' : 𝓞 E, (a₀' : E) = IsCMField.complexConj E (a₀ : E) :=
      ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a₀, rfl⟩
    obtain ⟨k, x, hk, hx⟩ := hs u
    obtain ⟨l, y, hl, hy⟩ := hs v
    have h2 : B (e (a₀ • x)) (e y) = B (e x) (e (a₀' • y)) := by
      rw [hB, hB, adj a₀ a₀' ha₀' x y]
    rw [hlin, hlin, hx, hy] at h2
    have h3 : (a₀ : E) • (k • u) = ((n : ℚ) * (k : ℚ)) • (a • u) := by
      ext i
      simp [ha₀, Rat.smul_def]
      ring
    have h4 : (a₀' : E) • (l • v) = ((n : ℚ) * (l : ℚ)) • (IsCMField.complexConj E a • v) := by
      ext i
      simp [ha₀', ha₀, Rat.smul_def]
      ring
    have h5 : k • u = (k : ℚ) • u := (Nat.cast_smul_eq_nsmul ℚ k u).symm
    have h6 : l • v = (l : ℚ) • v := (Nat.cast_smul_eq_nsmul ℚ l v).symm
    rw [h3, h4, h5, h6] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hn' hk') hl') (by linear_combination h2)
  · intro u v
    exact (LinearMap.IsAlt.neg (B := B) halt v u).symm
  · intro u hu
    obtain ⟨k, y, hk, hy⟩ := hs u
    have hf : ∀ x, form x y = 0 := by
      intro x
      have h : B (e x) (e y) = 0 := by rw [hy, map_nsmul, hu (e x), smul_zero]
      rw [hB] at h
      exact_mod_cast h
    have h0 : form y = 0 := LinearMap.ext fun x => by
      rw [hskew, hf]; simp
    have y0 : y = 0 := hbij.1 (by rw [h0, map_zero])
    rw [y0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hy
    exact (smul_eq_zero.mp hy.symm).resolve_left (Nat.cast_ne_zero.mpr hk)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil
