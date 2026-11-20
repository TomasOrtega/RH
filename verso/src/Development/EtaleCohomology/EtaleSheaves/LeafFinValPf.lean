import Development.EtaleCohomology.EtaleSheaves.LeafOrdInfLocalPf
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Norm.Defs

namespace LateralTheory.E.E4

open Polynomial IsDedekindDomain

/- English proof (translation)
Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin (HeightOneSpectrum D)`. Use `⟨n, MonoidHom.mk' (fun x => Multiplicative.ofAdd (fun i => WithZero.log ((e.symm i).valuation L (x : L)))) ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[← ofAdd_add]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Units.val_mul, map_mul, Pi.add_apply]`. Conclude with `WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero) ((Valuation.ne_zero_iff _).mpr y.ne_zero)`. Introduce `x hx`. Apply `HeightOneSpectrum.mem_integers_of_valuation_le_one` to reduce the goal to its premises.

Introduce `v`. Establish `h : WithZero.log ((e.symm (e v)).valuation L (x : L)) = 0` using `congrFun (congrArg Multiplicative.toAdd hx) (e v)`. Rewrite `h` using `[e.symm_apply_apply]`. Conclude with `WithZero.le_exp_of_log_le h.le`.
-/
theorem finVal_dedekind (D L : Type) [CommRing D] [IsDedekindDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] [Finite (HeightOneSpectrum D)] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
      (x : L) ∈ (algebraMap D L).range := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (HeightOneSpectrum D)
  refine ⟨n, MonoidHom.mk' (fun x => Multiplicative.ofAdd
    (fun i => WithZero.log ((e.symm i).valuation L (x : L)))) ?_, ?_⟩
  · intro x y
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Units.val_mul, map_mul, Pi.add_apply]
    exact WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  · intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h : WithZero.log ((e.symm (e v)).valuation L (x : L)) = 0 :=
      congrFun (congrArg Multiplicative.toAdd hx) (e v)
    rw [e.symm_apply_apply] at h
    exact WithZero.le_exp_of_log_le h.le

/- English proof (translation)
Establish `hf` using `IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) D`. Use `hf.to_subtype` as an intermediate fact. Use `Finite.of_injective (β := (IsLocalRing.maximalIdeal A).primesOver D) (fun v => ⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩) ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Conclude with `(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) v.asIdeal)).symm`.

Introduce `v w h`. Conclude with `HeightOneSpectrum.ext (congrArg Subtype.val h)`.
-/
theorem finVal_finite (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsDedekindDomain D]
    [Algebra A D] [Algebra.IsIntegral A D] [IsDomain A] [Module.IsTorsionFree A D] :
    Finite (HeightOneSpectrum D) := by
  have hf := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) D
  have := hf.to_subtype
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal A).primesOver D)
    (fun v => ⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩) ?_
  · have := v.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) v.asIdeal)).symm
  · intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)

/- English proof (translation)
Use `integralClosure.isDedekindDomain A K L` as an intermediate fact. Use `integralClosure.isFractionRing_of_finite_extension (A := A) K L` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap A L)`. Rewrite using `[IsScalarTower.algebraMap_eq A K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective A K)`.

Establish `: FaithfulSMul A (integralClosure A L)`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b h`. Conclude with `hinj (congrArg Subtype.val h)`. Use `finVal_finite A (integralClosure A L)` as an intermediate fact.

Take `⟨n, φ, h⟩` from `finVal_dedekind (integralClosure A L) L`. Use `⟨n, φ, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h x hx`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem finVal_sep (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  have := integralClosure.isDedekindDomain A K L
  have := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A (integralClosure A L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have := finVal_finite A (integralClosure A L)
  obtain ⟨n, φ, h⟩ := finVal_dedekind (integralClosure A L) L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  rw [← hy]
  exact y.2

/- English proof (translation)
Take `⟨n, φ, h⟩` from `finVal_sep A K (separableClosure K L)`. Use `⟨n, φ.comp (Units.map (Algebra.norm (separableClosure K L))), fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : IsIntegral A (Algebra.norm (separableClosure K L) (x : L))` using `h _ hx`. Take `⟨m, y, hy⟩` from `IsPurelyInseparable.pow_mem (separableClosure K L) (ringExpChar (separableClosure K L)) (x : L)`. Establish `hq : 0 < ringExpChar (separableClosure K L) ^ m` using `expChar_pow_pos (separableClosure K L) _ m`.

Establish `h2 : IsIntegral A (y ^ Module.finrank (separableClosure K L) L)`. Rewrite using `[← Algebra.norm_algebraMap, hy, map_pow]`. Conclude with `h1.pow _`. Establish `h3 : IsIntegral A y` using `h2.of_pow Module.finrank_pos`. Establish `: IsScalarTower A (separableClosure K L) L` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Establish `h4 : IsIntegral A (algebraMap (separableClosure K L) L y)` using `h3.algebraMap`. Rewrite `h4` using `[hy]`. Conclude with `h4.of_pow hq`.
-/
theorem finVal_gen (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  obtain ⟨n, φ, h⟩ := finVal_sep A K (separableClosure K L)
  refine ⟨n, φ.comp (Units.map (Algebra.norm (separableClosure K L))), fun x hx => ?_⟩
  have h1 : IsIntegral A (Algebra.norm (separableClosure K L) (x : L)) := h _ hx
  obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K L)
    (ringExpChar (separableClosure K L)) (x : L)
  have hq : 0 < ringExpChar (separableClosure K L) ^ m := expChar_pow_pos (separableClosure K L) _ m
  have h2 : IsIntegral A (y ^ Module.finrank (separableClosure K L) L) := by
    rw [← Algebra.norm_algebraMap, hy, map_pow]
    exact h1.pow _
  have h3 : IsIntegral A y := h2.of_pow Module.finrank_pos
  have : IsScalarTower A (separableClosure K L) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h4 : IsIntegral A (algebraMap (separableClosure K L) L y) := h3.algebraMap
  rw [hy] at h4
  exact h4.of_pow hq

/- English proof (translation)
Introduce `k L _ _ _ _ s hs hfd`. Establish `hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0` using `fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)`. Set `P : Ideal k[X]` to `RingHom.ker (evalRingHom (0 : k))`. Establish `hP : P.IsPrime` using `RingHom.ker_isPrime _`. Set `A` to `Localization.AtPrime P`.

Set `K` to `IntermediateField.adjoin k {s}`. Set `t : K` to `⟨s, IntermediateField.mem_adjoin_simple_self k s⟩`. Establish `hval : ∀ p : k[X], ((aeval t p : K) : L) = aeval s p` using `fun p => (aeval_algHom_apply K.val t p).symm`. Establish `hne' : ∀ p : k[X], p ≠ 0 → aeval t p ≠ 0` using `fun p hp h0 => hne p hp (by rw [← hval, h0]; rfl)`. Establish `hu : ∀ y : P.primeCompl, IsUnit ((aeval t : k[X] →ₐ[k] K).toRingHom y)`.

Introduce `y`. Use `(hne' y ?_).isUnit` and prove the remaining obligations. Introduce `h0`. Conclude with `y.2 (by rw [h0]; exact P.zero_mem)`. Set `f : A →+* K` to `IsLocalization.lift (M := P.primeCompl) hu`.

Establish `hf : ∀ p : k[X], f (algebraMap k[X] A p) = aeval t p` using `fun p => IsLocalization.lift_eq hu p`. Establish `hfrac : ∀ c : A, ∃ a b : k[X], b.eval 0 ≠ 0 ∧ f c = aeval t a / aeval t b`. Introduce `c`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj P.primeCompl c`. Use `⟨a, b, b.2, ?_⟩` and prove the remaining obligations.

Use `congrArg f hab` as an intermediate fact. Rewrite `this` using `[map_mul, hf, hf]`. Conclude with `(eq_div_iff (hu b).ne_zero).mpr this`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `c hc`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj P.primeCompl c`. Establish `h1` using `congrArg f hab`. Rewrite `h1` using `[map_mul, hc, zero_mul, hf]`. Establish `ha : a = 0`.

Assume the negation of the conclusion as `ha`. Conclude with `hne' a ha h1.symm`. Simplify using `only [ha, map_zero] at hab`. Conclude with `(IsLocalization.map_units A b).mul_left_eq_zero.mp hab`. Set `_ : Algebra A K` to `f.toAlgebra`.

Set `_ : Algebra A L` to `((algebraMap K L).comp f).toAlgebra`. Establish `: IsScalarTower A K L` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `: FaithfulSMul A K` using `(faithfulSMul_iff_algebraMap_injective A K).mpr hinj`. Establish `: IsFractionRing A K`. Use `IsFractionRing.of_field A K (fun z => ?_)` and prove the remaining obligations.

Take `⟨r, q, hz⟩` from `(IntermediateField.mem_adjoin_simple_iff k (z : L)).mp z.2`. Use `⟨algebraMap k[X] A r, algebraMap k[X] A q, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = f _ / f _`. Rewrite using `[hf, hf]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hz, ← hval, ← hval]`. Both sides reduce to the same expression. Take `⟨n, φ, h⟩` from `finVal_gen A K L`. Use `⟨n, φ, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, hpx⟩` from `h x hx`.

Use `choose a b hb hab using hfrac`. Use `⟨p.natDegree, fun i => a (p.coeff i), fun i => b (p.coeff i), fun i => hb _, ?_⟩` and prove the remaining obligations. Rewrite `hpx` using `[hp.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum]`. Rewrite using `[← hpx]`. Use `congr 1`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[eval₂_mul, eval₂_C, eval₂_X_pow]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = ((f (p.coeff i) : K) : L)`. Rewrite using `[hab, ← hval, ← hval]`.

Both sides reduce to the same expression.
-/
theorem LeafFinVal_of : LeafFinVal := by
  intro k L _ _ _ _ s hs hfd
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  let P : Ideal k[X] := RingHom.ker (evalRingHom (0 : k))
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let A := Localization.AtPrime P
  let K := IntermediateField.adjoin k {s}
  let t : K := ⟨s, IntermediateField.mem_adjoin_simple_self k s⟩
  have hval : ∀ p : k[X], ((aeval t p : K) : L) = aeval s p := fun p =>
    (aeval_algHom_apply K.val t p).symm
  have hne' : ∀ p : k[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h0 => hne p hp (by rw [← hval, h0]; rfl)
  have hu : ∀ y : P.primeCompl, IsUnit ((aeval t : k[X] →ₐ[k] K).toRingHom y) := by
    intro y
    refine (hne' y ?_).isUnit
    intro h0
    exact y.2 (by rw [h0]; exact P.zero_mem)
  let f : A →+* K := IsLocalization.lift (M := P.primeCompl) hu
  have hf : ∀ p : k[X], f (algebraMap k[X] A p) = aeval t p := fun p => IsLocalization.lift_eq hu p
  have hfrac : ∀ c : A, ∃ a b : k[X], b.eval 0 ≠ 0 ∧ f c = aeval t a / aeval t b := by
    intro c
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨a, b, b.2, ?_⟩
    have := congrArg f hab
    rw [map_mul, hf, hf] at this
    exact (eq_div_iff (hu b).ne_zero).mpr this
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    have h1 := congrArg f hab
    rw [map_mul, hc, zero_mul, hf] at h1
    have ha : a = 0 := by
      by_contra ha
      exact hne' a ha h1.symm
    simp only [ha, map_zero] at hab
    exact (IsLocalization.map_units A b).mul_left_eq_zero.mp hab
  let _ : Algebra A K := f.toAlgebra
  let _ : Algebra A L := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hinj
  have : IsFractionRing A K := by
    refine IsFractionRing.of_field A K (fun z => ?_)
    obtain ⟨r, q, hz⟩ := (IntermediateField.mem_adjoin_simple_iff k (z : L)).mp z.2
    refine ⟨algebraMap k[X] A r, algebraMap k[X] A q, ?_⟩
    change z = f _ / f _
    rw [hf, hf]
    apply Subtype.ext
    rw [hz, ← hval, ← hval]
    rfl
  obtain ⟨n, φ, h⟩ := finVal_gen A K L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := h x hx
  choose a b hb hab using hfrac
  refine ⟨p.natDegree, fun i => a (p.coeff i), fun i => b (p.coeff i), fun i => hb _, ?_⟩
  rw [hp.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at hpx
  rw [← hpx]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  change _ = ((f (p.coeff i) : K) : L)
  rw [hab, ← hval, ← hval]
  rfl

end LateralTheory.E.E4
