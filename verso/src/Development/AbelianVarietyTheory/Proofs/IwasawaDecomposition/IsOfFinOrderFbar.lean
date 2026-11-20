import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

@[reducible] def algK (D : D7) (jE : D.host.E →+* Qb) {M : Fld} (h : KQbar D jE ≤ M) : Algebra D.host.K M :=
  ((IntermediateField.inclusion h).toRingHom.comp (D.host.K.equivMap jE.toRatAlgHom).toRingHom).toAlgebra

/- English proof (translation)
The claim follows from `h`.
-/
theorem nfOf {M : Fld} (h : FiniteDimensional ℚ M) : NumberField M where
  to_finiteDimensional := h

/- English proof (translation)
Establish `hint : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Use `IntermediateField.adjoin.finiteDimensional hint` as an intermediate fact. Establish `: Finite (IntermediateField.adjoin (ZMod g) {x})` using `Module.finite_of_finite (ZMod g)`. Set `y : IntermediateField.adjoin (ZMod g) {x}` to `⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩`. Establish `hy : y ≠ 0` using `fun h => hx (congrArg Subtype.val h)`.

Establish `h1 : IsOfFinOrder (Units.mk0 y hy)` using `isOfFinOrder_of_finite _`. Conclude with `((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1`.
-/
theorem isOfFinOrder_fbar {g : ℕ} [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

section Iota

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Establish `h : t 0 * t 0 = t 0` using `by rw [← map_mul, mul_zero]`. Break down `eq_or_ne (t 0) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Conclude with `zero_mem _`.

Rewrite using `[(mul_eq_left₀ h0).1 h]`. Conclude with `one_mem _`. Conclude with `mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos (by rw [← map_pow, pow_orderOf_eq_one, map_one])`.
-/
theorem mem_of_monoidHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (t : Formalism.CyclotomicNorms.Fbar g →* Ω) (x : Formalism.CyclotomicNorms.Fbar g) : t x ∈ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
    rcases eq_or_ne (t 0) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
  · exact mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])

def redHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω) :
    Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l where
  toFun x := redThrough B κ (t x)
  map_one' := by rw [map_one]; exact redThrough_one B κ
  map_mul' x y := by
    rw [map_mul]; exact redThrough_mul B κ (mem_of_monoidHom B t x) (mem_of_monoidHom B t y)

end Iota

/- English proof (translation)
Set `ρ : B →+* Formalism.CyclotomicNorms.Fbar l` to `κ.toRingHom.comp (IsLocalRing.residue B)`. Establish `hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩` using `fun z hz => by`. Unfold `redThrough`. Rewrite using `[dif_pos hz]`. Both sides reduce to the same expression.

Establish `hz : x * y⁻¹ ≠ 0` using `mul_ne_zero hx (inv_ne_zero hy)`. Use `set n := orderOf (x * y⁻¹) with hn`. Establish `hnpos : 0 < n` using `(isOfFinOrder_fbar hz).orderOf_pos`. Establish `hcop : n.Coprime l`. Use `Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)` and prove the remaining obligations.

Use `orderOf_dvd_of_pow_eq_one ?_` and prove the remaining obligations. Rewrite using `[mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]`. Simplify using the standard rewrite rules. Establish `hmem` using `mem_of_monoidHom B t (x * y⁻¹)`. Establish `hprim : IsPrimitiveRoot (t (x * y⁻¹)) n`.

Use `⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩` and prove the remaining obligations. Use `ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_one]`. Conclude with `hm`. Establish `hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n` using `IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim`.

Establish `hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1`. Establish `hxy : x = x * y⁻¹ * y` using `by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]`. Establish `hy0 : redHom B κ t y ≠ 0`. Introduce `h0`. Establish `hyo` using `(isOfFinOrder_fbar hy).orderOf_pos`.

Establish `: redHom B κ t y ^ orderOf y = 1` using `by rw [← map_pow, pow_orderOf_eq_one, map_one]`. Rewrite `this` using `[h0, zero_pow hyo.ne']`. Conclude with `zero_ne_one this`. Establish `h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y`. Rewrite using `[← map_mul, ← hxy, one_mul, h]`.

Establish `h3` using `mul_right_cancel₀ hy0 h2`. Rewrite using `[← hρ]`. Conclude with `h3`. Establish `: NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l)` using `⟨fun h0 => (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩`. Establish `h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n`.

Rewrite using `[← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom]`. Rewrite using `[(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]`. Establish `hn1 : n = 1` using `IsPrimitiveRoot.one_left_iff.1 h3`. Rewrite `hn1` using `[hn, orderOf_eq_one_iff]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem redHom_inj {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [hl : Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (x y : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) (hy : y ≠ 0)
    (cx : (orderOf x).Coprime l) (cy : (orderOf y).Coprime l) (h : redHom B κ t x = redHom B κ t y) : x = y := by
  let ρ : B →+* Formalism.CyclotomicNorms.Fbar l := κ.toRingHom.comp (IsLocalRing.residue B)
  have hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩ := fun z hz => by
    unfold redThrough; rw [dif_pos hz]; rfl
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hmem := mem_of_monoidHom B t (x * y⁻¹)
  have hprim : IsPrimitiveRoot (t (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact hm
  have hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim
  have hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1 := by
    have hxy : x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hy0 : redHom B κ t y ≠ 0 := by
      intro h0
      have hyo := (isOfFinOrder_fbar hy).orderOf_pos
      have : redHom B κ t y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h0, zero_pow hyo.ne'] at this
      exact zero_ne_one this
    have h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y := by
      rw [← map_mul, ← hxy, one_mul, h]
    have h3 := mul_right_cancel₀ hy0 h2
    rw [← hρ]
    exact h3
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]
  have hn1 : n = 1 := IsPrimitiveRoot.one_left_iff.1 h3
  rw [hn, orderOf_eq_one_iff] at hn1
  calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    _ = y := by rw [hn1, one_mul]

end GlobalTheory.ParRay

end
