import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Break down `W.mem_or_inv_mem x with hx | hx` into its components or cases. Conclude with `hx`. Rewrite using `[h]`. Conclude with `mul_mem ha (pow_mem hx n)`.
-/
theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

/- English proof (translation)
Establish `hr : H.rt0 ∈ c.F` using `c.le (IntermediateField.subset_adjoin _ _ (by simp))`. Establish `hz : zeta l.A ∈ c.F` using `c.le (IntermediateField.subset_adjoin _ _ (by simp))`. Establish `hd : (H.d : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr H.d_prime.ne_zero`. Establish `hr0 : H.rt0 ≠ 0` using `fun h => by`. Use `H.sqrt_neg_disc_sq` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `hd (by simpa using this)`. Establish `hrW : H.rt0 ∈ W` using `mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by`. Rewrite using `[← H.sqrt_neg_disc_sq]`. Use the proof step `field_simp)`.

Establish `hp : IsPrimitiveRoot (zeta l.A) l.A` using `Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'`. Establish `hz0 : zeta l.A ≠ 0` using `hp.ne_zero l.A_pos.ne'`. Establish `hzW : zeta l.A ∈ W` using `mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by`. Establish `h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1`. Rewrite using `[← pow_succ', Nat.sub_add_cancel l.A_pos]`.

Conclude with `hp.pow_eq_one`. Rewrite using `[one_mul, inv_pow]`. Conclude with `eq_inv_of_mul_eq_one_left h1)`. Conclude with `⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩`.
-/
theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩

/- English proof (translation)
Introduce `h`. Establish `h1 : ((p : c.F))⁻¹ ∈ c.V W` using `by rw [h]; trivial`. Establish `h2 : ((p : ℂ))⁻¹ ∈ W` using `by simpa [ValuationSubring.mem_comap] using h1`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Rewrite `hW` using `[ValuationSubring.mem_nonunits_iff]`.

Establish `h3` using `(W.valuation_le_one_iff _).mpr h2`. Rewrite `h3` using `[map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hp0))]`. Conclude with `absurd hW (not_lt.mpr h3)`.
-/
theorem localRing_ne_top (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : c.V W ≠ ⊤ := by
  intro h
  have h1 : ((p : c.F))⁻¹ ∈ c.V W := by rw [h]; trivial
  have h2 : ((p : ℂ))⁻¹ ∈ W := by simpa [ValuationSubring.mem_comap] using h1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [ValuationSubring.mem_nonunits_iff] at hW
  have h3 := (W.valuation_le_one_iff _).mpr h2
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hp0))] at h3
  exact absurd hW (not_lt.mpr h3)

end GlobalTheory.JointModelGuards
