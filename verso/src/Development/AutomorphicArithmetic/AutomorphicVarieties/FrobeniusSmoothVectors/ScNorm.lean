import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx`.
-/
private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

/- English proof (translation)
Introduce `l _ c x`. Establish `hle : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1` using `fun x => norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)`. Establish `hu : ∀ u : c.Oˣ, ‖((u : c.O) : PadicAlgCl l)‖ = 1`. Introduce `u`. Establish `h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1`.

Rewrite using `[← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules. Establish `h2` using `hle u`. Establish `h3` using `hle (u⁻¹ : c.Oˣ)`. Establish `h4` using `norm_nonneg ((u : c.O) : PadicAlgCl l)`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `hl0 : (l : c.O) ≠ 0`. Introduce `h`. Establish `h' : ((l : c.O) : PadicAlgCl l) = 0` using `by rw [h]; rfl`.

Establish `: (l : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹`. Establish `: ((l : c.O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`.

Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hϖ1 : ‖(ϖ : PadicAlgCl l)‖ < 1`. Use `lt_of_le_of_ne (hle ϖ) fun h1 => ?_` and prove the remaining obligations. Take `⟨n, u, h⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Rewrite `hl` using `[h]`.

Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, h1, one_pow, mul_one] at hl`. Conclude with `absurd hl.symm (inv_lt_one_of_one_lt₀ hl1).ne`. Use `⟨hle x, fun hx => ?_, fun hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨y, rfl⟩` from `hx`.

Rewrite using `[Subalgebra.coe_mul, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hϖ1 (hle y)`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, rfl⟩`. Conclude with `absurd (hu u) hx.ne`.
-/
theorem UpperTheory.V.Fr.sc_norm :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : c.O), ‖(x : PadicAlgCl l)‖ ≤ 1 ∧ (x ∈ maximalIdeal c.O ↔ ‖(x : PadicAlgCl l)‖ < 1) := by
  intro l _ c x
  have hle : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hu : ∀ u : c.Oˣ, ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : c.Oˣ)
    have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have h' : ((l : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : c.O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => ?_
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h] at hl
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, h1, one_pow, mul_one] at hl
    exact absurd hl.symm (inv_lt_one_of_one_lt₀ hl1).ne
  refine ⟨hle x, fun hx => ?_, fun hx => ?_⟩
  · rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hϖ1 (hle y)
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    exact absurd (hu u) hx.ne
