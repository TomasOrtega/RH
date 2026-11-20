import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx`.
-/
private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

/- English proof (translation)
Introduce `l _ O _ _ a ha`. Establish `hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1` using `fun x => norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)`. Establish `hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1`. Introduce `u`. Establish `h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1`.

Rewrite using `[← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules. Establish `h2` using `hle u`. Establish `h3` using `hle (u⁻¹ : Oˣ)`. Establish `h4` using `norm_nonneg ((u : O) : PadicAlgCl l)`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `key : ∀ x : O, x ≠ 0 → ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat`. Introduce `x hx`. Take `⟨n, u, h⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`.

Rewrite using `[IsDiscreteValuationRing.addVal_def x u hϖ n h, h]`. Simplify using `[hu]`. Establish `hl0 : (l : O) ≠ 0`. Introduce `h`. Establish `h' : ((l : O) : PadicAlgCl l) = 0` using `by rw [h]; rfl`.

Establish `: (l : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹`. Establish `: ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`.

Establish `he : eO l O = IsDiscreteValuationRing.addVal O (l : O)` using `Ring.ord_eq_addVal (l : O)`. Rewrite using `[he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem UpperTheory.V.Base.normO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 →
      ‖(a : PadicAlgCl l)‖ ^ (eO l O).toNat = ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  intro l _ O _ _ a ha
  have hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)
  have hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg ((u : O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : ((l : O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : eO l O = IsDiscreteValuationRing.addVal O (l : O) := Ring.ord_eq_addVal (l : O)
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]
