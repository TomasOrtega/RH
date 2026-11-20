import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

/- English proof (translation)
Introduce `l _ c n x`. Establish `hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹`. Establish `: ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`. Take `⟨-, -, -, -, -, he0, -, he, -⟩` from `UpperTheory.V.Base.dvrFacts l c.O`.

Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h`. Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h]; rfl`.

Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `key` using `UpperTheory.V.Base.normO l c.O x hx`. Use `set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def`. Establish `hEtop : UpperTheory.V.Base.eO l c.O ≠ ⊤`.

Rewrite using `[he]`. Conclude with `fun h => hl0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)`. Establish `hEcast : UpperTheory.V.Base.eO l c.O = (e : ℕ∞)` using `(ENat.coe_toNat hEtop).symm`. Establish `hepos : e ≠ 0`. Introduce `h0`.

Apply `he0` to reduce the goal to its premises. Rewrite using `[hEcast, h0]`. Both sides reduce to the same expression. Establish `hxtop : IsDiscreteValuationRing.addVal c.O x ≠ ⊤` using `fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)`. Use `set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def`.

Establish `hvcast : IsDiscreteValuationRing.addVal c.O x = (v : ℕ∞)` using `(ENat.coe_toNat hxtop).symm`. Establish `hlpos : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)`. Establish `hllt : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : l.Prime).one_lt)`. Rewrite using `[norm_pow, hlnorm, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, ← he, hEcast, hvcast, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hepos, key, ← pow_mul, pow_le_pow_iff_right_of_lt_one₀ hlpos hllt]`. Rewrite using `[nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]`.
-/
theorem GlobalTheory.Coef.norm_le_norm_pow_iff_dvd :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O),
      ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  intro l _ c n x
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  obtain ⟨-, -, -, -, -, he0, -, he, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have key := UpperTheory.V.Base.normO l c.O x hx
  set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
  have hEtop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [he]; exact fun h => hl0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hEcast : UpperTheory.V.Base.eO l c.O = (e : ℕ∞) := (ENat.coe_toNat hEtop).symm
  have hepos : e ≠ 0 := by
    intro h0; apply he0; rw [hEcast, h0]; rfl
  have hxtop : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ :=
    fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
  have hvcast : IsDiscreteValuationRing.addVal c.O x = (v : ℕ∞) := (ENat.coe_toNat hxtop).symm
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hllt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : l.Prime).one_lt)
  rw [norm_pow, hlnorm, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    ← he, hEcast, hvcast, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hepos, key, ← pow_mul,
    pow_le_pow_iff_right_of_lt_one₀ hlpos hllt]
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]
