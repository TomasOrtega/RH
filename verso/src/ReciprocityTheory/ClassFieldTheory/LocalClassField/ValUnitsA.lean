import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Conclude with `(Fact.out : p.Prime).one_lt` after adjusting the coercions.
-/
theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

variable {p K} in
/- English proof (translation)
Introduce `h` and use `x.ne_zero (Subtype.ext h)`.
-/
theorem coe_units_ne_zero (x : Kˣ) : ((x : K) : PadicAlgCl p) ≠ 0 := fun h => x.ne_zero (Subtype.ext h)

variable {p K} in
/- English proof (translation)
The claim follows from `norm_pos_iff.2 (coe_units_ne_zero x)`.
-/
theorem norm_units_pos (x : Kˣ) : 0 < ‖((x : K) : PadicAlgCl p)‖ := norm_pos_iff.2 (coe_units_ne_zero x)

/- English proof (translation)
Unfold `vK`. Rewrite using `[vOn_spec, vbar_apply]`. Use `show (eK p K : ℝ) * - Real.logb p ‖((x : K) : PadicAlgCl p)‖ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_spec (x : Kˣ) : (vK p K x : ℝ) = - (eK p K * Real.logb p ‖((x : K) : PadicAlgCl p)‖) := by
  unfold vK
  rw [vOn_spec, vbar_apply]
  show (eK p K : ℝ) * - Real.logb p ‖((x : K) : PadicAlgCl p)‖ = _
  ring

/- English proof (translation)
Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[vK_spec]`. Simplify using the standard rewrite rules.
-/
theorem vK_one : vK p K 1 = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec]; simp

/- English proof (translation)
Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[Int.cast_add, vK_spec, vK_spec, vK_spec, Units.val_mul, MulMemClass.coe_mul, norm_mul, Real.logb_mul (norm_units_pos x).ne' (norm_units_pos y).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_mul (x y : Kˣ) : vK p K (x * y) = vK p K x + vK p K y := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, vK_spec, vK_spec, vK_spec, Units.val_mul, MulMemClass.coe_mul, norm_mul,
    Real.logb_mul (norm_units_pos x).ne' (norm_units_pos y).ne']
  ring

def vKHom : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (vK p K x)
  map_one' := by rw [vK_one]; rfl
  map_mul' x y := by rw [vK_mul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vKHom_apply (x : Kˣ) : vKHom p K x = Multiplicative.ofAdd (vK p K x) := rfl

/- English proof (translation)
Establish `h` using `vK_mul p K x⁻¹ x`. Rewrite `h` using `[inv_mul_cancel, vK_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vK_inv (x : Kˣ) : vK p K x⁻¹ = - vK p K x := by
  have h := vK_mul p K x⁻¹ x
  rw [inv_mul_cancel, vK_one] at h
  omega

/- English proof (translation)
Establish `h` using `map_zpow (vKHom p K) x n`. Rewrite `h` using `[vKHom_apply, vKHom_apply, ← ofAdd_zsmul]`. Simplify using `using Multiplicative.ofAdd.injective h`.
-/
theorem vK_zpow (x : Kˣ) (n : ℤ) : vK p K (x ^ n) = n * vK p K x := by
  have h := map_zpow (vKHom p K) x n
  rw [vKHom_apply, vKHom_apply, ← ofAdd_zsmul] at h
  simpa using Multiplicative.ofAdd.injective h

/- English proof (translation)
Establish `h` using `vK_zpow p K x n`. Rewrite `h` using `[zpow_natCast]`. Then use the resulting hypothesis.
-/
theorem vK_pow (x : Kˣ) (n : ℕ) : vK p K (x ^ n) = n * vK p K x := by
  have h := vK_zpow p K x n
  rwa [zpow_natCast] at h

variable {p} in
/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq E.val E.val.injective]`. Both sides reduce to the same expression.
-/
theorem norm_algHom {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : E →ₐ[ℚ_[p]] PadicAlgCl p) (x : E) :
    ‖σ x‖ = ‖(x : PadicAlgCl p)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq E.val E.val.injective]
  rfl

variable {K L}

/- English proof (translation)
The claim follows from `FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective`.
-/
theorem finDim_of_le (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : FiniteDimensional ℚ_[p] K :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h)` using `hL`. Conclude with `FiniteDimensional.right ℚ_[p] K _`.
-/
theorem finDim_extendScalars_of_le (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    FiniteDimensional K (IntermediateField.extendScalars h) := by
  have : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h) := hL
  exact FiniteDimensional.right ℚ_[p] K _

/- English proof (translation)
Use `finDim_extendScalars_of_le p hL h` as an intermediate fact. Establish `h1` using `Algebra.norm_eq_prod_embeddings K (PadicAlgCl p) x`. Establish `h2 : ((Algebra.norm K x : K) : PadicAlgCl p) = algebraMap K (PadicAlgCl p) (Algebra.norm K x)` using `rfl`. Rewrite using `[h2, h1, norm_prod, Finset.prod_congr rfl (fun σ _ => ?_), Finset.prod_const, Finset.card_univ, AlgHom.card]`. Conclude with `norm_algHom (E := L) (σ.restrictScalars ℚ_[p]) ⟨x.1, x.2⟩`.
-/
theorem norm_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : IntermediateField.extendScalars h) :
    ‖((Algebra.norm K x : K) : PadicAlgCl p)‖ =
      ‖(x : PadicAlgCl p)‖ ^ Module.finrank K (IntermediateField.extendScalars h) := by
  have := finDim_extendScalars_of_le p hL h
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p) x
  have h2 : ((Algebra.norm K x : K) : PadicAlgCl p) = algebraMap K (PadicAlgCl p) (Algebra.norm K x) := rfl
  rw [h2, h1, norm_prod, Finset.prod_congr rfl (fun σ _ => ?_), Finset.prod_const, Finset.card_univ,
    AlgHom.card]
  exact norm_algHom (E := L) (σ.restrictScalars ℚ_[p]) ⟨x.1, x.2⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
