import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral
open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx`.
-/
private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

/- English proof (translation)
Establish `hle : ∀ x : O, ‖algebraMap O (PadicAlgCl l) x‖ ≤ 1` using `fun x => norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).algebraMap)`. Establish `hu : ∀ u : Oˣ, ‖algebraMap O (PadicAlgCl l) (u : O)‖ = 1`. Introduce `u`. Establish `h1 : ‖algebraMap O (PadicAlgCl l) (u : O)‖ * ‖algebraMap O (PadicAlgCl l) ((u⁻¹ : Oˣ) : O)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, Units.mul_inv]`.

Simplify using the standard rewrite rules. Establish `h2` using `hle u`. Establish `h3` using `hle (u⁻¹ : Oˣ)`. Establish `h4` using `norm_nonneg (algebraMap O (PadicAlgCl l) (u : O))`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `key : ∀ x : O, x ≠ 0 → ‖algebraMap O (PadicAlgCl l) x‖ = ‖algebraMap O (PadicAlgCl l) ϖ‖ ^ (IsDiscreteValuationRing.addVal O x).toNat`. Introduce `x hx`. Take `⟨n, u, h⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Rewrite using `[IsDiscreteValuationRing.addVal_def x u hϖ n h, h]`.

Simplify using `[hu]`. Establish `hl0 : (l : O) ≠ 0`. Introduce `h`. Establish `h' : algebraMap O (PadicAlgCl l) (l : O) = 0` using `by rw [h, map_zero]`. Rewrite `h'` using `[map_natCast]`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'`. Establish `hl : ‖algebraMap O (PadicAlgCl l) (l : O)‖ = (l : ℝ)⁻¹`. Establish `: algebraMap O (PadicAlgCl l) (l : O) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`. Establish `he : UpperTheory.V.Base.eO l O = IsDiscreteValuationRing.addVal O (l : O)` using `(UpperTheory.V.Base.dvrFacts l O).2.2.2.2.2.2.2.1`.

Rewrite using `[he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem norm_abs (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)]
    (a : O) (ha : a ≠ 0) :
    ‖algebraMap O (PadicAlgCl l) a‖ ^ (UpperTheory.V.Base.eO l O).toNat =
      ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  have hle : ∀ x : O, ‖algebraMap O (PadicAlgCl l) x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).algebraMap)
  have hu : ∀ u : Oˣ, ‖algebraMap O (PadicAlgCl l) (u : O)‖ = 1 := by
    intro u
    have h1 : ‖algebraMap O (PadicAlgCl l) (u : O)‖ * ‖algebraMap O (PadicAlgCl l) ((u⁻¹ : Oˣ) : O)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg (algebraMap O (PadicAlgCl l) (u : O))
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖algebraMap O (PadicAlgCl l) x‖ =
      ‖algebraMap O (PadicAlgCl l) ϖ‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap O (PadicAlgCl l) (l : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  have hl : ‖algebraMap O (PadicAlgCl l) (l : O)‖ = (l : ℝ)⁻¹ := by
    have : algebraMap O (PadicAlgCl l) (l : O) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : UpperTheory.V.Base.eO l O = IsDiscreteValuationRing.addVal O (l : O) :=
    (UpperTheory.V.Base.dvrFacts l O).2.2.2.2.2.2.2.1
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hv : ∀ x, UpperTheory.V.UnitaryThreeInertia.vl1 l x = -Real.logb l ‖x‖` using `fun x => by`. Rewrite using `[UpperTheory.V.UnitaryThreeInertia.vl1, Real.logb, neg_div]`. Simplify using `only [hv]`.

Use `⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `IsUltrametricDist.norm_add_le_max x y`. Establish `hp` using `norm_pos_iff.2 hxy`.

Break down `le_max_iff.1 h with h | h` into its components or cases. Use `min_le_of_left_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))` and prove the remaining obligations. Conclude with `Real.logb_le_logb_of_le hl hp h`. Use `min_le_of_right_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))` and prove the remaining obligations. Conclude with `Real.logb_le_logb_of_le hl hp h`.

Establish `h` using `congrArg (Real.logb l) (norm_abs l O a ha)`. Rewrite `h` using `[Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.norm_bound_of_integral_values :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)],
        IsNVal O (PadicAlgCl l) (fun x => ((UpperTheory.V.Base.eO l O).toNat : ℝ) * UpperTheory.V.UnitaryThreeInertia.vl1 l x) := by
  intro l _ O _ _ _ _ _ _ _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hv : ∀ x, UpperTheory.V.UnitaryThreeInertia.vl1 l x = -Real.logb l ‖x‖ := fun x => by
    rw [UpperTheory.V.UnitaryThreeInertia.vl1, Real.logb, neg_div]
  simp only [hv]
  refine ⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩
  · rw [norm_mul, Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]
    ring
  · have h := IsUltrametricDist.norm_add_le_max x y
    have hp := norm_pos_iff.2 hxy
    rcases le_max_iff.1 h with h | h
    · refine min_le_of_left_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
    · refine min_le_of_right_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
  · have h := congrArg (Real.logb l) (norm_abs l O a ha)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl] at h
    linarith
