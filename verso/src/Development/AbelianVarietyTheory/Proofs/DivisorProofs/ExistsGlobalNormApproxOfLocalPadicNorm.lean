import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensorStatement
open scoped TensorProduct Classical

namespace GlobalTheory.LocalApprox

/- English proof (translation)
Establish `hinj : Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E)` using `Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective`. Establish `h1 : Function.Injective (LinearMap.mulLeft ℚ b)`. Introduce `x y hxy`. Apply `hinj` to reduce the goal to its premises. Establish `h` using `congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy`.

Simplify using `only [LinearMap.mulLeft_apply, map_mul] at h`. Conclude with `hb.mul_left_cancel h`. Take `⟨w, hw⟩` from `LinearMap.injective_iff_surjective.1 h1 1`. Establish `hw' : b * w = 1` using `hw`. Conclude with `⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩`.
-/
theorem isUnit_of_isUnit_one_tmul (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (b : E) (hb : IsUnit ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b)) : IsUnit b := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective
  have h1 : Function.Injective (LinearMap.mulLeft ℚ b) := by
    intro x y hxy
    apply hinj
    have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy
    simp only [LinearMap.mulLeft_apply, map_mul] at h
    exact hb.mul_left_cancel h
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 h1 1
  have hw' : b * w = 1 := hw
  exact ⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩

/- English proof (translation)
Establish `hu : 0 < ‖(u : ℚ_[ℓ])‖` using `norm_pos_iff.2 u.ne_zero`. Take `⟨c, hc⟩` from `Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu`. Establish `hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖`. Establish `h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c)` using `by ring`. Establish `hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖` using `by rwa [norm_neg]`.

Rewrite using `[h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]`. Establish `hc0 : (c : ℚ_[ℓ]) ≠ 0` using `norm_pos_iff.1 (hn ▸ hu)`. Establish `h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1` using `by rw [norm_div, hn, div_self hu.ne']`. Use `⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]`.
-/
theorem exists_rat_mul_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℚ_[ℓ]ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ r : ℤ_[ℓ]ˣ, (u : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] c * ((r : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hu : 0 < ‖(u : ℚ_[ℓ])‖ := norm_pos_iff.2 u.ne_zero
  obtain ⟨c, hc⟩ := Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu
  have hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖ := by
    have h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c) := by ring
    have hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖ := by rwa [norm_neg]
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  have hc0 : (c : ℚ_[ℓ]) ≠ 0 := norm_pos_iff.1 (hn ▸ hu)
  have h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1 := by rw [norm_div, hn, div_self hu.ne']
  refine ⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩
  rw [PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]

/- English proof (translation)
Introduce `E _ _ _ τ ℓ _ a u z ha hau`. Use `set S := ℚ_[ℓ] ⊗[ℚ] E`. Use `set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ`. Use `set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι`. Establish `hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w` using `fun w => rfl`.

Establish `hτι : ∀ w : E, τℓ (ι w) = ι (τ w)` using `fun w => by show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Establish `hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q)` using `fun q => by`. Rewrite using `[ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]`.

Establish `hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ]))` using `fun t => by`. Rewrite using `[show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]`. Conclude with `isIntegral_algebraMap`. Establish `hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w)` using `fun w hw => hw.map (τℓ.restrictScalars ℤ_[ℓ])`. Take `⟨c, hc0, r, hur⟩` from `exists_rat_mul_unit ℓ u`.

Take `⟨b, s, hs, hb⟩` from `GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z`. Take `⟨ρ, hρ, hρint⟩` from `GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs`. Use `set v : S := 1 + (ℓ : S) * s with hv`. Establish `hvint : IsIntegral ℤ_[ℓ] v`. Use `isIntegral_one.add (IsIntegral.mul ?_ hs)` and prove the remaining obligations.

Rewrite using `[show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]`. Conclude with `isIntegral_algebraMap`. Establish `hbU : IsUnit b` using `isUnit_of_isUnit_one_tmul E ℓ b (by`. Rewrite using `[hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)`. Use `set m : E := algebraMap ℚ E c * (b * τ b) with hm`.

Establish `hmU : IsUnit m` using `((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))`. Take `⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1` from `⟨_, hmU.mul_val_inv⟩`. Take `⟨ai, hai⟩ : ∃ ai : E, a * ai = 1` from `⟨_, ha.mul_val_inv⟩`. Use `set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR`. Use `set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi`.

Use `set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC`. Use `set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU`. Establish `hUCR : U = C * R` using `by rw [hU, hur, map_mul]`. Establish `hRRi : R * Ri = 1`. Rewrite using `[hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, PadicInt.coe_one, map_one]`.

Establish `h1 : ι a = U * ((z : S) * τℓ z)` using `hau`. Establish `h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v))`. Rewrite using `[hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]`. Establish `h4 : v * ρ = 1` using `hρ`. Establish `h5 : τℓ v * τℓ ρ = 1` using `by rw [← map_mul, h4, map_one]`.

Establish `h3 : ι m * ι mi = 1` using `by rw [← map_mul, hmi, map_one]`. Establish `h3' : ι a * ι ai = 1` using `by rw [← map_mul, hai, map_one]`. Establish `hx : ι (a * mi) = R * ρ * τℓ ρ`. Establish `hK : R * ρ * τℓ ρ * ι m = ι a`. Rewrite using `[h2, h1, hUCR]`.

Take the linear combination `(C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5`. Rewrite using `[map_mul]`. Take the linear combination `(-ι mi) * hK + (R * ρ * τℓ ρ) * h3`. Establish `hy : ι (m * ai) = Ri * v * τℓ v`. Establish `hK : Ri * v * τℓ v * ι a = ι m`.

Rewrite using `[h2, h1, hUCR]`. Take the linear combination `(C * (z : S) * v * τℓ z * τℓ v) * hRRi`. Rewrite using `[map_mul]`. Take the linear combination `(-ι ai) * hK + (Ri * v * τℓ v) * h3'`. Take `⟨d1, hd1, hx1⟩` from `GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by`.

Rewrite using `[← hιapp, hx]`. Conclude with `((hint _).mul hρint).mul (hτint _ hρint))`. Take `⟨d2, hd2, hy2⟩` from `GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by`. Rewrite using `[← hιapp, hy]`. Conclude with `((hint _).mul hvint).mul (hτint _ hvint))`.

Use `⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `(-a) * hmi`. Take the linear combination `(-m) * hai`. Introduce `h`. Break down `(Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h` into its components or cases.

Conclude with `hd1 h`. Conclude with `hd2 h`. Establish `: ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi))` using `by push_cast; ring`. Rewrite using `[this]`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1`.

Establish `: ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai))` using `by push_cast; ring`. Rewrite using `[this]`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2`.
-/
theorem main : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  intro E _ _ _ τ ℓ _ a u z ha hau
  set S := ℚ_[ℓ] ⊗[ℚ] E
  set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ
  set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι
  have hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w := fun w => rfl
  have hτι : ∀ w : E, τℓ (ι w) = ι (τ w) := fun w => by
    show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q) := fun q => by
    rw [ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]
  have hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ])) := fun t => by
    rw [show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w) := fun w hw =>
    hw.map (τℓ.restrictScalars ℤ_[ℓ])
  obtain ⟨c, hc0, r, hur⟩ := exists_rat_mul_unit ℓ u
  obtain ⟨b, s, hs, hb⟩ := GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z
  obtain ⟨ρ, hρ, hρint⟩ := GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs
  set v : S := 1 + (ℓ : S) * s with hv
  have hvint : IsIntegral ℤ_[ℓ] v := by
    refine isIntegral_one.add (IsIntegral.mul ?_ hs)
    rw [show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]
    exact isIntegral_algebraMap
  have hbU : IsUnit b := isUnit_of_isUnit_one_tmul E ℓ b (by
    rw [hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)
  set m : E := algebraMap ℚ E c * (b * τ b) with hm
  have hmU : IsUnit m := ((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))
  obtain ⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1 := ⟨_, hmU.mul_val_inv⟩
  obtain ⟨ai, hai⟩ : ∃ ai : E, a * ai = 1 := ⟨_, ha.mul_val_inv⟩

  set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR
  set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi
  set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC
  set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU
  have hUCR : U = C * R := by rw [hU, hur, map_mul]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.coe_one, map_one]
  have h1 : ι a = U * ((z : S) * τℓ z) := hau
  have h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v)) := by
    rw [hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]
  have h4 : v * ρ = 1 := hρ
  have h5 : τℓ v * τℓ ρ = 1 := by rw [← map_mul, h4, map_one]
  have h3 : ι m * ι mi = 1 := by rw [← map_mul, hmi, map_one]
  have h3' : ι a * ι ai = 1 := by rw [← map_mul, hai, map_one]
  have hx : ι (a * mi) = R * ρ * τℓ ρ := by
    have hK : R * ρ * τℓ ρ * ι m = ι a := by
      rw [h2, h1, hUCR]
      linear_combination (C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5
    rw [map_mul]
    linear_combination (-ι mi) * hK + (R * ρ * τℓ ρ) * h3
  have hy : ι (m * ai) = Ri * v * τℓ v := by
    have hK : Ri * v * τℓ v * ι a = ι m := by
      rw [h2, h1, hUCR]
      linear_combination (C * (z : S) * v * τℓ z * τℓ v) * hRRi
    rw [map_mul]
    linear_combination (-ι ai) * hK + (Ri * v * τℓ v) * h3'
  obtain ⟨d1, hd1, hx1⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by
    rw [← hιapp, hx]
    exact ((hint _).mul hρint).mul (hτint _ hρint))
  obtain ⟨d2, hd2, hy2⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by
    rw [← hιapp, hy]
    exact ((hint _).mul hvint).mul (hτint _ hvint))
  refine ⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩
  · linear_combination (-a) * hmi
  · linear_combination (-m) * hai
  · intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h
    · exact hd1 h
    · exact hd2 h
  · have : ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1
  · have : ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2

end GlobalTheory.LocalApprox
