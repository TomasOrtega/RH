import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrPre

noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

/- English proof (translation)
Use `congrArg (fun A : E →L[ℂ] E => A v) h` as an intermediate fact. Conclude with `this`.
-/
theorem comm_apply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {S T : E →L[ℂ] E}
    (h : S * T = T * S) (v : E) : S (T v) = T (S v) := by
  have := congrArg (fun A : E →L[ℂ] E => A v) h
  exact this

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

def formOf (S : Hs B hB →L[ℂ] Hs B hB) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪iota B hB x, S (iota B hB y)⟫_ℂ)
    (fun x₁ x₂ y => by simp [map_add, inner_add_left])
    (fun c x y => by simp [map_smul, inner_smul_left])
    (fun x y₁ y₂ => by simp [map_add, inner_add_right])
    (fun c x y => by simp [map_smul, inner_smul_right])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem formOf_apply (S : Hs B hB →L[ℂ] Hs B hB) (x y : M) :
    formOf B hB S x y = ⟪iota B hB x, S (iota B hB y)⟫_ℂ := rfl

variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

/- English proof (translation)
Use `set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def`. Establish `ha : 0 < a` using `by positivity`. Establish `hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ` using `fun u v => by`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]`. Establish `hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x` using `fun x y => by`.

Rewrite using `[formOf_apply, formOf_apply, inner_conj_symm, hsym]`. Establish `hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y` using `fun g x y => by`. Rewrite using `[formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]`. Establish `hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2` using `fun x => by`. Rewrite using `[formOf_apply]`.

Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2` using `fun x => by`. Rewrite using `[re_B B hB, abs_mul, abs_of_pos ha]`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)`.

Apply the tactic sequence `refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]`. Rewrite using `[Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Use `abs_le.1 (key x)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hext.1.2.2, hinvQ]`. Establish `h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S))`. Apply the tactic sequence `refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`.

Rewrite using `[map_sub, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]`. Rewrite using `[Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Use `abs_le.1 (key x)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hext.1.2.2, hinvQ]`.

Take `⟨c, hc'⟩` from `hext.2 _ h1 h2`. Establish `ha' : (a : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 ha.ne'`. Establish `hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y` using `fun x y => by`. Establish `h` using `hc' x y`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h`.

Rewrite using `[mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']`. Take the linear combination `h`. Use `set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))`. Establish `hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ` using `fun x y => by`. Rewrite using `[inner_iota, ← formOf_apply]`.

Conclude with `hQ x y`. Establish `hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ`. Introduce `u v`. Use `Completion.induction_on₂ u v ?_ fun p q => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd)) (continuous_const.mul (continuous_fst.inner continuous_snd))`.

Conclude with `hQ' p q`. Use `⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]`.
-/
theorem scalar_sa (hext : IsExtremeForm ρ B) (S : Hs B hB →L[ℂ] Hs B hB) (hS : IsSelfAdjoint S)
    (hc : ∀ g, S * pi B hB ρ hinv g = pi B hB ρ hinv g * S) : ∃ c : ℂ, S = c • 1 := by
  set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  have hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x := fun x y => by
    rw [formOf_apply, formOf_apply, inner_conj_symm, hsym]
  have hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y := fun g x y => by
    rw [formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]
  have hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2 := fun x => by
    rw [formOf_apply]
    calc _ ≤ ‖⟪iota B hB x, S (iota B hB x)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖iota B hB x‖ * ‖S (iota B hB x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖iota B hB x‖ * (‖S‖ * ‖iota B hB x‖) := by gcongr; exact S.le_opNorm _
      _ = _ := by ring
  have key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2 := fun x => by
    rw [re_B B hB, abs_mul, abs_of_pos ha]
    calc a * |(formOf B hB S x x).re| ≤ a * ((‖S‖ + 1) * ‖iota B hB x‖ ^ 2) := by
          gcongr; exact (hbd x).trans (by gcongr; linarith)
      _ = _ := by rw [ha_def]; field_simp
  have h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  have h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_sub, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  obtain ⟨c, hc'⟩ := hext.2 _ h1 h2
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y := fun x y => by
    have h := hc' x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']
    linear_combination h
  set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))
  have hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ := fun x y => by
    rw [inner_iota, ← formOf_apply]; exact hQ x y
  have hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ := by
    intro u v
    refine Completion.induction_on₂ u v ?_ fun p q => ?_
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_const.mul (continuous_fst.inner continuous_snd))
    · exact hQ' p q
  refine ⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩
  rw [hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

/- English proof (translation)
Establish `hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T` using `fun g => by`. Establish `h` using `congrArg star (hT g⁻¹)`. Simplify using `only [star_mul, star_pi, inv_inv] at h`. Conclude with `h.symm`. Establish `hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g = pi B hB ρ hinv g * realPart T` using `fun g => by`.

Simplify using `only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']`. Establish `him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g = pi B hB ρ hinv g * imaginaryPart T` using `fun g => by`. Simplify using `only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']`. Take `⟨c₁, h₁⟩` from `scalar_sa B hB ρ hinv hext _ (realPart T).prop hre`. Take `⟨c₂, h₂⟩` from `scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him`.

Use `⟨c₁ + Complex.I * c₂, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]`. Rewrite using `[h₁, h₂, smul_smul, add_smul]`.
-/
theorem commutant (hext : IsExtremeForm ρ B) (T : Hs B hB →L[ℂ] Hs B hB)
    (hT : ∀ g, T * pi B hB ρ hinv g = pi B hB ρ hinv g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T := fun g => by
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, star_pi, inv_inv] at h
    exact h.symm
  have hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * realPart T := fun g => by
    simp only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']
  have him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * imaginaryPart T := fun g => by
    simp only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']
  obtain ⟨c₁, h₁⟩ := scalar_sa B hB ρ hinv hext _ (realPart T).prop hre
  obtain ⟨c₂, h₂⟩ := scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him
  refine ⟨c₁ + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h₁, h₂, smul_smul, add_smul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
