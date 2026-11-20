import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem quasiRefl_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  simp [quasiRefl, smul_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem sesq_smul_right_eq_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h x (c • y) = c * h x y := by
  rw [map_smul, smul_eq_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.
-/
theorem quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, quasiRefl_apply, quasiRefl_apply, LinearMap.id_apply,
    map_sub, sesq_smul_right_eq_mul, sub_sub, ← add_smul]
  have hc : b * h u v + a * (h u v - b * h u v * h u u) = 0 := by
    linear_combination (h u v) * hab
  rw [hc, zero_smul, sub_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem sesq_smul_left_eq_star_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h (c • x) y = star c * h x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
private theorem star_apply_eq_apply_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (x y : V) :
    star (h x y) = h y x := by
  have := LinearMap.isSymm_def.mp hs x y
  rwa [starRingEnd_apply] at this

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem quasiRefl_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  simp only [quasiRefl_apply, map_sub, LinearMap.sub_apply, sesq_smul_left_eq_star_mul,
    sesq_smul_right_eq_mul, star_mul, hsy]
  linear_combination (-(h v u * h u w)) * ha

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isom_fix {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨1, Subgroup.one_mem _, rfl, fun v _ _ => rfl⟩
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  obtain ⟨c, hcdef⟩ : ∃ c, c = h (x - y) x := ⟨_, rfl⟩
  have hsum : c + star c = h (x - y) (x - y) := by
    rw [hcdef, hsy]
    simp only [map_sub, LinearMap.sub_apply, hx, hy]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxy
    have : h (x - y) (x - y) = 0 := by rw [← hsum, h0, star_zero, add_zero]
    exact sub_eq_zero.mp (hd _ this)
  have hs0 : star c ≠ 0 := star_ne_zero.mpr hc0
  have ha : c⁻¹ + star c⁻¹ = c⁻¹ * star c⁻¹ * h (x - y) (x - y) := by
    rw [← hsum, star_inv₀]
    field_simp
    ring
  have h1 : quasiRefl h (x - y) c⁻¹ ∘ₗ quasiRefl h (x - y) (star c⁻¹) =
      LinearMap.id := quasiRefl_comp h (x - y) ha
  have h2 : quasiRefl h (x - y) (star c⁻¹) ∘ₗ quasiRefl h (x - y) c⁻¹ =
      LinearMap.id := quasiRefl_comp h (x - y) (by rw [add_comm, ha]; ring)
  refine ⟨LinearEquiv.ofLinear _ _ h1 h2, ?_, ?_, ?_⟩
  · exact fun v w => quasiRefl_isom hs (x - y) ha v w
  · change quasiRefl h (x - y) c⁻¹ x = y
    rw [quasiRefl_apply, ← hcdef, inv_mul_cancel₀ hc0, one_smul, sub_sub_cancel]
  · intro v hxv hyv
    change quasiRefl h (x - y) c⁻¹ v = v
    rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, hxv, hyv, sub_zero, mul_zero,
      zero_smul, sub_zero]

end ReciprocityTheory.ChartRestriction.L3.WA
