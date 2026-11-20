import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

namespace PI.Witt

section
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
  (B : V →ₗ⋆[K] V →ₗ[K] K)

def qrefl (v : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - (a⁻¹ • (B v)).smulRight v

/- English proof (translation)
Simplify using `[qrefl, LinearMap.smulRight_apply, smul_eq_mul]`.
-/
lemma qrefl_apply (v : V) (a : K) (z : V) : qrefl B v a z = z - (a⁻¹ * B v z) • v := by
  simp [qrefl, LinearMap.smulRight_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[qrefl_apply, qrefl_apply, map_sub, map_smul, smul_eq_mul, hv, sub_sub, ← add_smul]`. Establish `h : b⁻¹ * B v z + a⁻¹ * (B v z - b⁻¹ * B v z * (a + b)) = 0`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, zero_smul, sub_zero]`.
-/
lemma qrefl_qrefl (v : V) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hv : B v v = a + b) (z : V) :
    qrefl B v a (qrefl B v b z) = z := by
  rw [qrefl_apply, qrefl_apply, map_sub, map_smul, smul_eq_mul, hv, sub_sub, ← add_smul]
  have h : b⁻¹ * B v z + a⁻¹ * (B v z - b⁻¹ * B v z * (a + b)) = 0 := by
    field_simp
    ring
  rw [h, zero_smul, sub_zero]

/- English proof (translation)
Establish `ha' : star a ≠ 0` using `star_ne_zero.2 ha`. Establish `key : ∀ p q r : K, p - a⁻¹ * q * r - (star a)⁻¹ * r * q + (star a)⁻¹ * r * (a⁻¹ * q) * (a + star a) = p`. Introduce `p q r`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[qrefl_apply, qrefl_apply]`. Simplify using `only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, starRingEnd_apply, RingHom.id_apply, star_mul', star_inv₀, hB, hv]`. Take the linear combination `key (B z w) (B v w) (B z v)`.
-/
lemma qrefl_isometry (hB : ∀ x y, star (B x y) = B y x) (v : V) (a : K) (ha : a ≠ 0)
    (hv : B v v = a + star a) (z w : V) :
    B (qrefl B v a z) (qrefl B v a w) = B z w := by
  have ha' : star a ≠ 0 := star_ne_zero.2 ha
  have key : ∀ p q r : K, p - a⁻¹ * q * r - (star a)⁻¹ * r * q +
      (star a)⁻¹ * r * (a⁻¹ * q) * (a + star a) = p := by
    intro p q r
    field_simp
    ring
  rw [qrefl_apply, qrefl_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_smul, starRingEnd_apply, RingHom.id_apply, star_mul', star_inv₀, hB, hv]
  linear_combination key (B z w) (B v w) (B z v)

def qreflEquiv (v : V) (a : K) (ha : a ≠ 0) (hv : B v v = a + star a) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (qrefl B v a) (qrefl B v (star a))
    (LinearMap.ext fun z => qrefl_qrefl B v a (star a) ha (by simpa using ha) hv z)
    (LinearMap.ext fun z => qrefl_qrefl B v (star a) a (by simpa using ha) ha
      (by rw [hv, add_comm]) z)

/- English proof (translation)
Establish `hv : B (x - y) (x - y) = B (x - y) x + star (B (x - y) x)`. Rewrite using `[hB]`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Rewrite using `[← hxy]`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `refine ⟨qreflEquiv B (x - y) (B (x - y) x) ha hv, fun z w => qrefl_isometry B hB (x - y) _ ha hv z w, ?_, fun z hz1 hz2 => ?_⟩`. Use `show qrefl B (x - y) (B (x - y) x) x = y`. Rewrite using `[qrefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]`. Use `show qrefl B (x - y) (B (x - y) x) z = z`. Rewrite using `[qrefl_apply]`.

Simplify using `only [map_sub, LinearMap.sub_apply, hz1, hz2, sub_zero, mul_zero, zero_smul]`.
-/
lemma oneVector_generic (hB : ∀ x y, star (B x y) = B y x) (x y : V) (hxy : B x x = B y y)
    (ha : B (x - y) x ≠ 0) :
    ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
      ∀ z, B x z = 0 → B y z = 0 → g z = z := by
  have hv : B (x - y) (x - y) = B (x - y) x + star (B (x - y) x) := by
    rw [hB]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  refine ⟨qreflEquiv B (x - y) (B (x - y) x) ha hv,
    fun z w => qrefl_isometry B hB (x - y) _ ha hv z w, ?_, fun z hz1 hz2 => ?_⟩
  · show qrefl B (x - y) (B (x - y) x) x = y
    rw [qrefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]
  · show qrefl B (x - y) (B (x - y) x) z = z
    rw [qrefl_apply]
    simp only [map_sub, LinearMap.sub_apply, hz1, hz2, sub_zero, mul_zero, zero_smul]

end

/- English proof (translation)
Introduce `K V _ _ _ _ _ B hB x y hxy hx0`. Distinguish the cases in `ha : B (x - y) x ≠ 0`. Conclude with `oneVector_generic B hB x y hxy ha`. Use `push_neg at ha`. Establish `hyx : B y x = B x x`.

Establish `h : B (x - y) x = B x x - B y x` using `by simp only [map_sub, LinearMap.sub_apply]`. Rewrite `ha` using `[h]`. Conclude with `(sub_eq_zero.1 ha).symm`. Establish `hxy' : B x x = B (-y) (-y)` using `by simp [hxy]`. Establish `ha2 : B (x - -y) x ≠ 0`.

Rewrite using `[sub_neg_eq_add, map_add, LinearMap.add_apply, hyx]`. Introduce `h`. Apply `hx0` to reduce the goal to its premises. Establish `h2 : (2 : K) * B x x = 0` using `by rw [two_mul]; exact h`. Conclude with `(mul_eq_zero.1 h2).resolve_left two_ne_zero`.

Take `⟨g1, hg1, hg1x, hg1z⟩` from `oneVector_generic B hB x (-y) hxy' ha2`. Establish `hyy : B y y ≠ 0` using `hxy ▸ hx0`. Establish `ha0 : B y y / 2 ≠ 0` using `div_ne_zero hyy two_ne_zero`. Establish `hstar : star (B y y / 2) = B y y / 2` using `by rw [star_div₀, hB, star_ofNat]`. Establish `hv : B y y = B y y / 2 + star (B y y / 2)` using `by rw [hstar]; ring`.

Establish `h2 : (B y y / 2)⁻¹ * B y y = 2` using `by field_simp`. Use `⟨g1.trans (qreflEquiv B y (B y y / 2) ha0 hv), fun z w => ?_, ?_, fun z hz1 hz2 => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply]`. Establish `hq : ∀ u, qreflEquiv B y (B y y / 2) ha0 hv u = qrefl B y (B y y / 2) u` using `fun _ => rfl`. Apply the tactic sequence `rw [hq, hq, qrefl_isometry B hB y _ ha0 hv, hg1]`.

Simplify using `only [LinearEquiv.trans_apply, hg1x] show qrefl B y (B y y / 2) (-y) = y`. Rewrite using `[qrefl_apply, map_neg, mul_neg, neg_smul, sub_neg_eq_add, h2, two_smul]`. Normalize the expressions using the abelian group laws. Simplify using `only [LinearEquiv.trans_apply]`. Rewrite using `[hg1z z hz1 (by rw [map_neg, LinearMap.neg_apply, hz2, neg_zero])]`.

Use `show qrefl B y (B y y / 2) z = z`. Rewrite using `[qrefl_apply, hz2, mul_zero, zero_smul, sub_zero]`.
-/
theorem one_vector_holds : OneVector := by
  intro K V _ _ _ _ _ B hB x y hxy hx0
  by_cases ha : B (x - y) x ≠ 0
  · exact oneVector_generic B hB x y hxy ha
  · push_neg at ha
    have hyx : B y x = B x x := by
      have h : B (x - y) x = B x x - B y x := by simp only [map_sub, LinearMap.sub_apply]
      rw [h] at ha
      exact (sub_eq_zero.1 ha).symm
    have hxy' : B x x = B (-y) (-y) := by simp [hxy]
    have ha2 : B (x - -y) x ≠ 0 := by
      rw [sub_neg_eq_add, map_add, LinearMap.add_apply, hyx]
      intro h
      apply hx0
      have h2 : (2 : K) * B x x = 0 := by rw [two_mul]; exact h
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    obtain ⟨g1, hg1, hg1x, hg1z⟩ := oneVector_generic B hB x (-y) hxy' ha2
    have hyy : B y y ≠ 0 := hxy ▸ hx0
    have ha0 : B y y / 2 ≠ 0 := div_ne_zero hyy two_ne_zero
    have hstar : star (B y y / 2) = B y y / 2 := by rw [star_div₀, hB, star_ofNat]
    have hv : B y y = B y y / 2 + star (B y y / 2) := by rw [hstar]; ring
    have h2 : (B y y / 2)⁻¹ * B y y = 2 := by field_simp
    refine ⟨g1.trans (qreflEquiv B y (B y y / 2) ha0 hv), fun z w => ?_, ?_, fun z hz1 hz2 => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      have hq : ∀ u, qreflEquiv B y (B y y / 2) ha0 hv u = qrefl B y (B y y / 2) u := fun _ => rfl
      rw [hq, hq, qrefl_isometry B hB y _ ha0 hv, hg1]
    · simp only [LinearEquiv.trans_apply, hg1x]
      show qrefl B y (B y y / 2) (-y) = y
      rw [qrefl_apply, map_neg, mul_neg, neg_smul, sub_neg_eq_add, h2, two_smul]
      abel
    · simp only [LinearEquiv.trans_apply]
      rw [hg1z z hz1 (by rw [map_neg, LinearMap.neg_apply, hz2, neg_zero])]
      show qrefl B y (B y y / 2) z = z
      rw [qrefl_apply, hz2, mul_zero, zero_smul, sub_zero]

end PI.Witt
